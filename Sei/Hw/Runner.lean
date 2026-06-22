/-
L2 (large-use-case plan): a bounded firmware runner. Runs a descriptor-backed
machine (from an intake manifest, not a hand-built fixture) under a fuel bound,
dispatching on the CPU family, and classifies the stop into a typed reason with a
deterministic, machine-readable run report.
-/
import Sei.Core
import Sei.Hw.Intake
import Sei.Isa.Arm
import Sei.Isa.Mips
open Lean Sei.Core Sei.Hw Sei.Hw.Adapter
namespace Sei.Hw

inductive StopReason
  | halted | blockedFrontier | unsupportedInstr | unknownMmio
  | controllerWait | timerWait | fuelExhausted | exceptionLoop
  deriving DecidableEq, Repr

structure RunReport where
  arch : String
  endian : String
  entry : Nat
  regions : Nat
  devices : Nat
  fuel : Nat
  stop : StopReason
  lastPc : Nat
  events : Nat
  traceHash : Nat
  descriptorId : String
  /-- L5 coverage: undecoded instructions reached, as (PC, opcode/word, mnemonic). -/
  unsupported : List (Nat × Nat × String)
  /-- #4: applied entry state (sp, high-vectors, override count). -/
  entrySp : Nat
  highVectors : Bool
  regOverrides : Nat
  deriving Repr, DecidableEq

/-- Entry state applied at reset (descriptor `entry.*`). -/
structure EntryState where
  resetPc : Nat
  sp : Nat := 0
  highVectors : Bool := false
  exceptionState : String := "none"
  regOverrides : List (Nat × Word) := []

/-- A stable, deterministic content hash of the event trace (every rendered
    character, not just length — so distinct traces of equal length differ). -/
def traceHash (m : Machine) : Nat :=
  m.trace.foldl (fun h ev =>
    ev.effect.render.toList.foldl (fun h c => (h * 1000003 + c.toNat + 1) % 2147483647) h) 7

def hasUnknownMmio (m : Machine) : Bool := m.hasUnknown
def unsupportedEvents (m : Machine) : List (Nat × Nat × String) :=
  m.trace.toList.filterMap fun ev => match ev.effect with
    | .unsupported pc op mn => some (pc.toNat, op, mn) | _ => none

/-- Run an already-built machine for `arch` from the entry state to a typed
    frontier; returns the report and the final machine (for trace/frontier export). -/
def runMachine (m : Machine) (arch endian : String) (e : EntryState) (descId : String) (fuel : Nat)
    : RunReport × Machine :=
  let mk (stop : StopReason) (lastPc : Nat) (m' : Machine) : RunReport × Machine :=
    let unsup := unsupportedEvents m'
    ({ arch, endian, entry := e.resetPc, regions := m.regions.size, devices := m.devices.size,
       fuel, stop := if !unsup.isEmpty then .unsupportedInstr else stop,
       lastPc, events := m'.trace.size, traceHash := traceHash m',
       descriptorId := descId, unsupported := unsup,
       entrySp := e.sp, highVectors := e.highVectors, regOverrides := e.regOverrides.length }, m')
  let applyOverrides {C} (setRegs : C → Nat → Word → C) (c0 : C) : C :=
    e.regOverrides.foldl (fun c (i, v) => setRegs c i v) c0
  match arch with
  | "mips32" =>
    let base : Sei.Isa.Mips.Cpu := { pc := BitVec.ofNat 32 e.resetPc, npc := BitVec.ofNat 32 (e.resetPc + 4) }
    let base := { base with regs := base.regs.setIfInBounds 29 (BitVec.ofNat 32 e.sp) }   -- $sp = r29
    let cpu := applyOverrides (fun c i v => { c with regs := c.regs.setIfInBounds i v }) base
    let (c, m') := Sei.Isa.Mips.runMips fuel (cpu, m)
    mk (if c.halted then .halted else if hasUnknownMmio m' then .unknownMmio else .fuelExhausted) c.pc.toNat m'
  | _ =>   -- arm or thumb (thumb starts with the T-bit set; or exception_state="thumb")
    let base : Sei.Isa.Arm.Cpu :=
      { pc := BitVec.ofNat 32 e.resetPc, tbit := arch == "thumb" || e.exceptionState == "thumb",
        highVectors := e.highVectors }
    let base := { base with regs := base.regs.setIfInBounds 13 (BitVec.ofNat 32 e.sp) }   -- sp = r13
    let cpu := applyOverrides (fun c i v => { c with regs := c.regs.setIfInBounds i v }) base
    let (c, m') := Sei.Isa.Arm.runArm fuel (cpu, m)
    mk (if c.blocked then .blockedFrontier else if c.halted then .halted
        else if hasUnknownMmio m' then .unknownMmio else .fuelExhausted) c.pc.toNat m'

/-- Run a descriptor-backed firmware image to a typed frontier (from an intake manifest). -/
def runManifest (manText : String) (images : List (String × ByteArray)) (fuel : Nat)
    : Except String RunReport := do
  let manJ ← Json.parse manText
  let arch ← (manJ.getObjVal? "arch").bind (·.getStr?)
  let endian := getStr manJ "endian" "little"
  let resetPc ← parseHexNat (getStr (← manJ.getObjVal? "entry") "reset_pc" "0x0")
  let descId := getStr ((manJ.getObjVal? "source").toOption.getD (Json.mkObj [])) "path" "manifest"
  pure (runMachine (← intakeMachine manText images) arch endian { resetPc } descId fuel).1

end Sei.Hw
