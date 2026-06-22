/-
Descriptor-driven CPU bring-up (audit N1, point 4): a `.sei.json` descriptor +
a firmware image instantiate a `Machine`, and the ARM interpreter executes from
the descriptor's `reset_pc` — reproducing the E02 reset-slice success signals
through the descriptor path (instead of a hand-built machine). Exit 0 = pass.
-/
import Sei.Core
import Sei.Hw.Descriptor
import Sei.Isa.Arm
open Lean Sei.Core Sei.Hw Sei.Isa.Arm

def q (s : String) : String := s.replace "'" "\""

/-- An ARM machine descriptor: ROM holds firmware `main.bin`, RAM for the stack,
    reset at 0x0, default unknown-MMIO policy. -/
def armDesc : String := q
  "{'cpu':{'arch':'arm','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'rom','base':'0x0','size':'0x1000','kind':'rom','perms':'rx','image':'main.bin'},{'name':'ram','base':'0x80000','size':'0x80000','kind':'ram','perms':'rw'}],'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}}}"

/-- The E02 reset slice, as a firmware image. -/
def resetProg : List Word :=
  [MOVW 0 0, MOVT 0 0, MCR 0 1 0, MRC 1 0 0, MOV 13 0x00100000,
   MOVW 2 0, MOVT 2 0x4000, LDR 3 2 0, SUB 13 13 4, STR 3 13 0, B 0x28 0x28]

def progBytes : ByteArray := bytesToBA (assemble resetProg true)

def bringup : Except String (List (String × Bool)) := do
  let h ← parseDescriptor (← Json.parse armDesc)
  let m ← loadMachine h [("main.bin", progBytes)]
  -- build the CPU from the descriptor's reset state and run
  let cpu : Cpu := { ({} : Cpu) with pc := BitVec.ofNat 32 h.resetPc, highVectors := h.highVectors }
  let (c, m) := runArm 200 (cpu, m)
  let anyCp15Write := m.effects.any (fun e => match e with | .cp15 "write" .. => true | _ => false)
  let cp15Midr := m.effects.any (fun e => match e with
    | .cp15 "read" _ _ _ _ _ v => v == (0x41069265 : Word) | _ => false)
  let frontier := m.effects.any (fun e => match e with
    | .unknownRead a _ _ => a == (0x40000000 : Word) | _ => false)
  let stackStore := m.effects.any (fun e => match e with
    | .memWrite a _ _ => a == (0x000FFFFC : Word) | _ => false)
  pure [ ("arch_arm", h.arch == "arm"),
         ("blocked_at_frontier", c.blocked),
         ("stack_setup", c.regs.getD 13 0 == (0x00100000 - 4 : Word)),
         ("cp15_write_logged", anyCp15Write),
         ("cp15_midr_read", cp15Midr && c.regs.getD 1 0 == (0x41069265 : Word)),
         ("mmio_frontier", frontier),
         ("stack_store", stackStore) ]

def main : IO Unit := do
  match bringup with
  | .error e => throw (IO.userError s!"bringup failed: {e}")
  | .ok checks =>
    let mut ok := true
    for (n, b) in checks do
      let tag := if b then "ok" else "FAIL"
      IO.println s!"{n}: {tag}"
      if !b then ok := false
    if !ok then throw (IO.userError "descriptor bring-up failed")
    IO.println "descriptor bring-up: PASS"
