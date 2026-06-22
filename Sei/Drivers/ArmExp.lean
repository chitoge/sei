/-
Classic ARM experiments in Lean (no Python): E02 reset slice (LE + BE) and E03
exception/high-vector slice (IRQ, FIQ on high vectors, undefined, data abort).
Exit 0 = pass.
-/
import Sei.Core
import Sei.Isa.Arm
open Sei.Core
open Sei.Isa.Arm

/-- Place 32-bit words at byte addresses into a zero-filled image of `size`.
    Addresses are absolute; `base` is the region base they are relative to. -/
def placeImage (base size : Nat) (little : Bool) (ps : List (Nat × Word)) : List Byte := Id.run do
  let mut buf : Array Byte := (List.replicate size (0 : Byte)).toArray
  for (addr, w) in ps do
    let bs := encodeBytes little w.toNat 4
    for k in [0:4] do
      buf := buf.setIfInBounds (addr - base + k) (bs.getD k 0)
  return buf.toList

/-! ### Trace predicates (over the typed effect log) -/

def anyCp15Write (m : Machine) : Bool :=
  m.effects.any (fun e => match e with | .cp15 "write" .. => true | _ => false)
def cp15ReadMidr (m : Machine) : Bool :=
  m.effects.any (fun e => match e with | .cp15 "read" _ _ _ _ _ v => v == (0x41069265 : Word) | _ => false)
def unknownReadAt (m : Machine) (a : Word) : Bool :=
  m.effects.any (fun e => match e with | .unknownRead a' _ _ => a' == a | _ => false)
def memWriteAt (m : Machine) (a : Word) : Bool :=
  m.effects.any (fun e => match e with | .memWrite a' _ _ => a' == a | _ => false)
def excVector (m : Machine) (kind : String) : Option Word :=
  (m.effects.findSome? (fun e => match e with | .exception k vec _ => if k == kind then some vec else none | _ => none))
def hasReturn (m : Machine) : Bool :=
  m.effects.any (fun e => match e with | .exception "return" .. => true | _ => false)
def hasNote (m : Machine) (s : String) : Bool :=
  m.effects.any (fun e => match e with | .note s' => s' == s | _ => false)

def vecIs (m : Machine) (kind : String) (v : Word) : Bool :=
  match excVector m kind with | some x => x == v | none => false

/-! ### E02 reset slice -/

def resetProg : List Word :=
  [MOVW 0 0, MOVT 0 0, MCR 0 1 0, MRC 1 0 0, MOV 13 0x00100000,
   MOVW 2 0, MOVT 2 0x4000, LDR 3 2 0, SUB 13 13 4, STR 3 13 0, B 0x28 0x28]

def e02 (little : Bool) : List (String × Bool) :=
  let rom := mkRegion "rom" 0 0x1000 Kind.rom (parsePerms "rx") little (bytesToBA (assemble resetProg little))
  let ram := mkRegion "ram" 0x00080000 0x80000 Kind.ram (parsePerms "rw") little
  let m : Machine := { regions := #[rom, ram], unknownDefault := 0 }
  let (c, m) := runArm 200 (({} : Cpu), m)
  let tag := if little then "le" else "be"
  [ (s!"e02_{tag}_blocked", c.blocked),
    (s!"e02_{tag}_stack", c.regs.getD 13 0 == (0x00100000 - 4 : Word)),
    (s!"e02_{tag}_cp15_write", anyCp15Write m),
    (s!"e02_{tag}_cp15_midr", cp15ReadMidr m && c.regs.getD 1 0 == (0x41069265 : Word)),
    (s!"e02_{tag}_mmio_frontier", unknownReadAt m 0x40000000),
    (s!"e02_{tag}_stack_store", memWriteAt m 0x000FFFFC) ]

/-! ### E03 exceptions -/

def baseCpu (high : Bool) (pc : Word) : Cpu :=
  { ({} : Cpu) with haltOnSelfBranch := false, highVectors := high, pc := pc }

def armMachine (romBase : Nat) (little : Bool) (ps : List (Nat × Word)) (extraRO : Bool := false) : Machine :=
  let rom := mkRegion "rom" romBase 0x10000 Kind.rom (parsePerms "rx") little (bytesToBA (placeImage romBase 0x10000 little ps))
  let ram := mkRegion "ram" 0x00200000 0x10000 Kind.ram (parsePerms "rw") little
  let regs := if extraRO then #[rom, ram, mkRegion "rodata" 0x00300000 0x1000 Kind.rom (parsePerms "r") little]
              else #[rom, ram]
  { regions := regs, unknownDefault := 0 }

def e03_irq : List (String × Bool) :=
  let ps : List (Nat × Word) :=
    [(0x00, B 0x100 0x00), (0x18, B 0x300 0x18),
     (0x100, MOV 0 1), (0x104, MOV 1 2), (0x108, B 0x108 0x108),
     (0x300, MOV 4 0xAB), (0x304, SUBS_pc_lr 4)]
  let m := armMachine 0 true ps
  let (c1, m1) := runArm 4 (baseCpu false 0, m)               -- reach the spin
  let (cM, mM) := runArm 1 ({ c1 with irqPending := true, iMask := true }, m1)  -- masked
  let masked := cM.mode == MODE_SVC
  let (c2, m2) := runArm 8 ({ cM with iMask := false }, mM)    -- unmasked → taken
  [ ("e03_irq_masking", masked),
    ("e03_irq_vector_0x18", vecIs m2 "irq" 0x18),
    ("e03_irq_handler_ran", c2.regs.getD 4 0 == (0xAB : Word)),
    ("e03_irq_returned_svc", c2.mode == MODE_SVC),
    ("e03_irq_return_event", hasReturn m2) ]

def e03_fiq_high : List (String × Bool) :=
  let b := 0xFFFF0000
  let ps : List (Nat × Word) :=
    [(b + 0x00, B (b+0x100) (b+0x00)), (b + 0x1C, B (b+0x400) (b+0x1C)),
     (b + 0x100, MOV 0 1), (b + 0x104, B (b+0x104) (b+0x104)),
     (b + 0x400, MOV 5 0xCD), (b + 0x404, SUBS_pc_lr 4)]
  let m := armMachine b true ps
  let (c1, m1) := runArm 3 (baseCpu true (BitVec.ofNat 32 b), m)
  let (cM, mM) := runArm 1 ({ c1 with fiqPending := true, fMask := true }, m1)
  let masked := cM.mode != MODE_FIQ
  let (c2, m2) := runArm 6 ({ cM with fMask := false }, mM)
  [ ("e03_fiq_masking", masked),
    ("e03_fiq_high_vector", vecIs m2 "fiq" 0xFFFF001C),
    ("e03_fiq_handler_ran", c2.regs.getD 5 0 == (0xCD : Word)) ]

def e03_undef : List (String × Bool) :=
  let ps : List (Nat × Word) :=
    [(0x00, B 0x100 0x00), (0x04, B 0x200 0x04),
     (0x100, WORDV 0xEC000000), (0x104, MOV 6 0x55), (0x108, B 0x108 0x108),
     (0x200, MOV 7 0x99), (0x204, MOVS_pc_lr)]
  let m := armMachine 0 true ps
  let (c, m) := runArm 10 (baseCpu false 0, m)
  [ ("e03_undef_trap", m.effects.any (fun e => match e with
        | .unsupported _ op _ => op == 0xEC000000 | _ => false)),   -- typed coverage event
    ("e03_undef_vector_0x04", vecIs m "undef" 0x04),
    ("e03_undef_handler_ran", c.regs.getD 7 0 == (0x99 : Word)),
    ("e03_undef_resumed", c.regs.getD 6 0 == (0x55 : Word)) ]

def e03_dabt : List (String × Bool) :=
  let ps : List (Nat × Word) :=
    [(0x00, B 0x100 0x00), (0x10, B 0x280 0x10),
     (0x100, MOVW 0 0), (0x104, MOVT 0 0x0030), (0x108, MOV 1 0x42),
     (0x10C, STR 1 0 0), (0x110, B 0x110 0x110),
     (0x280, MOV 8 0x77), (0x284, SUBS_pc_lr 4)]
  let m := armMachine 0 true ps true
  let (c, m) := runArm 12 (baseCpu false 0, m)
  [ ("e03_dabt_trap", hasNote m "data_abort"),
    ("e03_dabt_vector_0x10", vecIs m "dabt" 0x10),
    ("e03_dabt_handler_ran", c.regs.getD 8 0 == (0x77 : Word)) ]

-- Encoding goldens: exact A32 constants (independently known / verified in the
-- Python phase), so the assembler isn't merely self-consistent with the decoder.
def encGolden : List (String × Bool) :=
  [ ("enc_MCR_sctlr", MCR 0 1 0 == (0xEE010F10 : Word)),    -- MCR p15,0,r0,c1,c0,0
    ("enc_MRC_midr", MRC 1 0 0 == (0xEE101F10 : Word)),     -- MRC p15,0,r1,c0,c0,0
    ("enc_MOVW_r0_0", MOVW 0 0 == (0xE3000000 : Word)) ]

def checks : List (String × Bool) :=
  encGolden ++ e02 true ++ e02 false ++ e03_irq ++ e03_fiq_high ++ e03_undef ++ e03_dabt

def main : IO Unit := do
  let mut allOk := true
  for (name, ok) in checks do
    let st := if ok then "ok" else "FAIL"
    IO.println s!"{name}: {st}"
    if !ok then allOk := false
  if !allOk then throw (IO.userError "arm experiments failed")
  IO.println "arm experiments: PASS"
