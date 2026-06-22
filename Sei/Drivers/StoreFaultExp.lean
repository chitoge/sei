/-
Audit (new): write faults must not be swallowed. A store that the bus rejects
(strict unknown-MMIO write, device cross-window, or a permission/cross fault)
must NOT let the interpreter silently continue. Checks Toy, IR, and MIPS stores
(ARM already faults). Exit 0 = pass.
-/
import Sei.Core
import Sei.Isa.Toy
import Sei.IR
import Sei.Isa.Mips
import Sei.Hw.Pcode
open Sei.Core

def hasAbort (m : Machine) : Bool :=
  m.effects.any fun e => match e with | .note "data_abort" => true | _ => false

-- Toy STR to an unmapped address under strict-fault write policy → halt + abort.
def toyFault : Bool :=
  let prog := [Sei.Isa.Toy.MOVI 2 0x42, Sei.Isa.Toy.MOVI 3 0x9000,
               Sei.Isa.Toy.STR 2 3 0, Sei.Isa.Toy.HALT]
  let rom := mkRegion "rom" 0 0x1000 Kind.rom (parsePerms "rx") true (bytesToBA (Sei.Isa.Toy.assemble prog true))
  let m : Machine := { regions := #[rom], unknownWrite := .fault }
  let (c, m') := Sei.Isa.Toy.runToy 50 (({} : Sei.Isa.Toy.Cpu), m)
  c.halted && hasAbort m'

-- IR store (via the P-code importer) to an unmapped address → block halts + abort.
def irFault : Bool :=
  let ops := [Sei.Pcode.Op.copy (.reg 2) (.const 0x42),
              Sei.Pcode.Op.copy (.reg 3) (.const 0x9000),
              Sei.Pcode.Op.store (.reg 3) (.reg 2) 4]
  match Sei.Pcode.runPcode ops ({ unknownWrite := .fault } : Machine) with
  | .ok m' => hasAbort m'
  | .error _ => false

-- MIPS SW to ROM (no write permission) → store exception (EXC_TLBS), not silent.
def mipsImage : List Byte := Id.run do
  let prog := [Sei.Isa.Mips.ORI 2 0 0x42, Sei.Isa.Mips.LUI 3 0x8000, Sei.Isa.Mips.SW 2 0 3]
  let mut buf : Array Byte := (List.replicate 0x1000 (0 : Byte)).toArray
  for (w, i) in prog.zipIdx do
    let bs := encodeBytes true w.toNat 4
    for k in [0:4] do buf := buf.setIfInBounds (i * 4 + k) (bs.getD k 0)
  return buf.toList

def mipsFault : Bool :=
  let rom := mkRegion "rom" 0 0x1000 Kind.rom (parsePerms "rx") true (bytesToBA mipsImage)
  let (_, m') := Sei.Isa.Mips.runMips 6 (({} : Sei.Isa.Mips.Cpu), { regions := #[rom] })
  m'.effects.any fun e => match e with
    | .exception "mips" _ code => code == Sei.Isa.Mips.EXC_TLBS | _ => false

def checks : List (String × Bool) :=
  [ ("toy_store_fault_halts", toyFault),
    ("ir_store_fault_halts", irFault),
    ("mips_store_fault_excepts", mipsFault) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "store-fault propagation checks failed")
  IO.println "store-fault propagation: PASS"
