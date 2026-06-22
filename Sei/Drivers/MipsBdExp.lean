/-
N4 (MIPS fidelity): an exception taken in a branch delay slot sets `Cause.BD`
and backs EPC up to the branch instruction (so ERET re-runs the branch). Program:
BEQ r0,r0 (always taken) at 0x80000000 with a SYSCALL in its delay slot at
0x80000004. After the SYSCALL traps, EPC = 0x80000000 (the branch) and Cause.BD
is set. Exit 0 = pass.
-/
import Sei.Core
import Sei.Isa.Mips
open Sei.Core Sei.Isa.Mips

def image : List Byte :=
  let w (off : Nat) (word : Word) (buf : Array Byte) : Array Byte := Id.run do
    let bs := encodeBytes true word.toNat 4
    let mut b := buf
    for k in [0:4] do b := b.setIfInBounds (off + k) (bs.getD k 0)
    return b
  let buf := (List.replicate 0x100 (0 : Byte)).toArray
  let buf := w 0x0 (0x10000004 : Word) buf   -- BEQ r0, r0, +4 (always taken)
  let buf := w 0x4 (0x0000000C : Word) buf    -- SYSCALL (delay slot)
  buf.toList

def machine : Machine :=
  { regions := #[mkRegion "rom" 0 0x100 Kind.rom (parsePerms "rx") true (bytesToBA image)] }

def CAUSE_BD : Word := BitVec.ofNat 32 (1 <<< 31)

def result : Cpu := (runMips 2 (({} : Cpu), machine)).1

def checks : List (String × Bool) :=
  [ ("epc_points_to_branch", result.c0 EPC == (0x80000000 : Word)),
    ("cause_bd_set", (result.c0 CAUSE &&& CAUSE_BD) == CAUSE_BD) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "MIPS branch-delay exception checks failed")
  IO.println "MIPS branch-delay fidelity (N4): PASS"
