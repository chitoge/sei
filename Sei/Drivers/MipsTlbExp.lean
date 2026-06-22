/-
N4 (MIPS fidelity): TLBWI installs a TLB entry from EntryHi/EntryLo, and a
subsequent useg load translates through it. Program sets EntryHi=0x1000 (VPN),
EntryLo=0x80 (→ PFN 0x2000), TLBWI, then `LW r4, 0(r3=0x1000)` reads the value
placed at physical 0x2000. Exit 0 = pass.
-/
import Sei.Core
import Sei.Isa.Mips
open Sei.Core Sei.Isa.Mips

def prog : List Word :=
  [ ORI 1 0 0x1000,     -- r1 = 0x1000 (EntryHi VPN)
    MTC0 1 10 0,        -- EntryHi = r1
    ORI 2 0 0x80,       -- r2 = 0x80 (EntryLo → PFN 0x2000)
    MTC0 2 2 0,         -- EntryLo = r2
    TLBWI,              -- install 0x1000 → 0x2000
    ORI 3 0 0x1000,     -- r3 = 0x1000 (useg virtual address)
    LW 4 0 3,           -- r4 = mem[translate(0x1000)] = mem[phys 0x2000]
    BEQ 0 0 0x20 0x20 ] -- spin

def progImage : List Byte := Id.run do
  let mut buf : Array Byte := (List.replicate 0x1000 (0 : Byte)).toArray
  for (w, i) in prog.zipIdx do
    let bs := encodeBytes true w.toNat 4
    for k in [0:4] do buf := buf.setIfInBounds (i * 4 + k) (bs.getD k 0)
  return buf.toList

-- physical 0x2000 holds 0xCAFE (the TLB-mapped target page)
def dataImage : List Byte := encodeBytes true 0xCAFE 4 ++ List.replicate (0x1000 - 4) 0

def machine : Machine :=
  { regions := #[
      mkRegion "rom" 0x0 0x1000 Kind.rom (parsePerms "rx") true (bytesToBA progImage),
      mkRegion "ram" 0x2000 0x1000 Kind.ram (parsePerms "rw") true (bytesToBA dataImage) ] }

def result : Machine := (runMips 30 (({} : Cpu), machine)).2

def checks : List (String × Bool) :=
  [ ("tlbw_event", result.effects.any fun e => match e with | .cp15 "tlbw" .. => true | _ => false),
    ("useg_load_via_tlb", result.effects.any fun e => match e with
       | .reg 4 v => v == (0xCAFE : Word) | _ => false) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "MIPS TLBWI checks failed")
  IO.println "MIPS TLBWI fidelity (N4): PASS"
