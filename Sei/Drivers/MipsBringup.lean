/-
MIPS descriptor-driven CPU bring-up: a `.sei.json` (physical regions, reset_pc in
kseg0) + a firmware image instantiate a `Machine`, and the MIPS interpreter runs
from reset_pc, reproducing the E05 timer-interrupt signals (Count==Compare →
IP7, ISR marker write, ERET) through the descriptor path. Exit 0 = pass.
-/
import Sei.Core
import Sei.Hw.Descriptor
import Sei.Isa.Mips
open Lean Sei.Core Sei.Hw Sei.Isa.Mips

def q (s : String) : String := s.replace "'" "\""

/-- Sparse word placement into a zero-filled image. -/
def placeImage (size : Nat) (ps : List (Nat × Word)) : List Byte := Id.run do
  let mut buf : Array Byte := (List.replicate size (0 : Byte)).toArray
  for (off, w) in ps do
    let bs := encodeBytes true w.toNat 4
    for k in [0:4] do
      buf := buf.setIfInBounds (off + k) (bs.getD k 0)
  return buf.toList

/-- E05 timer program: set Compare/Status, loop; the timer ISR (@0x180) writes a
    marker to 0x80001000 and acks Compare, then ERETs. -/
def timerProg : List (Nat × Word) :=
  [ (0x00, ORI 9 0 15), (0x04, MTC0 9 11 0),
    (0x08, ORI 10 0 0x8001), (0x0C, MTC0 10 12 0),
    (0x10, LUI 13 0x8000), (0x14, ORI 13 13 0x1000),
    (0x18, ORI 4 0 0), (0x1C, ORI 5 0 40),
    (0x20, ADDIU 4 4 1), (0x24, BNE 4 5 0x24 0x20), (0x28, NOP),
    (0x2C, BEQ 0 0 0x2C 0x2C), (0x30, NOP),
    (0x180, ORI 12 0 0xABC), (0x184, SW 12 0 13), (0x188, MTC0 0 11 0), (0x18C, ERET) ]

def fwBytes : List Byte := placeImage 0x1000 timerProg

/-- MIPS machine descriptor: physical ROM/RAM, reset in kseg0 at 0x80000000. -/
def mipsDesc : String := q
  "{'cpu':{'arch':'mips32','endian':'little'},'entry':{'reset_pc':'0x80000000'},'memory':[{'name':'rom','base':'0x0','size':'0x1000','kind':'rom','perms':'rx','image':'fw'},{'name':'ram','base':'0x1000','size':'0x3000','kind':'ram','perms':'rw'}],'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}}}"

def bringup : Except String (List (String × Bool)) := do
  let h ← parseDescriptor (← Json.parse mipsDesc)
  let m ← loadMachine h [("fw", bytesToBA fwBytes)]
  let cpu : Cpu :=
    { ({} : Cpu) with pc := BitVec.ofNat 32 h.resetPc, npc := BitVec.ofNat 32 (h.resetPc + 4) }
  let (_, m) := runMips 200 (cpu, m)
  let hasTimer := m.effects.any (fun e => match e with | .timer .. => true | _ => false)
  let hasIrq := m.effects.any (fun e => match e with | .irqLine "timer" true => true | _ => false)
  let hasEret := m.effects.any (fun e => match e with | .exception "eret" .. => true | _ => false)
  let marker := m.effects.any (fun e => match e with
    | .memWrite a _ v => a == (0x1000 : Word) && v == (0xABC : Word) | _ => false)
  pure [ ("arch_mips32", h.arch == "mips32"),
         ("timer_match", hasTimer),
         ("timer_irq", hasIrq),
         ("isr_marker", marker),
         ("eret_returned", hasEret) ]

def main : IO Unit := do
  match bringup with
  | .error e => throw (IO.userError s!"mips bringup failed: {e}")
  | .ok checks =>
    let mut ok := true
    for (n, b) in checks do
      let tag := if b then "ok" else "FAIL"
      IO.println s!"{n}: {tag}"
      if !b then ok := false
    if !ok then throw (IO.userError "mips descriptor bring-up failed")
    IO.println "mips descriptor bring-up: PASS"
