/-
MIPS32 experiments in Lean (no Python): E05 — timer interrupt, syscall, and TLB
(miss vs hit). Exit 0 = pass.
-/
import Sei.Core
import Sei.Isa.Mips
open Sei.Core
open Sei.Isa.Mips

def little : Bool := true

def placeImage (base size : Nat) (ps : List (Nat × Word)) : List Byte := Id.run do
  let mut buf : Array Byte := (List.replicate size (0 : Byte)).toArray
  for (addr, w) in ps do
    let bs := encodeBytes little w.toNat 4
    for k in [0:4] do
      buf := buf.setIfInBounds (addr - base + k) (bs.getD k 0)
  return buf.toList

/-- rom (phys 0, kseg0 0x80000000) + ram (phys 0x1000). -/
def mkMachine (ps : List (Nat × Word)) : Machine :=
  { regions := #[
      mkRegion "rom" 0 0x1000 Kind.rom (parsePerms "rx") little (bytesToBA (placeImage 0 0x1000 ps)),
      mkRegion "ram" 0x1000 0x3000 Kind.ram (parsePerms "rw") little ],
    unknownDefault := 0 }

def hasTimer (m : Machine) : Bool := m.effects.any (fun e => match e with | .timer .. => true | _ => false)
def hasIrq (m : Machine) : Bool := m.effects.any (fun e => match e with | .irqLine "timer" true => true | _ => false)
def hasExc (m : Machine) (code : Nat) : Bool :=
  m.effects.any (fun e => match e with | .exception "mips" _ c => c == code | _ => false)
def hasEret (m : Machine) : Bool := m.effects.any (fun e => match e with | .exception "eret" .. => true | _ => false)
def wroteVal (m : Machine) (a v : Word) : Bool :=
  m.effects.any (fun e => match e with | .memWrite a' _ v' => a' == a && v' == v | _ => false)

/-! ### Timer interrupt -/

def timerProg : List (Nat × Word) :=
  [ (0x00, ORI 9 0 15), (0x04, MTC0 9 11 0),         -- Compare = 15
    (0x08, ORI 10 0 0x8001), (0x0C, MTC0 10 12 0),   -- Status = IE | IM7
    (0x10, LUI 13 0x8000), (0x14, ORI 13 13 0x1000), -- r13 = 0x80001000
    (0x18, ORI 4 0 0), (0x1C, ORI 5 0 40),
    (0x20, ADDIU 4 4 1), (0x24, BNE 4 5 0x24 0x20), (0x28, NOP),
    (0x2C, BEQ 0 0 0x2C 0x2C), (0x30, NOP),
    -- ISR @ 0x180
    (0x180, ORI 12 0 0xABC), (0x184, SW 12 0 13),
    (0x188, MTC0 0 11 0), (0x18C, ERET) ]

def e05_timer : List (String × Bool) :=
  let (c, m) := runMips 200 (({} : Cpu), mkMachine timerProg)
  [ ("e05_timer_match", hasTimer m),
    ("e05_timer_irq", hasIrq m),
    ("e05_timer_int_entry", hasExc m EXC_INT),
    ("e05_timer_isr_marker", wroteVal m 0x1000 0xABC),
    ("e05_timer_eret", hasEret m),
    ("e05_timer_epc_kseg0", decide ((c.c0 EPC).toNat ≥ 0x80000000)) ]

/-! ### Syscall -/

def syscallProg : List (Nat × Word) :=
  [ (0x00, LUI 13 0x8000), (0x04, ORI 13 13 0x2000),
    (0x08, SYSCALL), (0x0C, BEQ 0 0 0x0C 0x0C), (0x10, NOP),
    (0x180, ORI 12 0 0x555), (0x184, SW 12 0 13),
    (0x188, MFC0 14 14 0), (0x18C, ADDIU 14 14 4), (0x190, MTC0 14 14 0), (0x194, ERET) ]

def e05_syscall : List (String × Bool) :=
  let (c, m) := runMips 60 (({} : Cpu), mkMachine syscallProg)
  [ ("e05_sys_exception", hasExc m EXC_SYS),
    ("e05_sys_marker", wroteVal m 0x2000 0x555),
    ("e05_sys_epc_advanced", c.c0 EPC == (0x8000000C : Word)),
    ("e05_sys_eret", hasEret m),
    ("e05_sys_returned", c.pc == (0x8000000C : Word) || c.pc == (0x80000010 : Word)) ]

/-! ### TLB -/

def tlbProg : List (Nat × Word) :=
  [ (0x00, LUI 8 0x0040), (0x04, ORI 8 8 0x0000),
    (0x08, LW 2 0 8), (0x0C, BEQ 0 0 0x0C 0x0C), (0x10, NOP) ]

def e05_tlb : List (String × Bool) :=
  let (cMiss, mMiss) := runMips 20 (({} : Cpu), mkMachine tlbProg)
  -- hit: seed phys 0x2000 and install a TLB entry 0x00400000 → phys 0x2000
  let mSeed := (mkMachine tlbProg)
  let (_, mSeed) := mSeed.busWrite 0x2000 0xCAFEF00D 32
  let cpuHit : Cpu := ({} : Cpu).addTlb 0x00400000 0x2000
  let (cHit, _) := runMips 20 (cpuHit, mSeed)
  [ ("e05_tlb_miss_tlbl", hasExc mMiss EXC_TLBL),
    ("e05_tlb_badvaddr", cMiss.c0 BADVADDR == (0x00400000 : Word)),
    ("e05_tlb_hit_value", cHit.r 2 == (0xCAFEF00D : Word)) ]

-- Encoding goldens: well-known MIPS32 constants, so the assembler is checked
-- against an external reference rather than only against the decoder.
def encGolden : List (String × Bool) :=
  [ ("enc_ERET", ERET == (0x42000018 : Word)),
    ("enc_SYSCALL", SYSCALL == (0x0000000C : Word)),
    ("enc_LUI", LUI 1 0x1234 == (0x3C011234 : Word)) ]   -- lui $1, 0x1234

def checks : List (String × Bool) := encGolden ++ e05_timer ++ e05_syscall ++ e05_tlb

def main : IO Unit := do
  let mut allOk := true
  for (name, ok) in checks do
    let st := if ok then "ok" else "FAIL"
    IO.println s!"{name}: {st}"
    if !ok then allOk := false
  if !allOk then throw (IO.userError "mips experiments failed")
  IO.println "mips experiments: PASS"
