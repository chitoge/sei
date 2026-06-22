/-
N4 (ARM fidelity): banked r13/r14. A mode switch saves the outgoing mode's SP/LR
and restores the incoming mode's, so each mode has its own stack pointer — and an
exception entry/return round-trip preserves the interrupted mode's SP. Exit 0 = pass.
-/
import Sei.Core
import Sei.Isa.Arm
open Sei.Core Sei.Isa.Arm

def bankRoundTrip : Bool :=
  let c : Cpu := {}
  let c := c.setR 13 0x1000
  let c := c.switchMode MODE_IRQ
  let irqDefault := c.regs.getD 13 0
  let c := c.setR 13 0x2000
  let c := c.switchMode MODE_SVC
  let svcSp := c.regs.getD 13 0
  let c := c.switchMode MODE_IRQ
  let irqSp := c.regs.getD 13 0
  irqDefault == 0 && svcSp == 0x1000 && irqSp == 0x2000

def excRoundTrip : Bool :=
  let c : Cpu := {}
  let c := c.setR 13 0x1000
  let (c, _) := takeException c ({} : Machine) "irq" 0x100
  let inIrqSp := c.regs.getD 13 0
  let c := c.setR 13 0x9000
  let c := unpackCpsr c (spsrGet c MODE_IRQ)
  c.mode == MODE_SVC && c.regs.getD 13 0 == 0x1000 && inIrqSp == 0

def checks : List (String × Bool) :=
  [ ("bank_round_trip", bankRoundTrip),
    ("exception_preserves_svc_sp", excRoundTrip) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "ARM banking checks failed")
  IO.println "ARM banked registers (N4): PASS"
