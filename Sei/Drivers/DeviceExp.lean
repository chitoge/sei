/-
Device DSL experiment in Lean (no Python): E07 — a UART register model with a
behavior overlay (TX/RX FIFOs, RXNE status, read-only & write-1-to-clear fields,
reserved bits, IRQ on RXNE&RXIE), driven over the bus. Exit 0 = pass.
-/
import Sei.Core
open Sei.Core

def UART_BASE : Nat := 0x9000

def mkUart : Device :=
  { name := "uart0", base := UART_BASE, size := 0x100, beh := .uart [] [] 1 0,
    sem := { id := "uart0", cls := .spec, proofUse := .local, source := "hand-authored UART (E07)" } }

def baseMachine : Machine :=
  { regions := #[mkRegion "ram" 0 0x1000 Kind.ram (parsePerms "rw") true],
    devices := #[mkUart] }

def dev (m : Machine) : Device := m.devices.getD 0 default
def uartSr (d : Device) : Word := match d.beh with | .uart _ _ sr _ => sr | _ => 0
def uartTx (d : Device) : List Nat := match d.beh with | .uart tx _ _ _ => tx | _ => []

def rd (m : Machine) (a : Nat) : Word × Machine :=
  let (r, m) := m.busRead (BitVec.ofNat 32 a) 32
  (match r with | .ok x => x | _ => 0, m)
def wr (m : Machine) (a : Nat) (v : Word) : Machine := (m.busWrite (BitVec.ofNat 32 a) v 32).2
def pushRx (m : Machine) (b : Nat) : Machine :=
  { m with devices := m.devices.setIfInBounds 0 ((dev m).uartRxPush b) }

def checks : List (String × Bool) := Id.run do
  let mut m := baseMachine
  let mut cs : List (String × Bool) := []

  -- 1. reset values
  let (sr0, m1) := rd m (UART_BASE + 0x4); m := m1
  cs := cs ++ [("reset_TXE_set", sr0 &&& UART_TXE != 0),
               ("reset_RXNE_clear", sr0 &&& UART_RXNE == 0)]

  -- 2. read-only SR: writing must not change TXE/RXNE
  m := wr m (UART_BASE + 0x4) 0xFFFFFFFF
  let (sr1, m2) := rd m (UART_BASE + 0x4); m := m2
  cs := cs ++ [("ro_SR_ignored", sr1 &&& 0x3 == sr0 &&& 0x3)]

  -- 3. reserved bits in CR ignored; declared fields settable
  m := wr m (UART_BASE + 0x8) 0xFFFFFFFF
  let (cr, m3) := rd m (UART_BASE + 0x8); m := m3
  cs := cs ++ [("cr_reserved_ignored", cr == 0x3)]

  -- 4. TX side effect (snapshot the pre-TX device as a value first)
  let snap := m
  m := wr m (UART_BASE + 0x0) (BitVec.ofNat 32 (Char.toNat 'H'))
  m := wr m (UART_BASE + 0x0) (BitVec.ofNat 32 (Char.toNat 'I'))
  cs := cs ++ [("tx_side_effect", uartTx (dev m) == [72, 73]),
               ("snapshot_untouched", uartTx (dev snap) == [])]

  -- 5. RX + IRQ assert (CR.RXIE set in step 3)
  m := pushRx m (Char.toNat 'A')
  cs := cs ++ [("irq_asserted", (dev m).irq == true)]

  -- 6. RX read + IRQ deassert after draining
  let (rxv, m4) := rd m (UART_BASE + 0x0); m := m4
  cs := cs ++ [("rx_read_value", rxv == BitVec.ofNat 32 (Char.toNat 'A')),
               ("irq_deasserted", (dev m).irq == false)]

  -- 7. write-1-to-clear overrun
  m := pushRx m (Char.toNat 'B')
  m := pushRx m (Char.toNat 'C')           -- second unread byte → OVR
  let ovrBefore := uartSr (dev m) &&& UART_OVR != 0
  m := wr m (UART_BASE + 0x4) UART_OVR      -- write 1 to OVR → clear
  let ovrAfter := uartSr (dev m) &&& UART_OVR != 0
  cs := cs ++ [("w1c_overrun", ovrBefore && ! ovrAfter)]

  -- 8. finding 4: a 32-bit access crossing the device window end faults
  let crossRead := (m.busRead (BitVec.ofNat 32 (UART_BASE + 0xFE)) 32).1
  cs := cs ++ [("device_cross_window_faults",
                match crossRead with | .error .cross => true | _ => false)]

  return cs

def main : IO Unit := do
  let mut allOk := true
  for (name, ok) in checks do
    let st := if ok then "ok" else "FAIL"
    IO.println s!"{name}: {st}"
    if !ok then allOk := false
  if !allOk then throw (IO.userError "device experiment failed")
  IO.println "device experiment: PASS"
