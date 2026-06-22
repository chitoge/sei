/-
Audit (flash controller): a flash device over a backing image with deterministic
read-id / read-status / indirect read, a separate XIP direct-read mode, and
fail-closed behavior on unsupported commands. Snapshot/replay is the pure Machine
value (so two identical runs agree). Exit 0 = pass.
-/
import Sei.Core
open Sei.Core

def FLASH : Nat := 0x10000000
def backing : List Word := [0xAAAA, 0xBBBB, 0xCCCC]

def flashDev : Device :=
  { name := "flash0", base := FLASH, size := 0x100, beh := .flash backing 0 0 false,
    sem := { id := "flash0", cls := .observational, proofUse := .none, source := "flash controller" } }

def machine : Machine := { devices := #[flashDev] }

def rd (m : Machine) (off : Nat) : Word × Machine :=
  let (r, m) := m.busRead (BitVec.ofNat 32 (FLASH + off)) 32; (r.toOption.getD 0, m)
def wr (m : Machine) (off : Nat) (v : Word) : Machine := (m.busWrite (BitVec.ofNat 32 (FLASH + off)) v 32).2

def runFlash : List (String × Bool) :=
  let m := machine
  let m := wr m 0x0 0x9F; let (id, m) := rd m 0x8                -- READ_ID
  let m := wr m 0x0 0x05; let (status, m) := rd m 0x8            -- READ_STATUS
  let m := wr m 0x0 0x03; let m := wr m 0x4 0                    -- READ, addr 0
  let (d0, m) := rd m 0x8                                        -- indirect read, advances
  let (d1, m) := rd m 0x8
  let m := wr m 0x0 0xDE; let (bad, m) := rd m 0x8               -- unsupported command
  let m := wr m 0x0 0xB7; let m := wr m 0x4 2                    -- enter XIP, addr 2
  let (xipData, _) := rd m 0x8
  [ ("read_id", id == 0xC2),
    ("read_status_ready", status == 1),
    ("indirect_read_seq", d0 == 0xAAAA && d1 == 0xBBBB),
    ("unsupported_cmd_fails_closed", bad == traceFrontier),
    ("xip_direct_read", xipData == 0xCCCC) ]

def deterministic : Bool := runFlash == runFlash

def main : IO Unit := do
  let mut ok := true
  for (n, b) in runFlash ++ [("deterministic_replay", deterministic)] do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "flash controller checks failed")
  IO.println "flash controller: PASS"
