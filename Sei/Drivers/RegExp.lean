/-
E20 test: ingest a register schema (SVD/SystemRDL-like) into an executable
`regfile` device, then exercise the access policies at runtime through the bus —
read-only preserved, write-1-to-clear, reserved ignored on write and read-as-0,
rw takes value — and confirm the events carry `spec` provenance. The static
access-policy invariants are proven in `Sei/Hw/RegisterIR.lean` (bv_decide).
Exit 0 = pass.
-/
import Sei.Core
import Sei.Hw.Descriptor
import Sei.Hw.RegisterIR
open Lean Sei.Core Sei.Hw

def q (s : String) : String := s.replace "'" "\""

-- SR: TXE ro@0, OVR w1c@3, reserved[31:4], reset 0x9.  CR: EN rw@[1:0], reserved[31:2].
def schema : String := q
  "{'name':'uart_regs','registers':[{'name':'SR','offset':'0x0','reset':'0x9','fields':[{'name':'TXE','bits':'0','access':'ro'},{'name':'OVR','bits':'3','access':'w1c'},{'name':'RESV','bits':'31:4','access':'reserved'}]},{'name':'CR','offset':'0x8','reset':'0x0','fields':[{'name':'EN','bits':'1:0','access':'rw'},{'name':'RESV','bits':'31:2','access':'reserved'}]}]}"

def BASE : Nat := 0x40000000

def regChecks : Except String (List (String × Bool)) := do
  let dev ← loadRegDevice schema BASE 0x100
  let m : Machine :=
    { regions := #[mkRegion "ram" 0 0x1000 Kind.ram (parsePerms "rw") true], devices := #[dev] }
  let rd := fun (m : Machine) (off : Nat) =>
    let (r, m) := m.busRead (BitVec.ofNat 32 (BASE + off)) 32; ((r.toOption.getD 0 : Word), m)
  let wr := fun (m : Machine) (off : Nat) (v : Word) =>
    (m.busWrite (BitVec.ofNat 32 (BASE + off)) v 32).2
  let (sr0, m) := rd m 0x0            -- initial: TXE+OVR
  let m := wr m 0x0 0x8              -- write OVR=1 → w1c clears
  let (sr1, m) := rd m 0x0
  let m := wr m 0x0 0xFFFFFFFF       -- all ones
  let (sr2, m) := rd m 0x0
  let m := wr m 0x8 0x3              -- CR EN = 3
  let (cr0, m) := rd m 0x8
  let m := wr m 0x8 0xFFFFFFFF       -- reserved write
  let (cr1, m) := rd m 0x8
  let specEvents := m.trace.all fun ev => match ev.effect with
    | .mmioRead .. | .mmioWrite .. => ev.prov.cls == SemClass.spec
    | _ => true
  pure [ ("sr_initial_reads_0x9", sr0 == 0x9),
         ("ro_kept_w1c_cleared", sr1 == 0x1),
         ("allones_respects_policy", sr2 == 0x7),
         ("rw_takes_value", cr0 == 0x3),
         ("reserved_write_ignored", cr1 == 0x3),
         ("events_classified_spec", specEvents) ]

def isErr {α} : Except String α → Bool | .error _ => true | .ok _ => false

-- Fail-closed register parsing: invalid access string / malformed bit range reject.
def badAccess : String := q
  "{'name':'r','registers':[{'name':'X','offset':'0x0','reset':'0x0','fields':[{'name':'F','bits':'0','access':'wibble'}]}]}"
def badBits : String := q
  "{'name':'r','registers':[{'name':'X','offset':'0x0','reset':'0x0','fields':[{'name':'F','bits':'3:9','access':'rw'}]}]}"

def negChecks : List (String × Bool) :=
  [ ("invalid_access_rejected", isErr (loadRegDevice badAccess 0 0x100)),
    ("malformed_bits_rejected", isErr (loadRegDevice badBits 0 0x100)) ]

def main : IO Unit := do
  match regChecks with
  | .error e => throw (IO.userError s!"register ingestion failed: {e}")
  | .ok checks =>
    let mut ok := true
    for (n, b) in checks ++ negChecks do
      let tag := if b then "ok" else "FAIL"
      IO.println s!"{n}: {tag}"
      if !b then ok := false
    if !ok then throw (IO.userError "register access-policy checks failed")
    IO.println "register IR (E20): PASS"
