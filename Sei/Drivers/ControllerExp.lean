/-
L4 test: controller-first platform models used from descriptor-backed runs.
A descriptor instantiates a DDR controller that gates a DRAM region; ARM firmware
runs the init sequence and then reads DRAM successfully. A watchdog honors its
declared policy (disabled / serviced / reset). Snapshot is the pure Machine value.
Exit 0 = pass.
-/
import Sei.Core
import Sei.Hw.Descriptor
import Sei.Isa.Arm
open Lean Sei.Core Sei.Hw Sei.Isa.Arm

def q (s : String) : String := s.replace "'" "\""

-- firmware: init DDR (store 1 to 0x50000004) then load DRAM[0] into r3
def fw : ByteArray := bytesToBA (assemble
  [ MOVW 0 1, MOVW 1 0x0004, MOVT 1 0x5000, STR 0 1 0,
    MOVW 2 0, MOVT 2 0x8000, LDR 3 2 0, B 0x1C 0x1C ] true)
def dram : ByteArray := bytesToBA (encodeBytes true 0xD4A 4)

def desc : String := q
  "{'cpu':{'arch':'arm','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'rom','base':'0x0','size':'0x1000','kind':'rom','perms':'rx','image':'fw'},{'name':'dram','base':'0x80000000','size':'0x1000','kind':'ram','perms':'rw','image':'dram','gated':true}],'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}},'devices':[{'name':'ddr0','type':'ddr','base':'0x50000000','size':'0x100','gates':'dram','semantics':{'class':'observational','proof_use':'none'}}]}"

def loadCtrl : Except String Machine := do
  loadMachine (← parseDescriptor (← Json.parse desc)) [("fw", fw), ("dram", dram)]

def ddrFirmwareReadsDram : Bool :=
  match loadCtrl with
  | .ok m =>
    let (c, _) := runArm 40 (({} : Cpu), m)
    c.regs.getD 3 0 == (0xD4A : Word)
  | .error _ => false

-- watchdog: read STATUS `reads` times from a fresh device, return the last value
def wdMachine (policy : String) : Machine :=
  { devices := #[{ name := "wd", base := 0x60000000, size := 0x100, beh := .watchdog 0 2 policy,
                   sem := { id := "wd", cls := .observational, proofUse := .none } }] }
def readStatus (m : Machine) : Word × Machine :=
  let (r, m) := m.busRead 0x60000000 32; (r.toOption.getD 0, m)
def service (m : Machine) : Machine := (m.busWrite (BitVec.ofNat 32 0x60000004) 1 32).2

def wdFires (policy : String) (n : Nat) : Bool := Id.run do
  let mut m := wdMachine policy
  let mut last : Word := 0
  for _ in [0:n] do let (s, m') := readStatus m; m := m'; last := s
  return last == 1

def wdServiced : Bool := Id.run do
  let mut m := wdMachine "serviced"
  let (_, m1) := readStatus m; m := m1
  let (_, m2) := readStatus m; m := m2
  m := service m                       -- kick before timeout
  let (_, m3) := readStatus m; m := m3
  let (s, _) := readStatus m
  return s == 0                        -- did not fire after servicing

-- #7: descriptor `type:"increasing-timer"` lowers to an executable free-running
-- counter (BRO1 0xd0d00400), and `type:"const"` returns its constant reset value.
def periphDesc : String := q
  "{'cpu':{'arch':'arm','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'rom','base':'0x0','size':'0x1000','kind':'rom','perms':'rx'}],'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}},'devices':[{'name':'timer','type':'increasing-timer','base':'0xd0d00400','size':'0x4','step':'0x1000','semantics':{'class':'derived','proof_use':'local'}},{'name':'stat','type':'const','base':'0xd0b0000c','size':'0x4','schema':{'registers':[{'name':'R','offset':'0x0','reset':'0x80000000'}]},'semantics':{'class':'derived','proof_use':'local'}}]}"

def loadPeriph : Except String Machine := do
  loadMachine (← parseDescriptor (← Json.parse periphDesc)) []

def timerIncrements : Bool :=
  match loadPeriph with
  | .ok m =>
    let (a, m) := m.busRead (BitVec.ofNat 32 0xd0d00400) 32
    let (b, _) := m.busRead (BitVec.ofNat 32 0xd0d00400) 32
    b.toOption.getD 0 == a.toOption.getD 0 + 0x1000
  | .error _ => false

def constReads : Bool :=
  match loadPeriph with
  | .ok m => (m.busRead (BitVec.ofNat 32 0xd0b0000c) 32).1.toOption.getD 0 == 0x80000000
  | .error _ => false

-- snapshot: a saved Machine value is unaffected by later mutation
def snapshotHolds : Bool :=
  match loadCtrl with
  | .ok m =>
    let snap := m
    let advanced := (m.busWrite (BitVec.ofNat 32 0x50000004) 1 32).2   -- enable dram
    -- snap's dram is still gated (disabled); advanced's is enabled
    (snap.regions.any (fun r => r.name == "dram" && r.enabled == false)) &&
    (advanced.regions.any (fun r => r.name == "dram" && r.enabled == true))
  | .error _ => false

def checks : List (String × Bool) :=
  [ ("ddr_controller_from_descriptor_firmware", ddrFirmwareReadsDram),
    ("watchdog_disabled_never_fires", ! wdFires "disabled" 5),
    ("watchdog_reset_fires", wdFires "reset" 5),
    ("watchdog_serviced_holds", wdServiced),
    ("increasing_timer_lowers", timerIncrements),
    ("const_device_lowers", constReads),
    ("snapshot_covers_controller_state", snapshotHolds) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "controller checks failed")
  IO.println "controller-first platform models (L4): PASS"
