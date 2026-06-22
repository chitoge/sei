/-
L6 test: the Unicorn-like API surface. Exercises load, memory read/write,
add/remove device, snapshot/fork, hook queries, bounded run, and export — over a
descriptor of the same shape the Lean tests use. Exit 0 = pass.
-/
import Sei.Core
import Sei.Api
import Sei.Isa.Arm
open Sei.Core Sei.Hw Sei.Api Sei.Isa.Arm

def q (s : String) : String := s.replace "'" "\""

def desc : String := q
  "{'cpu':{'arch':'arm','endian':'little'},'entry':{'reset_pc':'0x0'},'memory':[{'name':'rom','base':'0x0','size':'0x1000','kind':'rom','perms':'rx','image':'fw'},{'name':'ram','base':'0x1000','size':'0x1000','kind':'ram','perms':'rw'}],'mmio':{'default_unknown_policy':{'on_read':'default-value','value':'0x0','on_write':'log-drop'}}}"
def fw : ByteArray := bytesToBA (assemble [MOVW 1 0x42, B 0x4 0x4] true)   -- r1=0x42, then frontier

def checks : List (String × Bool) :=
  match load desc [("fw", fw)] with
  | .error _ => [("load", false)]
  | .ok m =>
    let (wres, m2) := memWrite m 0x1000 0xABCD 32             -- write to ram (returns fault)
    let (rdv, _) := memRead m2 0x1000 32
    let (wbad, _) := memWrite m 0x0 0x1 32                    -- write to read-only ROM → perm fault
    let extra : Device := { name := "x", base := 0x50000000, size := 0x10, beh := .regStub [] }
    let m3 := addDevice m extra                               -- preserves busWellFormed → ok
    let bad := addDevice m { name := "ov", base := 0x0, size := 0x10, beh := .regStub [] }  -- shadows rom
    let m4 := (m3.toOption.getD m)
    -- snapshot/fork exercises
    let snap := snapshot m                              -- capture state before any writes
    let (_, mMut) := memWrite m 0x1000 0xBEEF 32       -- mutate m (creates new value)
    let (vSnap, _) := memRead snap 0x1000 32            -- snap is pre-mutation copy
    let mRes := restore snap                             -- restore is identity on value
    let (vRes, _) := memRead mRes 0x1000 32
    let (fA, fB) := fork m                              -- two independent copies
    let (_, fBMut) := memWrite fB 0x1000 0xF00D 32     -- mutate fB only
    let (vFA, _) := memRead fA 0x1000 32               -- fA must be unchanged
    let (vFB, _) := memRead fBMut 0x1000 32            -- fBMut should see the write
    -- snapshot of a snapshot is also unchanged (value semantics)
    let snapSnap := snapshot snap
    let (_, snapMut) := memWrite snapSnap 0x1000 0x1234 32
    let (vSnapSnap, _) := memRead snap 0x1000 32        -- original snap still clean
    let (f1, f2) := fork m
    match run desc [("fw", fw)] 30 with
    | .error _ => [("run", false)]
    | .ok (rep, mr) =>
      [ ("load_builds_machine", m.regions.size == 2),
        ("mem_write_then_read", wres.toOption.isSome && rdv.toOption.getD 0 == (0xABCD : Word)),
        ("write_fault_surfaced", match wbad with | .error _ => true | _ => false),
        ("declared_image_required", match run desc [] 30 with | .error _ => true | _ => false),
        ("add_device_ok", match m3 with | .ok m' => m'.devices.size == m.devices.size + 1 | _ => false),
        ("add_device_fails_closed", match bad with | .error _ => true | _ => false),
        ("remove_device", (removeDevice m4 "x").devices.size == m.devices.size),
        -- snapshotting exercises: value semantics mean snapshots and forks are independent copies
        ("snapshot_is_value", (snapshot m).regions.size == m.regions.size),
        ("snapshot_isolates_pre_write", vSnap.toOption.getD 1 == 0),
        ("restore_is_identity", vRes.toOption.getD 1 == 0),
        ("fork_two_handles", f1.regions.size == m.regions.size && f2.devices.size == m.devices.size),
        ("fork_a_unaffected_by_b_write", vFA.toOption.getD 1 == 0),
        ("fork_b_sees_its_own_write", vFB.toOption.getD 0 == (0xF00D : Word)),
        ("snapshot_of_snapshot_independent", vSnapSnap.toOption.getD 1 == 0),
        ("run_reports_frontier", rep.arch == "arm" && rep.stop == StopReason.blockedFrontier),
        ("code_hook_sees_exec", (codeHook mr).length > 0),
        ("export_trace_nonempty", (exportTrace mr).length > 0),
        ("deterministic_run", (run desc [("fw", fw)] 30).toOption.map (·.1) == some rep) ]

def main : IO Unit := do
  let mut ok := true
  for (n, b) in checks do
    let tag := if b then "ok" else "FAIL"
    IO.println s!"{n}: {tag}"
    if !b then ok := false
  if !ok then throw (IO.userError "API checks failed")
  IO.println "Unicorn-like API surface (L6): PASS"
