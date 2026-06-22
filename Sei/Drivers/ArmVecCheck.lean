/-
A32 differential validation: load a golden-vector corpus (generated offline from
Unicorn — see tools/armgen/) and check the SEI ARM executor reproduces each
instruction's post-state (regs, PC, NZCV). The oracle's authority is captured as
committed data; this checker is pure Lean with no external dependency.

Usage: arm_vec_check <corpus.json>   (exit 0 = all vectors match)
-/
import Sei.Core
import Sei.Isa.Arm
import Lean.Data.Json
import Lean.Data.Json.Parser
open Lean Sei.Core Sei.Isa.Arm

def jN : Json → Nat
  | .num n => n.mantissa.toNat        -- u32 test values: non-negative integers (exponent 0)
  | _ => 0
def jArr (j : Json) (k : String) : Array Json := (((j.getObjVal? k).bind (·.getArr?)).toOption).getD #[]
def jField (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD (Json.num 0)

def CODE : Nat := 0x10000

/-- Run one vector through `Arm.step`; return (post-state matches, we decoded it, why). -/
def checkVec (v : Json) : Bool × Bool × String := Id.run do
  let insn := jN (jField v "insn")
  let inRegs := jArr v "in_regs"; let inNzcv := jArr v "in_nzcv"
  let outRegs := jArr v "out_regs"; let outNzcv := jArr v "out_nzcv"
  let outPc := jN (jField v "out_pc")
  let mut regs : Array Word := (List.replicate 16 (0 : Word)).toArray
  for i in [0:15] do regs := regs.setIfInBounds i (BitVec.ofNat 32 (jN (inRegs.getD i (Json.num 0))))
  let nz (i : Nat) : Bool := jN (inNzcv.getD i (Json.num 0)) == 1
  -- match the oracle's pre-CPSR convention: SVC mode (0x13), I/F/T = 0
  let inSregs := jArr v "in_sregs"
  let mut cpu : Cpu := { regs := regs, pc := BitVec.ofNat 32 CODE,
                         n := nz 0, z := nz 1, c := nz 2, v := nz 3,
                         mode := 0x13, iMask := false, fMask := false, tbit := false,
                         haltOnSelfBranch := false }
  for i in [0:inSregs.size] do cpu := cpu.setSReg i (BitVec.ofNat 32 (jN (inSregs.getD i (Json.num 0))))
  -- code region is writable to match the oracle's RWX mapping (PC-relative stores)
  let romR := mkRegion "rom" CODE 0x1000 Kind.ram (parsePerms "rwx") true (bytesToBA (encodeBytes true insn 4))
  -- optional data window for load/store vectors
  let memBase := jN (jField v "mem_base")
  let preMem := (jArr v "pre_mem").toList.map (fun j => (BitVec.ofNat 8 (jN j) : Byte))
  let postMem := jArr v "post_mem"
  let DATA := 0x20000
  let m : Machine := { regions :=
    if preMem.isEmpty then #[romR]
    else #[romR, mkRegion "ram" DATA 0x1000 Kind.ram (parsePerms "rw") true
            (bytesToBA (List.replicate (memBase - DATA) 0 ++ preMem))] }
  let (c, m, _) := step cpu m
  -- compare r0..r14, PC, NZCV
  let mut ok := true
  let mut why := ""
  for i in [0:postMem.size] do
    let (rv, _) := m.busRead (BitVec.ofNat 32 (memBase + i)) 8
    let exp := BitVec.ofNat 32 (jN (postMem.getD i (Json.num 0)))
    if rv.toOption.getD 0 != exp then ok := false; why := why ++ s!" mem[{i}]"
  for i in [0:15] do
    let exp := BitVec.ofNat 32 (jN (outRegs.getD i (Json.num 0)))
    if c.regs.getD i 0 != exp then ok := false; why := why ++ s!" r{i}={(c.regs.getD i 0).toNat}≠{exp.toNat}"
  if c.pc != BitVec.ofNat 32 outPc then ok := false; why := why ++ s!" pc≠{outPc}"
  let onz (i : Nat) : Bool := jN (outNzcv.getD i (Json.num 0)) == 1
  if (c.n, c.z, c.c, c.v) != (onz 0, onz 1, onz 2, onz 3) then ok := false; why := why ++ " nzcv"
  let outSregs := jArr v "out_sregs"
  for i in [0:outSregs.size] do
    let exp := BitVec.ofNat 32 (jN (outSregs.getD i (Json.num 0)))
    if c.sReg i != exp then ok := false; why := why ++ s!" s{i}={(c.sReg i).toNat}≠{exp.toNat}"
  -- FPSCR: compare only the NZCV nibble (cumulative exception flags are unmodeled)
  match v.getObjVal? "out_fpscr" with
  | .ok fj =>
    if (c.fpscr.toNat &&& 0xf0000000) != (jN fj &&& 0xf0000000) then
      ok := false; why := why ++ s!" fpscr_nzcv={c.fpscr.toNat &&& 0xf0000000}≠{jN fj &&& 0xf0000000}"
  | _ => pure ()
  -- "decoded" = we did not fall through to the unsupported/undef path
  let decoded := ¬ m.effects.any (fun e => match e with | .unsupported .. => true | _ => false)
  (ok, decoded, if ok then "" else s!"insn={insn}:{why}")

def main (args : List String) : IO Unit := do
  let path := args.headD ""
  if path.isEmpty then throw (IO.userError "usage: arm_vec_check <corpus.json> [--stats]")
  let stats := args.contains "--stats"
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => throw (IO.userError s!"bad corpus json: {e}")
  | .ok j =>
    let vectors := jArr j "vectors"
    if stats then
      -- completeness/correctness report over a broad corpus: classify each as
      -- decoded+match / decoded+MISMATCH (a bug) / not-decoded (coverage gap).
      let mut okN := 0; let mut mismatch := 0; let mut undecoded := 0
      let mut bugs : List String := []
      for v in vectors do
        let (ok, decoded, why) := checkVec v
        if ok then okN := okN + 1
        else if decoded then mismatch := mismatch + 1; bugs := bugs ++ [why]
        else undecoded := undecoded + 1
      IO.println s!"A32 differential coverage over {vectors.size} oracle-accepted instructions:"
      IO.println s!"  decoded & correct : {okN}"
      IO.println s!"  decoded & MISMATCH: {mismatch}  (bugs in supported groups)"
      IO.println s!"  not decoded       : {undecoded}  (coverage gaps / unsupported groups)"
      if args.contains "--dump" then         -- per-instruction line: insn cat name
        for v in vectors do
          let (ok, decoded, _) := checkVec v
          let cat := if ok then "ok" else if decoded then "MISMATCH" else "undecoded"
          let nm := (jField v "name").getStr?.toOption.getD "?"
          let insnN := jN (jField v "insn")
          IO.println s!"VEC {insnN} {cat} {nm}"
      else for b in bugs.take 2000 do IO.println s!"  MISMATCH {b}"
      if mismatch > 0 && ¬ args.contains "--dump" then throw (IO.userError s!"{mismatch} decoded instructions mismatched the oracle")
    else
      let mut pass := 0
      let mut fails : List String := []
      for v in vectors do
        let (ok, _, why) := checkVec v
        if ok then pass := pass + 1 else fails := fails ++ [why]
      let group := (jField j "group").getStr?.toOption.getD "?"
      IO.println s!"A32 vectors: {pass}/{vectors.size} pass ({group} group)"
      for f in fails.take 20 do IO.println s!"  FAIL {f}"
      if !fails.isEmpty then throw (IO.userError s!"{fails.length} A32 vectors mismatched the oracle")
      IO.println "arm_vec_check: PASS"
