/-
MIPS32 LE differential validation: load a golden-vector corpus (generated offline
from Unicorn — see tools/mipsgen/) and check the SEI MIPS executor reproduces each
instruction's post-state (GPRs, HI, LO).

Groups validated: alu-r alu-i muldiv special2 special3.
Branches / CP0 / memory are covered by dedicated Lean-only experiments.

Usage: mips_vec_check <corpus.json>  [--stats]   (exit 0 = all match)
-/
import Sei.Core
import Sei.Isa.Mips
import Lean.Data.Json
import Lean.Data.Json.Parser
open Lean Sei.Core Sei.Isa.Mips

def jN : Json → Nat
  | .num n => n.mantissa.toNat
  | _ => 0
def jArr (j : Json) (k : String) : Array Json := (((j.getObjVal? k).bind (·.getArr?)).toOption).getD #[]
def jField (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD (Json.num 0)
def jHas (j : Json) (k : String) : Bool :=
  match j.getObjVal? k with | .ok _ => true | .error _ => false

-- Physical base of the kseg0-mapped code window: cpu.pc = CODE_VIRT → phys = CODE_PHYS
def CODE_PHYS : Nat := 0x00000000
def CODE_VIRT : Nat := 0x80000000

-- Data memory window for memory-op vectors (oracle uses physical; SEI uses kseg0 virtual)
def DATA_PHYS : Nat := 0x00001000
def DATA_VIRT : Nat := 0x80001000

/-- Run one vector through `Mips.step`; return (post-state matches, was decoded, why). -/
def checkVec (v : Json) : Bool × Bool × String := Id.run do
  let insn := jN (jField v "insn")
  let inRegsJ := jArr v "in_regs"
  let outRegsJ := jArr v "out_regs"
  let in_hi  := BitVec.ofNat 32 (jN (jField v "in_hi"))
  let in_lo  := BitVec.ofNat 32 (jN (jField v "in_lo"))
  let exp_hi := BitVec.ofNat 32 (jN (jField v "out_hi"))
  let exp_lo := BitVec.ofNat 32 (jN (jField v "out_lo"))
  -- Build initial GPR array (32 registers, r0 fixed at 0)
  let mut regs : Array Word := (List.replicate 32 (0 : Word)).toArray
  for i in [1:32] do
    regs := regs.setIfInBounds i (BitVec.ofNat 32 (jN (inRegsJ.getD i (Json.num 0))))
  -- Memory-op vectors carry base_reg/mem_virt: substitute the oracle's physical
  -- address in base_reg with the SEI kseg0 virtual address.
  let base_reg := jN (jField v "base_reg")
  let mem_virt := jN (jField v "mem_virt")
  let has_mem  := jHas v "in_mem_word"
  if mem_virt != 0 && base_reg != 0 then
    regs := regs.setIfInBounds base_reg (BitVec.ofNat 32 mem_virt)
  -- FPR state
  let inFprsJ := jArr v "in_fprs"
  let mut fprs : Array Word := (List.replicate 32 (0 : Word)).toArray
  for i in [0:32] do
    fprs := fprs.setIfInBounds i (BitVec.ofNat 32 (jN (inFprsJ.getD i (Json.num 0))))
  let in_fcr31 := if jHas v "in_fcr31" then jN (jField v "in_fcr31") else 0
  let cpu : Cpu := { regs := regs, hi := in_hi, lo := in_lo,
                     pc := BitVec.ofNat 32 CODE_VIRT,
                     npc := BitVec.ofNat 32 (CODE_VIRT + 4),
                     fprs := fprs,
                     fcr31 := BitVec.ofNat 32 in_fcr31 }
  -- ROM at physical 0x0 (kseg0: virt 0x80000000 → phys 0x0)
  let rom := mkRegion "rom" CODE_PHYS 0x1000 Kind.ram (parsePerms "rwx") true
               (bytesToBA (encodeBytes true insn 4))
  -- Optional DATA region for memory-op vectors (kseg0: virt 0x80001000 → phys 0x00001000)
  let in_mem_word := jN (jField v "in_mem_word")
  let dataRegion := mkRegion "data" DATA_PHYS 0x1000 Kind.ram (parsePerms "rw") true
                     (bytesToBA (encodeBytes true in_mem_word 4))
  let m : Machine := { regions := if has_mem then #[rom, dataRegion] else #[rom] }
  let (c, m_after, _) := step cpu m
  -- "decoded" = did not halt (reserved/unsupported paths set halted := true)
  let decoded := ¬ c.halted
  let mut ok := true
  let mut why := ""
  -- Compare all 32 GPRs (r0 is always 0 by invariant).
  -- Skip base_reg for memory vectors: oracle has physical addr, checker has virtual.
  for i in [0:32] do
    if mem_virt != 0 && i == base_reg then continue
    let exp := BitVec.ofNat 32 (jN (outRegsJ.getD i (Json.num 0)))
    if c.regs.getD i 0 != exp then
      ok := false
      why := why ++ s!" r{i}={( c.regs.getD i 0).toNat}≠{exp.toNat}"
  -- Compare HI / LO
  if c.hi != exp_hi then ok := false; why := why ++ s!" hi={c.hi.toNat}≠{exp_hi.toNat}"
  if c.lo != exp_lo then ok := false; why := why ++ s!" lo={c.lo.toNat}≠{exp_lo.toNat}"
  -- Compare memory word for store vectors (out_mem_word present)
  if jHas v "out_mem_word" then
    let exp_mem := jN (jField v "out_mem_word")
    let (mres, _) := m_after.busRead (BitVec.ofNat 32 DATA_PHYS) 32
    match mres with
    | .ok got_mem =>
      if got_mem.toNat != exp_mem then
        ok := false; why := why ++ s!" mem={got_mem.toNat}≠{exp_mem}"
    | .error _ =>
      ok := false; why := why ++ " mem=<read_error>"
  -- Compare FPRs if out_fprs present
  if jHas v "out_fprs" then
    let outFprsJ := jArr v "out_fprs"
    for i in [0:32] do
      let exp := BitVec.ofNat 32 (jN (outFprsJ.getD i (Json.num 0)))
      if c.fprs.getD i 0 != exp then
        ok := false
        why := why ++ s!" f{i}={( c.fprs.getD i 0).toNat}≠{exp.toNat}"
  -- Compare FCR31 if out_fcr31 present
  if jHas v "out_fcr31" then
    let exp_fcr31 := jN (jField v "out_fcr31")
    if c.fcr31.toNat != exp_fcr31 then
      ok := false
      why := why ++ s!" fcr31={c.fcr31.toNat}≠{exp_fcr31}"
  (ok, decoded, if ok then "" else s!"insn={insn}:{why}")

def main (args : List String) : IO Unit := do
  let path := args.headD ""
  if path.isEmpty then throw (IO.userError "usage: mips_vec_check <corpus.json> [--stats]")
  let stats := args.contains "--stats"
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => throw (IO.userError s!"bad corpus json: {e}")
  | .ok j =>
    let vectors := jArr j "vectors"
    if stats then
      let mut okN := 0; let mut mismatch := 0; let mut undecoded := 0
      let mut bugs : List String := []
      for v in vectors do
        let (ok, decoded, why) := checkVec v
        if ok then okN := okN + 1
        else if decoded then mismatch := mismatch + 1; bugs := bugs ++ [why]
        else undecoded := undecoded + 1
      let grp := (jField j "group").getStr?.toOption.getD "?"
      IO.println s!"MIPS32 differential coverage over {vectors.size} oracle-accepted instructions ({grp}):"
      IO.println s!"  decoded & correct : {okN}"
      IO.println s!"  decoded & MISMATCH: {mismatch}  (bugs in supported groups)"
      IO.println s!"  not decoded       : {undecoded}  (coverage gaps)"
      for b in bugs.take 2000 do IO.println s!"  MISMATCH {b}"
      if mismatch > 0 then throw (IO.userError s!"{mismatch} decoded instructions mismatched the oracle")
    else
      let mut pass := 0
      let mut fails : List String := []
      for v in vectors do
        let (ok, _, why) := checkVec v
        if ok then pass := pass + 1 else fails := fails ++ [why]
      let grp := (jField j "group").getStr?.toOption.getD "?"
      IO.println s!"MIPS32 vectors: {pass}/{vectors.size} pass ({grp} group)"
      for f in fails.take 20 do IO.println s!"  FAIL {f}"
      if !fails.isEmpty then throw (IO.userError s!"{fails.length} MIPS32 vectors mismatched the oracle")
      IO.println "mips_vec_check: PASS"
