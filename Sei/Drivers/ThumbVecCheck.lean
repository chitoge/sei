/-
T16 differential validation: run Thumb golden vectors (generated offline via
tools/armgen/thumb_gen.py) through Lean stepThumb and compare post-state.
Usage: thumb_vec_check <corpus.json>   (exit 0 = all vectors match)
-/
import Sei.Core
import Sei.Isa.Arm
import Lean.Data.Json
import Lean.Data.Json.Parser
open Lean Sei.Core Sei.Isa.Arm

def jN : Json → Nat | .num n => n.mantissa.toNat | _ => 0
def jArr (j : Json) (k : String) : Array Json :=
  ((j.getObjVal? k).bind (·.getArr?)).toOption.getD #[]
def jField (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD (Json.num 0)

def CODE : Nat := 0x10000
def DATA : Nat := 0x20000

def checkThumbVec (v : Json) : Bool × String := Id.run do
  let insnBytes := (jArr v "insn").toList.map (fun j => UInt8.ofNat (jN j))
  let inRegs  := jArr v "in_regs"
  let inNzcv  := jArr v "in_nzcv"
  let outRegs := jArr v "out_regs"
  let outNzcv := jArr v "out_nzcv"
  let outPc   := jN (jField v "out_pc")
  -- Build initial CPU: Thumb mode (tbit=true), SVC mode
  let mut regs : Array Word := (List.replicate 16 (0 : Word)).toArray
  for i in [0:15] do
    regs := regs.setIfInBounds i (BitVec.ofNat 32 (jN (inRegs.getD i (Json.num 0))))
  let nz (i : Nat) : Bool := jN (inNzcv.getD i (Json.num 0)) == 1
  let cpu0 : Cpu := { regs, pc := BitVec.ofNat 32 CODE,
                      n := nz 0, z := nz 1, c := nz 2, v := nz 3,
                      mode := 0x13, tbit := true, haltOnSelfBranch := false }
  -- CODE region: instruction bytes padded with zeros (enough room for BL second halfword)
  let padded := insnBytes ++ List.replicate (8 - insnBytes.length) 0
  let codeBA  := ByteArray.mk padded.toArray
  let codeReg := mkRegion "code" CODE 0x2000 Kind.ram (parsePerms "rwx") true codeBA
  -- Optional data region for load/store vectors
  let preMem  := (jArr v "pre_mem").toList.map (fun j => UInt8.ofNat (jN j))
  let postMem := jArr v "post_mem"
  let memBase := jN (jField v "mem_base")
  let m0 : Machine :=
    if preMem.isEmpty then { regions := #[codeReg] }
    else
      let dataReg := mkRegion "data" DATA 0x1000 Kind.ram (parsePerms "rw") true
                    (ByteArray.mk (preMem.toArray))
      { regions := #[codeReg, dataReg] }
  let (c, m, _) := step cpu0 m0
  -- Compare post-state
  let mut ok  := true
  let mut why := ""
  -- Registers r0..r14
  for i in [0:15] do
    let exp := BitVec.ofNat 32 (jN (outRegs.getD i (Json.num 0)))
    if c.regs.getD i 0 != exp then
      ok := false; why := why ++ s!" r{i}={(c.regs.getD i 0).toNat}≠{exp.toNat}"
  -- PC
  if c.pc != BitVec.ofNat 32 outPc then
    ok := false; why := why ++ s!" pc={(c.pc.toNat)}≠{outPc}"
  -- NZCV
  let onz (i : Nat) : Bool := jN (outNzcv.getD i (Json.num 0)) == 1
  if (c.n, c.z, c.c, c.v) != (onz 0, onz 1, onz 2, onz 3) then
    ok := false; why := why ++ " nzcv"
  -- Memory (if applicable)
  for i in [0:postMem.size] do
    let (rv, _) := m.busRead (BitVec.ofNat 32 (memBase + i)) 8
    let exp := BitVec.ofNat 32 (jN (postMem.getD i (Json.num 0)))
    if rv.toOption.getD 0 != exp then ok := false; why := why ++ s!" mem[{i}]"
  let label := (jField v "label").getStr?.toOption.getD
               ((jField v "group").getStr?.toOption.getD "?")
  (ok, if ok then "" else s!"[{label}] insn={insnBytes}:{why}")

def main (args : List String) : IO Unit := do
  let path := args.headD ""
  if path.isEmpty then throw (IO.userError "usage: thumb_vec_check <corpus.json>")
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => throw (IO.userError s!"bad json: {e}")
  | .ok j =>
    let vectors := jArr j "vectors"
    let mut pass := 0
    let mut fails : List String := []
    for v in vectors do
      let (ok, why) := checkThumbVec v
      if ok then pass := pass + 1 else fails := fails ++ [why]
    IO.println s!"T16 vectors: {pass}/{vectors.size} pass"
    for f in fails.take 30 do IO.println s!"  FAIL {f}"
    if !fails.isEmpty then throw (IO.userError s!"{fails.length} T16 vectors mismatched oracle")
    IO.println "thumb_vec_check: PASS"
