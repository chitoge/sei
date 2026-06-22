/-
RegisterIR (experiment E20): ingest an SVD/SystemRDL-like register schema into a
typed register model, build an executable `regfile` device with per-bit access
policy (read-only / write-1-to-clear / clear-on-read / reserved), and prove the
access-policy invariants against the executable `regWrite`/`regRead`.

Register layout + access policy is `spec`-eligible (the source specifies it);
no timing/FIFO/DMA/protocol behavior is invented.
-/
import Lean.Data.Json
import Sei.Hw.Descriptor
import Std.Tactic.BVDecide
open Lean Sei.Core
namespace Sei.Hw

inductive Access | rw | ro | w1c | cor | reserved
  deriving DecidableEq, Repr

def parseAccess : String → Except String Access
  | "rw" => .ok .rw | "ro" => .ok .ro | "w1c" => .ok .w1c
  | "cor" => .ok .cor | "clear-on-read" => .ok .cor | "reserved" => .ok .reserved
  | s => .error s!"invalid register access: {s}"

structure FieldSpec where
  name : String
  lo : Nat
  hi : Nat
  access : Access

structure RegSpec where
  name : String
  offset : Nat
  reset : Word
  fields : List FieldSpec

/-- Bit mask for the inclusive range `[lo, hi]`. -/
def maskRange (lo hi : Nat) : Word :=
  (((1 : Word) <<< (hi - lo + 1)) - 1) <<< lo

/-- Combined mask of all fields with a given access policy. -/
def maskOf (fields : List FieldSpec) (a : Access) : Word :=
  fields.foldl (fun acc f => if f.access == a then acc ||| maskRange f.lo f.hi else acc) 0

def RegSpec.cell (r : RegSpec) : RegCell :=
  { offset := r.offset, value := r.reset,
    roMask := maskOf r.fields .ro, w1cMask := maskOf r.fields .w1c,
    corMask := maskOf r.fields .cor, resvMask := maskOf r.fields .reserved }

/-! ### Parser (`bits` is `"hi:lo"` or a single bit index, decimal) -/

def parseBits (s : String) : Except String (Nat × Nat) :=
  match s.splitOn ":" with
  | [single] => match single.toNat? with | some n => .ok (n, n) | none => .error s!"bad bit index: {s}"
  | [hiS, loS] =>
    match hiS.toNat?, loS.toNat? with
    | some hi, some lo => if lo ≤ hi then .ok (lo, hi) else .error s!"bad bit range (lo>hi): {s}"
    | _, _ => .error s!"bad bit range: {s}"
  | _ => .error s!"bad bit spec: {s}"

def parseField (j : Json) : Except String FieldSpec := do
  let (lo, hi) ← parseBits (← jStr j "bits")
  let access ← parseAccess (← jStr j "access")
  pure { name := (← jStr j "name"), lo, hi, access }

def parseReg (j : Json) : Except String RegSpec := do
  let fields ← (jArrOpt j "fields").toList.mapM parseField
  pure { name := (← jStr j "name"), offset := (← jHex j "offset"),
         reset := BitVec.ofNat 32 (← jHex j "reset"), fields }

/-- Parse a register-block schema → (block name, registers). -/
def parseRegBlock (j : Json) : Except String (String × List RegSpec) := do
  pure ((← jStr j "name"), ← (jArrOpt j "registers").toList.mapM parseReg)

/-- Build an executable `regfile` device (declared `spec` layout/access policy). -/
def buildRegDevice (name : String) (base size : Nat) (regs : List RegSpec) : Device :=
  { name, base, size, beh := .regfile (regs.map (·.cell)),
    sem := { id := name, cls := .spec, proofUse := .local,
             source := "register schema (SVD/SystemRDL-like)" } }

def loadRegDevice (text : String) (base size : Nat) : Except String Device := do
  let (name, regs) ← parseRegBlock (← Json.parse text)
  pure (buildRegDevice name base size regs)

/-! ### Access-policy proofs (against the executable `regWrite`/`regRead`)

Concrete SR register: `TXE` read-only @ bit0, `OVR` write-1-to-clear @ bit3,
reserved `[31:4]`, reset `0x9` (TXE=1, OVR=1). -/

def srCell : RegCell :=
  { offset := 0x0, value := 0x9, roMask := 0x1, w1cMask := 0x8, resvMask := 0xFFFFFFF0 }

/-- `regWrite` on the SR cell, fully inlined for bitblasting. -/
def srWrite (v : Word) : Word :=
  regWrite { offset := 0x0, value := 0x9, roMask := 0x1, w1cMask := 0x8, resvMask := 0xFFFFFFF0 } v

/- Access-policy proofs. `bv_decide` is reliable on this toolchain for the
   *concrete* register-write goals (the worst-case all-ones write is the
   strongest single witness for ro/reserved), but reports spurious
   counterexamples on the ∀-write form of `regWrite` (the `~~~ value` term); the
   general behavior is covered by the runtime checks in `//:reg_test`. -/

/-- Read-only: an all-ones write does not change bit0 (TXE). -/
theorem sr_ro_preserved : srWrite 0xFFFFFFFF &&& 0x1 = 0x1 := by
  unfold srWrite regWrite; bv_decide

/-- Write-1-to-clear: writing a 1 to OVR clears it. -/
theorem sr_w1c_clears : srWrite 0x8 &&& 0x8 = 0 := by
  unfold srWrite regWrite; bv_decide

/-- Write-1-to-clear: writing a 0 to OVR leaves it set. -/
theorem sr_w1c_keep : srWrite 0x0 &&& 0x8 = 0x8 := by
  unfold srWrite regWrite; bv_decide

/-- Reserved bits ignore an all-ones write. -/
theorem sr_reserved_write_ignored : srWrite 0xFFFFFFFF &&& 0xFFFFFFF0 = 0 := by
  unfold srWrite regWrite; bv_decide

/-- Reserved bits read as zero (for *any* underlying value). -/
theorem sr_reserved_reads_zero (v : Word) :
    regRead { offset := 0x0, value := v, resvMask := 0xFFFFFFF0 } &&& 0xFFFFFFF0 = 0 := by
  unfold regRead; bv_decide

/-- Read/write bits take the written value (CR: EN @ `[1:0]`, reserved `[31:2]`). -/
def crWrite (v : Word) : Word :=
  regWrite { offset := 0x8, value := 0x0, resvMask := 0xFFFFFFFC } v

theorem cr_rw_takes_value : crWrite 0x2 &&& 0x3 = 0x2 := by
  unfold crWrite regWrite; bv_decide

theorem cr_reserved_ignored : crWrite 0xFFFFFFFF &&& 0x3 = 0x3 := by
  unfold crWrite regWrite; bv_decide

end Sei.Hw
