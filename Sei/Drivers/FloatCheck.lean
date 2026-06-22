/-
Validate the Sei.Float soft-float component bit-exactly against the Unicorn-
generated binary32/binary64 corpus (tools/armgen/softfloat*_gen.py). Pure Lean,
no oracle dependency at test time.  Usage: float_check <corpus.json>.
-/
import Sei.Float
import Lean.Data.Json
import Lean.Data.Json.Parser
open Lean Sei.Float

def hexDig (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
def parseHex (s : String) : Nat := (s.toList.drop 2).foldl (fun n c => n * 16 + hexDig c) 0  -- "0x…"
-- a/b/r are JSON numbers (binary32) or hex strings (binary64, > 2^53)
def jVal : Json → Nat | .num n => n.mantissa.toNat | .str s => parseHex s | _ => 0
def jField (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD (Json.num 0)
def jStr (j : Json) (k : String) : String := ((j.getObjVal? k).bind (·.getStr?)).toOption.getD ""

def apply (fmt op : String) (a b : Nat) : Nat :=
  if fmt == "f64" then
    match op with
    | "add" => f64Add a b | "sub" => f64Sub a b | "mul" => f64Mul a b | "div" => f64Div a b | "sqrt" => f64Sqrt a | _ => 0
  else
    match op with
    | "add" => f32Add a b | "sub" => f32Sub a b | "mul" => f32Mul a b | "div" => f32Div a b | "sqrt" => f32Sqrt a | _ => 0

def applyConv (op : String) (a : Nat) : Option Nat :=
  match op with
  | "u32_to_f32" => some (u32ToF Fmt.f32 a) | "i32_to_f32" => some (i32ToF Fmt.f32 a)
  | "f32_to_u32" => some (fToInt Fmt.f32 false false a) | "f32_to_i32" => some (fToInt Fmt.f32 true false a)
  | "f32_to_f64" => some (f32ToF64 a) | "f64_to_f32" => some (f64ToF32 a)
  | "u32_to_f64" => some (u32ToF Fmt.f64 a) | "i32_to_f64" => some (i32ToF Fmt.f64 a)
  | "f64_to_u32" => some (fToInt Fmt.f64 false false a) | "f64_to_i32" => some (fToInt Fmt.f64 true false a)
  -- VCVTR (round to nearest-even, FPSCR.RMode=RNE)
  | "f32_to_u32r" => some (fToInt Fmt.f32 false true a) | "f32_to_i32r" => some (fToInt Fmt.f32 true true a)
  | "f64_to_u32r" => some (fToInt Fmt.f64 false true a) | "f64_to_i32r" => some (fToInt Fmt.f64 true true a)
  | _ => none

def main (args : List String) : IO Unit := do
  let text ← IO.FS.readFile (args.headD "")
  match Json.parse text with
  | .error e => throw (IO.userError s!"bad corpus: {e}")
  | .ok j =>
    let vecs := (((j.getObjVal? "vectors").bind (·.getArr?)).toOption).getD #[]
    let mut pass := 0
    let mut perOp : List (String × Nat × Nat) := [("add",0,0),("sub",0,0),("mul",0,0),("div",0,0),("sqrt",0,0)]
    let mut fails : List String := []
    for v in vecs do
      let op := jStr v "op"; let fmt := jStr v "fmt"
      let a := jVal (jField v "a"); let b := jVal (jField v "b"); let r := jVal (jField v "r")
      let cc := jVal (jField v "c")
      let got := if op == "fma" then fma Fmt.f32 a b cc
                 else match applyConv op a with | some g => g | none => apply fmt op a b
      perOp := perOp.map (fun (o, p, f) => if o == op then (o, p + (if got == r then 1 else 0), f + (if got == r then 0 else 1)) else (o, p, f))
      if got == r then pass := pass + 1
      else if fails.length < 30 then fails := fails ++ [s!"{fmt} {op} a={a} b={b}: got {got} ≠ {r}"]
    for (o, p, f) in perOp do IO.println s!"  {o}: {p} ok, {f} mismatch"
    IO.println s!"Sei.Float: {pass}/{vecs.size} bit-exact vs Unicorn"
    for f in fails do IO.println s!"  FAIL {f}"
    if pass != vecs.size then throw (IO.userError s!"{vecs.size - pass} soft-float mismatches")
    IO.println "float_check: PASS"
