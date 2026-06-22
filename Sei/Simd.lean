/-
Sei.Simd — a standalone Advanced SIMD (NEON) lane-math component (no ISA / Machine
/ Core dependency; pure functions over bit patterns). Element-size-parametric;
operates on a `w`-bit register value (w ∈ {64, 128}) as lanes of `esize` bits. The
vector floating-point lanes delegate to Sei.Float. See docs/neon-subsystem-plan.md.
-/
import Sei.Float

namespace Sei.Simd

def mask (bits : Nat) : Nat := (1 <<< bits) - 1

/-! ### lane helpers -/

/-- Extract lane `i` (`esize` bits) from a `w`-bit register value. -/
def lane (esize x i : Nat) : Nat := (x >>> (i * esize)) &&& mask esize

/-- Build a `w`-bit value from `w/esize` lanes produced by `f i (lane i)`. -/
def mapLanes (w esize x : Nat) (f : Nat → Nat → Nat) : Nat := Id.run do
  let n := w / esize
  let mut r := 0
  for i in [0:n] do
    r := r ||| ((f i (lane esize x i) &&& mask esize) <<< (i * esize))
  return r

/-- Zip two `w`-bit values lane-wise. -/
def zipLanes (w esize x y : Nat) (f : Nat → Nat → Nat → Nat) : Nat := Id.run do
  let n := w / esize
  let mut r := 0
  for i in [0:n] do
    r := r ||| ((f i (lane esize x i) (lane esize y i) &&& mask esize) <<< (i * esize))
  return r

/-! ### P1 bitwise (whole-register) -/

def vand (_w a b : Nat) : Nat := a &&& b
def vorr (_w a b : Nat) : Nat := a ||| b
def veor (_w a b : Nat) : Nat := a ^^^ b
def vbic (w a b : Nat) : Nat := a &&& (mask w ^^^ b)                 -- a AND NOT b
def vorn (w a b : Nat) : Nat := (a ||| (mask w ^^^ b)) &&& mask w    -- a OR NOT b
def vmvn (w a : Nat) : Nat := mask w ^^^ a
-- select: original destination `d` plus the two source operands `n`, `m`
def vbsl (w d n m : Nat) : Nat := (d &&& n) ||| ((mask w ^^^ d) &&& m)
def vbit (w d n m : Nat) : Nat := (n &&& m) ||| (d &&& (mask w ^^^ m))
def vbif (w d n m : Nat) : Nat := (n &&& (mask w ^^^ m)) ||| (d &&& m)

/-- Zip three `w`-bit values lane-wise (for multiply-accumulate). -/
def zip3Lanes (w esize x y z : Nat) (f : Nat → Nat → Nat → Nat → Nat) : Nat := Id.run do
  let n := w / esize
  let mut r := 0
  for i in [0:n] do
    r := r ||| ((f i (lane esize x i) (lane esize y i) (lane esize z i) &&& mask esize) <<< (i * esize))
  return r

/-! ### P3 integer arithmetic (element-wise, modular — signed/unsigned agree) -/

def vadd (w esize a b : Nat) : Nat := zipLanes w esize a b (fun _ x y => x + y)
def vsub (w esize a b : Nat) : Nat := zipLanes w esize a b (fun _ x y => x + (1 <<< esize) - y)
def vmul (w esize a b : Nat) : Nat := zipLanes w esize a b (fun _ x y => x * y)
def vmla (w esize d a b : Nat) : Nat := zip3Lanes w esize d a b (fun _ dd x y => dd + x * y)
def vmls (w esize d a b : Nat) : Nat := zip3Lanes w esize d a b (fun _ dd x y => dd + (1 <<< (2*esize)) - (x * y))

/-! ### P4 compare / min-max / abs-diff / halving (signed `s = true`) -/

/-- Interpret an `esize`-bit lane as a signed integer. -/
def toS (esize x : Nat) : Int := if x ≥ (1 <<< (esize - 1)) then (x : Int) - (1 <<< esize) else x
def cmpMask (esize : Nat) (b : Bool) : Nat := if b then mask esize else 0

def vceq (w esize a b : Nat) : Nat := zipLanes w esize a b (fun _ x y => cmpMask esize (x == y))
def vtst (w esize a b : Nat) : Nat := zipLanes w esize a b (fun _ x y => cmpMask esize (x &&& y != 0))
def vcgt (w esize s a b : Nat) : Nat :=
  zipLanes w esize a b (fun _ x y => cmpMask esize (if s == 1 then toS esize x > toS esize y else x > y))
def vcge (w esize s a b : Nat) : Nat :=
  zipLanes w esize a b (fun _ x y => cmpMask esize (if s == 1 then toS esize x ≥ toS esize y else x ≥ y))
def vmax (w esize s a b : Nat) : Nat :=
  zipLanes w esize a b (fun _ x y => if (if s == 1 then toS esize x ≥ toS esize y else x ≥ y) then x else y)
def vmin (w esize s a b : Nat) : Nat :=
  zipLanes w esize a b (fun _ x y => if (if s == 1 then toS esize x ≤ toS esize y else x ≤ y) then x else y)
def vabd (w esize s a b : Nat) : Nat :=
  zipLanes w esize a b (fun _ x y => if s == 1 then (toS esize x - toS esize y).natAbs else (if x ≥ y then x - y else y - x))
/-- floor((x ± y + rnd)/2) for `esize` lanes, signed `s`, in two's-complement. -/
def halve (esize s rnd x y : Nat) (sub : Bool) : Nat :=
  let xs : Int := if s == 1 then toS esize x else x
  let ys : Int := if s == 1 then toS esize y else y
  let sum := if sub then xs - ys else xs + ys
  (((sum + rnd).fdiv 2).emod (1 <<< esize)).toNat
def vhadd (w esize s a b : Nat) : Nat := zipLanes w esize a b (fun _ x y => halve esize s 0 x y false)
def vhsub (w esize s a b : Nat) : Nat := zipLanes w esize a b (fun _ x y => halve esize s 0 x y true)
def vrhadd (w esize s a b : Nat) : Nat := zipLanes w esize a b (fun _ x y => halve esize s 1 x y false)

/-! ### P6 saturating -/

/-- Clamp a signed value to the `esize` signed range; two's-complement result. -/
def satS (esize : Nat) (v : Int) : Nat :=
  let hi : Int := (1 <<< (esize - 1)) - 1; let lo : Int := -(1 <<< (esize - 1))
  ((if v > hi then hi else if v < lo then lo else v).emod (1 <<< esize)).toNat
/-- Clamp to the `esize` unsigned range. -/
def satU (esize : Nat) (v : Int) : Nat :=
  let hi : Int := (1 <<< esize) - 1
  (if v > hi then hi else if v < 0 then 0 else v).toNat
def sat (esize s : Nat) (v : Int) : Nat := if s == 1 then satS esize v else satU esize v

def vqadd (w esize s a b : Nat) : Nat :=
  zipLanes w esize a b (fun _ x y => sat esize s ((if s == 1 then toS esize x else x) + (if s == 1 then toS esize y else y)))
def vqsub (w esize s a b : Nat) : Nat :=
  zipLanes w esize a b (fun _ x y => sat esize s ((if s == 1 then toS esize x else x) - (if s == 1 then toS esize y else y)))

/-- Saturating register variable shift (VQSHL/VQRSHL reg): left shifts saturate. -/
def vqshlReg (w esize s rnd a shv : Nat) : Nat := zipLanes w esize a shv (fun _ x amtRaw =>
  let amt := toS 8 (amtRaw &&& 0xff)
  let val : Int := if s == 1 then toS esize x else x
  if amt ≥ 0 then sat esize s (val * (1 <<< amt.toNat))
  else
    let sh := (-amt).toNat
    sat esize s ((if rnd == 1 then val + (1 <<< (sh - 1)) else val).fdiv (1 <<< sh)))

/-- Saturating shift-left by immediate. `su=1` ⇒ VQSHLU (signed in, unsigned out). -/
def vqshlImm (w esize s su sh a : Nat) : Nat := mapLanes w esize a (fun _ x =>
  let val : Int := if s == 1 || su == 1 then toS esize x else x
  if su == 1 then satU esize (val * (1 <<< sh)) else sat esize s (val * (1 <<< sh)))

/-! ### P5 shifts -/

/-- One lane right-shifted by `sh` (signed `s`, rounding `rnd`), two's-complement. -/
def shrLane (esize s rnd sh x : Nat) : Nat :=
  let val : Int := if s == 1 then toS esize x else x
  let rounded : Int := if rnd == 1 then val + (1 <<< (sh - 1)) else val
  ((rounded.fdiv (1 <<< sh)).emod (1 <<< esize)).toNat

def vshrImm (w esize s rnd sh a : Nat) : Nat := mapLanes w esize a (fun _ x => shrLane esize s rnd sh x)
def vsraImm (w esize s rnd sh d a : Nat) : Nat :=
  zipLanes w esize d a (fun _ dd x => dd + shrLane esize s rnd sh x)        -- accumulate (modular)
def vshlImm (w esize sh a : Nat) : Nat := mapLanes w esize a (fun _ x => x <<< sh)
def vsli (w esize sh d a : Nat) : Nat :=
  zipLanes w esize d a (fun _ dd x => ((x <<< sh) &&& mask esize) ||| (dd &&& mask sh))
def vsri (w esize sh d a : Nat) : Nat :=
  zipLanes w esize d a (fun _ dd x => (x >>> sh) ||| (dd &&& (mask esize ^^^ mask (esize - sh))))

/-- Register variable shift: lane of `a` shifted by the signed low byte of `shv`. -/
def vshlReg (w esize s rnd a shv : Nat) : Nat := zipLanes w esize a shv (fun _ x amtRaw =>
  let amt := toS 8 (amtRaw &&& 0xff)
  if amt ≥ (esize : Int) then 0
  else if amt ≥ 0 then (x <<< amt.toNat) &&& mask esize
  else
    let sh := (-amt).toNat
    let val : Int := if s == 1 then toS esize x else x
    let rounded : Int := if rnd == 1 then val + (1 <<< (sh - 1)) else val
    ((rounded.fdiv (1 <<< sh)).emod (1 <<< esize)).toNat)

/-! ### P9 vector floating-point (Advanced SIMD Standard mode: flush-to-zero + default-NaN) -/

open Sei.Float (Fmt dec flush)
def F32 : Sei.Float.Fmt := Sei.Float.Fmt.f32
def fzAbs (x : Nat) : Nat := x &&& 0x7fffffff

/-- Standard-mode result wrapper: flush a finite output, force the default NaN. -/
def fpStd (r : Nat) : Nat :=
  if (dec F32 r).isNaN F32 then F32.dnan else flush F32 r
/-- Apply a binary f32 op per 32-bit lane, Standard mode (flush inputs + output). -/
def vfBin (w a b : Nat) (op : Nat → Nat → Nat) : Nat :=
  zipLanes w 32 a b (fun _ x y => fpStd (op (flush F32 x) (flush F32 y)))
def vfUn (w a : Nat) (op : Nat → Nat) : Nat := mapLanes w 32 a (fun _ x => fpStd (op (flush F32 x)))

def vfAdd (w a b : Nat) : Nat := vfBin w a b Sei.Float.f32Add
def vfSub (w a b : Nat) : Nat := vfBin w a b Sei.Float.f32Sub
def vfMul (w a b : Nat) : Nat := vfBin w a b Sei.Float.f32Mul
def vfAbd (w a b : Nat) : Nat := vfBin w a b (fun x y => fzAbs (Sei.Float.f32Sub x y))
def vfFma (w d a b : Nat) : Nat := zip3Lanes w 32 d a b (fun _ dd x y => fpStd (Sei.Float.fma F32 (flush F32 x) (flush F32 y) (flush F32 dd)))
def vfFms (w d a b : Nat) : Nat := zip3Lanes w 32 d a b (fun _ dd x y => fpStd (Sei.Float.fma F32 (flush F32 x ^^^ 0x80000000) (flush F32 y) (flush F32 dd)))
def vfMla (w d a b : Nat) : Nat := zip3Lanes w 32 d a b (fun _ dd x y => fpStd (Sei.Float.f32Add (flush F32 dd) (fpStd (Sei.Float.f32Mul (flush F32 x) (flush F32 y)))))
def vfMls (w d a b : Nat) : Nat := zip3Lanes w 32 d a b (fun _ dd x y => fpStd (Sei.Float.f32Sub (flush F32 dd) (fpStd (Sei.Float.f32Mul (flush F32 x) (flush F32 y)))))

def fcmpMask (nz target : Nat) : Nat := if nz == target then 0xffffffff else 0
def vfCeq (w a b : Nat) : Nat := zipLanes w 32 a b (fun _ x y => fcmpMask (Sei.Float.cmp F32 (flush F32 x) (flush F32 y)) 0b0110)
def vfCge (w a b : Nat) : Nat := zipLanes w 32 a b (fun _ x y =>
  let nz := Sei.Float.cmp F32 (flush F32 x) (flush F32 y); if nz == 0b0110 || nz == 0b0010 then 0xffffffff else 0)
def vfCgt (w a b : Nat) : Nat := zipLanes w 32 a b (fun _ x y => fcmpMask (Sei.Float.cmp F32 (flush F32 x) (flush F32 y)) 0b0010)
def vfAcge (w a b : Nat) : Nat := zipLanes w 32 a b (fun _ x y =>
  let nz := Sei.Float.cmp F32 (fzAbs (flush F32 x)) (fzAbs (flush F32 y)); if nz == 0b0110 || nz == 0b0010 then 0xffffffff else 0)
def vfAcgt (w a b : Nat) : Nat := zipLanes w 32 a b (fun _ x y =>
  fcmpMask (Sei.Float.cmp F32 (fzAbs (flush F32 x)) (fzAbs (flush F32 y))) 0b0010)

/-- FP max/min: NaN ⇒ default NaN; ±0 by sign (max favors +0, min −0); else by value. -/
def fmaxLane (x y : Nat) (isMax : Bool) : Nat :=
  if (dec F32 x).isNaN F32 || (dec F32 y).isNaN F32 then F32.dnan
  else if (dec F32 x).isZero && (dec F32 y).isZero then
    let neg := if isMax then (x >>> 31) &&& 1 == 1 && (y >>> 31) &&& 1 == 1
                        else (x >>> 31) &&& 1 == 1 || (y >>> 31) &&& 1 == 1
    if neg then 0x80000000 else 0
  else let nz := Sei.Float.cmp F32 x y
       if isMax then (if nz == 0b0010 || nz == 0b0110 then x else y)
       else (if nz == 0b1000 || nz == 0b0110 then x else y)
def vfMax (w a b : Nat) : Nat := zipLanes w 32 a b (fun _ x y => fmaxLane (flush F32 x) (flush F32 y) true)
def vfMin (w a b : Nat) : Nat := zipLanes w 32 a b (fun _ x y => fmaxLane (flush F32 x) (flush F32 y) false)
-- VRECPS/VRSQRTS: 0·∞ (either order) ⇒ the step constant (2.0 / 1.5), not NaN.
-- The step is FUSED on ARM (FRECPS/FRSQRTS): the product is not separately rounded.
def vfRecps (w a b : Nat) : Nat := zipLanes w 32 a b (fun _ x0 y0 =>
  let x := flush F32 x0; let y := flush F32 y0
  if ((dec F32 x).isZero && (dec F32 y).isInf F32) || ((dec F32 x).isInf F32 && (dec F32 y).isZero) then 0x40000000
  else fpStd (Sei.Float.fma F32 (x ^^^ 0x80000000) y 0x40000000))                            -- 2 − a·b (fused)
def vfRsqrts (w a b : Nat) : Nat := zipLanes w 32 a b (fun _ x0 y0 =>
  let x := flush F32 x0; let y := flush F32 y0
  if ((dec F32 x).isZero && (dec F32 y).isInf F32) || ((dec F32 x).isInf F32 && (dec F32 y).isZero) then 0x3fc00000
  else fpStd (Sei.Float.fma F32 ((Sei.Float.f32Mul x 0x3f000000) ^^^ 0x80000000) y 0x3fc00000))  -- 1.5 − (a/2)·b (fused, no overflow)
def vfAbsS (w a : Nat) : Nat := mapLanes w 32 a (fun _ x => x &&& 0x7fffffff)      -- VABS.f32 (sign clear)
def vfNegS (w a : Nat) : Nat := mapLanes w 32 a (fun _ x => x ^^^ 0x80000000)      -- VNEG.f32 (sign flip)

/-! ### P7 widening / narrowing (3-reg different lengths) -/

/-- Widen: esize-lane inputs `a`,`b` (D) → 2·esize result (Q). -/
def widenL (esize s a b : Nat) (op : Int → Int → Int) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n] do
    let x : Int := if s == 1 then toS esize (lane esize a i) else lane esize a i
    let y : Int := if s == 1 then toS esize (lane esize b i) else lane esize b i
    r := r ||| (((op x y).emod (1 <<< (2*esize))).toNat <<< (i * 2*esize))
  return r
def vaddl (esize s a b : Nat) : Nat := widenL esize s a b (· + ·)
def vsubl (esize s a b : Nat) : Nat := widenL esize s a b (· - ·)
def vmull (esize s a b : Nat) : Nat := widenL esize s a b (· * ·)
def vabdl (esize s a b : Nat) : Nat := widenL esize s a b (fun x y => (x - y).natAbs)
/-- VADDW/VSUBW: `a` is the wide (Q) operand, `b` is narrow (D). -/
def widenW (esize s a b : Nat) (sub : Bool) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n] do
    let x : Int := toS (2*esize) (lane (2*esize) a i)
    let y : Int := if s == 1 then toS esize (lane esize b i) else lane esize b i
    r := r ||| ((((if sub then x - y else x + y)).emod (1 <<< (2*esize))).toNat <<< (i * 2*esize))
  return r
/-- VMLAL/VMLSL/VABAL: accumulate the widened product/abs-diff into Qd. -/
def widenAcc (esize s d a b : Nat) (sub absdiff : Bool) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n] do
    let x : Int := if s == 1 then toS esize (lane esize a i) else lane esize a i
    let y : Int := if s == 1 then toS esize (lane esize b i) else lane esize b i
    let p : Int := if absdiff then (x - y).natAbs else x * y
    let acc : Int := lane (2*esize) d i
    r := r ||| ((((if sub then acc - p else acc + p)).emod (1 <<< (2*esize))).toNat <<< (i * 2*esize))
  return r
/-- VMOVL: widen one D operand → Q (signed/unsigned). -/
def vmovl (esize s a : Nat) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n] do
    let x : Int := if s == 1 then toS esize (lane esize a i) else lane esize a i
    r := r ||| ((x.emod (1 <<< (2*esize))).toNat <<< (i * 2*esize))
  return r

/-- VMOVN: narrow each 2·esize element of `a` (Q) to its low esize bits → D. -/
def vmovn (esize a : Nat) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n] do r := r ||| ((lane (2*esize) a i &&& mask esize) <<< (i*esize))
  return r
/-- VADDHN/VSUBHN: add/sub the wide operands, keep the high esize bits → D. -/
def vaddhn (esize a b : Nat) (sub rnd : Bool) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n] do
    let s0 := if sub then lane (2*esize) a i + (1 <<< (2*esize)) - lane (2*esize) b i
              else lane (2*esize) a i + lane (2*esize) b i
    let s := if rnd then s0 + (1 <<< (esize - 1)) else s0
    r := r ||| (((s >>> esize) &&& mask esize) <<< (i*esize))
  return r
/-- VSHRN/VRSHRN: shift each wide element right by `sh`, narrow → D. -/
def vshrn (esize rnd sh a : Nat) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n] do
    let v := lane (2*esize) a i
    let rv := if rnd == 1 then v + (1 <<< (sh - 1)) else v
    r := r ||| (((rv >>> sh) &&& mask esize) <<< (i*esize))
  return r
/-- VQMOVN/VQMOVUN/VQSHRN/VQRSHRN/VQSHRUN: saturating narrow each 2·esize element.
    op=0: signed saturate to signed (VQMOVN / VQSHRN)
    op=1: signed saturate to unsigned (VQMOVUN / VQSHRUN)
    op=2: unsigned saturate to unsigned (VQMOVN.u / VQSHRN.u) -/
def vqmovn (esize op sh rnd : Nat) (a : Nat) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n] do
    let v0 := lane (2*esize) a i
    let v := if sh == 0 then v0
             else let signed := op == 0 || op == 1
                  let sv : Int := if signed then toS (2*esize) v0 else v0
                  let rv : Int := if rnd == 1 then sv + (1 <<< (sh - 1)) else sv
                  (rv.fdiv (1 <<< sh)).emod (1 <<< (2*esize)) |>.toNat
    let sv : Int := toS (2*esize) v
    let e := if op == 0 then satS esize sv             -- signed → signed
             else if op == 1 then satU esize sv         -- signed → unsigned
             else satU esize (v : Int)                  -- unsigned → unsigned
    r := r ||| ((e &&& mask esize) <<< (i*esize))
  return r

/-- VQDMULL: 2×signed widening multiply, saturate at 2·esize boundary → Q. -/
def vqdmull (esize s a b : Nat) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n] do
    let p : Int := 2 * toS esize (lane esize a i) * toS esize (lane esize b i)
    let sat := satS (2*esize) p
    r := r ||| ((sat &&& mask (2*esize)) <<< (i * 2*esize))
  return r
/-- VQDMLAL/VQDMLSL: VQDMULL + accumulate into Qd. -/
def vqdmlacc (esize s sub acc a b : Nat) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n] do
    let p : Int := 2 * toS esize (lane esize a i) * toS esize (lane esize b i)
    let sat := toS (2*esize) (satS (2*esize) p)
    let acc_v := toS (2*esize) (lane (2*esize) acc i)
    let res := satS (2*esize) (if sub == 1 then acc_v - sat else acc_v + sat)
    r := r ||| ((res &&& mask (2*esize)) <<< (i * 2*esize))
  return r

/-- VSHLL: widen each esize element of `a` (D) and shift left → Q. -/
def vshll (esize s sh a : Nat) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n] do
    let x : Int := if s == 1 then toS esize (lane esize a i) else lane esize a i
    r := r ||| (((x * (1 <<< sh)).emod (1 <<< (2*esize))).toNat <<< (i * 2*esize))
  return r

/-! ### pairwise (D-register: fold adjacent pairs, Dn→low half, Dm→high) -/

def pairwise (esize a b : Nat) (op : Nat → Nat → Nat) : Nat := Id.run do
  let n := 64 / esize; let mut r := 0
  for i in [0:n/2] do
    r := r ||| ((op (lane esize a (2*i)) (lane esize a (2*i+1)) &&& mask esize) <<< (i*esize))
    r := r ||| ((op (lane esize b (2*i)) (lane esize b (2*i+1)) &&& mask esize) <<< ((n/2+i)*esize))
  return r
def vpadd (esize a b : Nat) : Nat := pairwise esize a b (fun x y => x + y)
def vpmax (esize s a b : Nat) : Nat := pairwise esize a b (fun x y => if (if s==1 then toS esize x ≥ toS esize y else x ≥ y) then x else y)
def vpmin (esize s a b : Nat) : Nat := pairwise esize a b (fun x y => if (if s==1 then toS esize x ≤ toS esize y else x ≤ y) then x else y)
def vpaddF (a b : Nat) : Nat := pairwise 32 a b (fun x y => fpStd (Sei.Float.f32Add (flush F32 x) (flush F32 y)))
def vpmaxF (a b : Nat) : Nat := pairwise 32 a b (fun x y => fmaxLane (flush F32 x) (flush F32 y) true)
def vpminF (a b : Nat) : Nat := pairwise 32 a b (fun x y => fmaxLane (flush F32 x) (flush F32 y) false)

/-! ### doubling multiply / vector convert / compare-zero / table -/

def vqdmulh (w esize rnd a b : Nat) : Nat := zipLanes w esize a b (fun _ x y =>
  let p := 2 * toS esize x * toS esize y
  satS esize ((if rnd == 1 then p + (1 <<< (esize - 1)) else p).fdiv (1 <<< esize)))
def vcvtToInt (w signed a : Nat) : Nat := mapLanes w 32 a (fun _ x => Sei.Float.fToInt F32 (signed == 1) false (flush F32 x))
def vcvtFromInt (w signed a : Nat) : Nat := mapLanes w 32 a (fun _ x => flush F32 (if signed == 1 then Sei.Float.i32ToF F32 x else Sei.Float.u32ToF F32 x))

/-- Compare each lane to zero (signed int) → all-ones / 0 mask. cmp ∈ {gt,ge,eq,le,lt}. -/
def vcmpz (w esize a : Nat) (op : Nat) : Nat := mapLanes w esize a (fun _ x =>
  let v := toS esize x
  let t := if op == 0 then v > 0 else if op == 1 then v ≥ 0 else if op == 2 then v == 0 else if op == 3 then v ≤ 0 else v < 0
  cmpMask esize t)
/-- FP compare each lane to +0.0 → mask. -/
def vfcmpz (w a : Nat) (op : Nat) : Nat := mapLanes w 32 a (fun _ x =>
  let nz := Sei.Float.cmp F32 (flush F32 x) 0
  let t := if op == 0 then nz == 0b0010 else if op == 1 then nz == 0b0010 || nz == 0b0110
           else if op == 2 then nz == 0b0110 else if op == 3 then nz == 0b1000 || nz == 0b0110 else nz == 0b1000
  if t then 0xffffffff else 0)

/-- VPADDL: add adjacent element pairs, widening to 2·esize (same register width). -/
def vpaddl (w esize s a : Nat) : Nat := Id.run do
  let n := w / esize; let mut r := 0
  for i in [0:n/2] do
    let x : Int := if s == 1 then toS esize (lane esize a (2*i)) else lane esize a (2*i)
    let y : Int := if s == 1 then toS esize (lane esize a (2*i+1)) else lane esize a (2*i+1)
    r := r ||| (((x + y).emod (1 <<< (2*esize))).toNat <<< (i * 2*esize))
  return r
/-- VPADAL: VPADDL accumulated into the existing wider destination. -/
def vpadal (w esize s d a : Nat) : Nat := Id.run do
  let n := w / esize; let mut r := 0
  for i in [0:n/2] do
    let x : Int := if s == 1 then toS esize (lane esize a (2*i)) else lane esize a (2*i)
    let y : Int := if s == 1 then toS esize (lane esize a (2*i+1)) else lane esize a (2*i+1)
    r := r ||| (((lane (2*esize) d i + x + y).emod (1 <<< (2*esize))).toNat <<< (i * 2*esize))
  return r

/-- VTBL/VTBX: byte table lookup. `table` is the (len+1)·8-byte register block. -/
def vtbl (len d m table : Nat) (ext : Bool) : Nat := Id.run do
  let tbytes := (len + 1) * 8; let mut r := 0
  for i in [0:8] do
    let idx := lane 8 m i
    let v := if idx < tbytes then lane 8 table idx else (if ext then lane 8 d i else 0)
    r := r ||| (v <<< (i*8))
  return r

/-! ### P10 load/store de-interleaving (VLDn/VSTn) -/

/-- De-interleave: register `reg` of an n-way structure load collects every n-th
    `esize` element of the contiguous memory value `mv`. -/
def deint (n esize mv reg : Nat) : Nat := Id.run do
  let lanes := 64 / esize; let mut r := 0
  for i in [0:lanes] do r := r ||| (lane esize mv (i*n + reg) <<< (i*esize))
  return r
/-- Interleave n register values into the contiguous memory layout for VSTn. -/
def intl (n esize : Nat) (regs : Array Nat) : Nat := Id.run do
  let lanes := 64 / esize; let mut r := 0
  for reg in [0:n] do
    for i in [0:lanes] do
      r := r ||| (lane esize (regs.getD reg 0) i <<< ((i*n + reg) * esize))
  return r

/-! ### P8 permute / count / reverse (two-register misc) -/

def popc (v : Nat) : Nat := Id.run do
  let mut n := 0; let mut x := v
  for _ in [0:64] do
    n := n + (x &&& 1)
    x := x >>> 1
  return n

/-- Reverse the order of `esize`-elements within each `region`-bit group. -/
def vrev (w region esize x : Nat) : Nat := Id.run do
  let groups := w / region; let per := region / esize
  let mut r := 0
  for g in [0:groups] do
    for i in [0:per] do
      r := r ||| (lane esize (x >>> (g * region)) i <<< (g * region + (per - 1 - i) * esize))
  return r

def vclz (w esize x : Nat) : Nat := mapLanes w esize x (fun _ v => esize - Sei.Float.bitlen v)
def vcls (w esize x : Nat) : Nat := mapLanes w esize x (fun _ v =>
  let t := if (v >>> (esize - 1)) &&& 1 == 1 then (mask esize) ^^^ v else v
  esize - Sei.Float.bitlen t - 1)
def vcnt (w x : Nat) : Nat := mapLanes w 8 x (fun _ v => popc v)
def vnegI (w esize x : Nat) : Nat := mapLanes w esize x (fun _ v => (1 <<< esize) - v)
def vabsI (w esize x : Nat) : Nat := mapLanes w esize x (fun _ v => (toS esize v).natAbs)
def vqabsI (w esize x : Nat) : Nat := mapLanes w esize x (fun _ v => satS esize (toS esize v).natAbs)
def vqnegI (w esize x : Nat) : Nat := mapLanes w esize x (fun _ v => satS esize (-(toS esize v)))

/-- VTRN: transpose element pairs across `d`,`m` → (newDd, newDm). -/
def vtrn (w esize d m : Nat) : Nat × Nat := Id.run do
  let n := w / esize; let mut rd := 0; let mut rm := 0
  for i in [0:n] do
    let srcd := if i % 2 == 0 then lane esize d i else lane esize m (i - 1)
    let srcm := if i % 2 == 0 then lane esize d (i + 1) else lane esize m i
    rd := rd ||| (srcd <<< (i*esize))
    rm := rm ||| (srcm <<< (i*esize))
  return (rd, rm)
/-- VZIP: interleave → first n elements of [d∥m interleaved] to Dd, next n to Dm. -/
def vzip (w esize d m : Nat) : Nat × Nat := Id.run do
  let n := w / esize; let mut rd := 0; let mut rm := 0
  for i in [0:n] do
    let src := if i % 2 == 0 then lane esize d (i/2) else lane esize m (i/2)
    rd := rd ||| (src <<< (i*esize))
    let src2 := if i % 2 == 0 then lane esize d (n/2 + i/2) else lane esize m (n/2 + i/2)
    rm := rm ||| (src2 <<< (i*esize))
  return (rd, rm)
/-- VUZP: de-interleave [d∥m] → evens to Dd, odds to Dm. -/
def vuzp (w esize d m : Nat) : Nat × Nat := Id.run do
  let n := w / esize; let mut rd := 0; let mut rm := 0
  for i in [0:n] do
    let evi := 2*i; let odi := 2*i + 1
    let ev := if evi < n then lane esize d evi else lane esize m (evi - n)
    let od := if odi < n then lane esize d odi else lane esize m (odi - n)
    rd := rd ||| (ev <<< (i*esize)); rm := rm ||| (od <<< (i*esize))
  return (rd, rm)

/-! ### P2 immediate (AdvSIMDExpandImm) -/

def rep (chunk count val : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:count] do r := r ||| ((val &&& ((1 <<< chunk) - 1)) <<< (i * chunk))
  return r

/-- AdvSIMDExpandImm → the 64-bit pattern (Q replicates it). `op`/`cmode` per ARM. -/
def advExpand (op cmode imm8 : Nat) : Nat :=
  let c1 := cmode >>> 1            -- cmode<3:1>
  let c0 := cmode &&& 1            -- cmode<0>
  if c1 == 0b000 then rep 32 2 imm8
  else if c1 == 0b001 then rep 32 2 (imm8 <<< 8)
  else if c1 == 0b010 then rep 32 2 (imm8 <<< 16)
  else if c1 == 0b011 then rep 32 2 (imm8 <<< 24)
  else if c1 == 0b100 then rep 16 4 imm8
  else if c1 == 0b101 then rep 16 4 (imm8 <<< 8)
  else if c1 == 0b110 then
    if c0 == 0 then rep 32 2 ((imm8 <<< 8) ||| 0xff) else rep 32 2 ((imm8 <<< 16) ||| 0xffff)
  else                              -- cmode<3:1> == 111
    if c0 == 0 && op == 0 then rep 8 8 imm8                          -- VMOV.i8 ×8
    else if c0 == 0 && op == 1 then Id.run do                       -- VMOV.i64 bit-expand
      let mut v := 0
      for i in [0:8] do if (imm8 >>> i) &&& 1 == 1 then v := v ||| (0xff <<< (i * 8))
      return v
    else rep 32 2 (Sei.Float.expandImm Sei.Float.Fmt.f32 imm8)      -- cmode 1111 op0: VMOV.F32

/-- The immediate-form result: VMOV (op=0) / VMVN (op=1, ones'-complement) for the
    cmode<0>=0 patterns; the i64/F32 specials are never inverted. -/
def vmovImm (op cmode imm8 : Nat) : Nat :=
  let base := advExpand op cmode imm8
  let isSpecial := (cmode >>> 1 == 0b111)   -- i8/i64/F32: op already consumed, no invert
  if op == 1 && ¬ isSpecial then mask 64 ^^^ base else base

end Sei.Simd
