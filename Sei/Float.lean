/-
Sei.Float — a standalone IEEE-754 soft-float component (no ISA / Machine / Core
dependency; pure functions over bit patterns). Tracks Berkeley SoftFloat / QEMU
`fpu/softfloat.c` so results are bit-exact vs Unicorn. Consumed by ISA FP layers
(ARM VFP, later MIPS CP1 / RISC-V F). See docs/softfloat-component-plan.md.

Format-parametric (binary32 + binary64), round-to-nearest-even, no flush-to-zero:
add/sub/mul/div/sqrt, plus conversions (int↔float, f32↔f64).
-/
namespace Sei.Float

/-- An IEEE binary format: `sb` stored fraction bits, `eb` exponent bits. -/
structure Fmt where
  sb : Nat
  eb : Nat
def Fmt.f16 : Fmt := ⟨10, 5⟩
def Fmt.f32 : Fmt := ⟨23, 8⟩
def Fmt.f64 : Fmt := ⟨52, 11⟩
def Fmt.bias (f : Fmt) : Nat := (1 <<< (f.eb - 1)) - 1
def Fmt.maxe (f : Fmt) : Nat := (1 <<< f.eb) - 1
def Fmt.hid (f : Fmt) : Nat := 1 <<< f.sb
def Fmt.qbit (f : Fmt) : Nat := 1 <<< (f.sb - 1)
def Fmt.fracm (f : Fmt) : Nat := (1 <<< f.sb) - 1
def Fmt.signp (f : Fmt) : Nat := f.eb + f.sb           -- sign-bit position
def Fmt.dnan (f : Fmt) : Nat := (f.maxe <<< f.sb) ||| f.qbit

structure F where
  sign : Bool
  exp : Nat
  frac : Nat
def dec (f : Fmt) (x : Nat) : F := ⟨(x >>> f.signp) &&& 1 == 1, (x >>> f.sb) &&& f.maxe, x &&& f.fracm⟩
def F.isNaN (f : Fmt) (a : F) : Bool := a.exp == f.maxe && a.frac != 0
def F.isSNaN (f : Fmt) (a : F) : Bool := a.isNaN f && (a.frac &&& f.qbit) == 0
def F.isInf (f : Fmt) (a : F) : Bool := a.exp == f.maxe && a.frac == 0
def F.isZero (a : F) : Bool := a.exp == 0 && a.frac == 0
def enc (f : Fmt) (sign : Bool) (exp frac : Nat) : Nat :=
  ((if sign then 1 else 0) <<< f.signp) ||| ((exp &&& f.maxe) <<< f.sb) ||| (frac &&& f.fracm)

/-- Shift right by `n`, OR-ing any dropped 1-bits into the sticky (bit 0). -/
def srStky (x n : Nat) : Nat :=
  if n == 0 then x else (x >>> n) ||| (if x &&& ((1 <<< n) - 1) != 0 then 1 else 0)

/-- Number of significant bits (⌊log2⌋+1); 0 for 0. -/
def bitlen (n : Nat) : Nat := if n == 0 then 0 else Nat.log2 n + 1

/-- Round-pack a finite value (RNE). `m` is the working significand with the
    hidden bit ~position `sb+3` and guard/round/sticky in bits [2:0]. -/
def roundPack (f : Fmt) (sign : Bool) (E0 : Int) (m0 : Nat) : Nat := Id.run do
  let H := f.sb + 3
  let mut E := E0; let mut m := m0
  let bl := bitlen m                                                      -- fold MSB down to bit H
  if bl > H + 1 then let sh := bl - (H + 1); m := srStky m sh; E := E + sh
  for _ in [0:140] do if m != 0 && m < (1 <<< H) && E > 1 then m := m <<< 1; E := E - 1  -- normalize
  if E < 1 then m := srStky m (1 - E).toNat; E := 0                              -- subnormal
  let g := (m >>> 2) &&& 1; let r := (m >>> 1) &&& 1; let s := m &&& 1; let lsb := (m >>> 3) &&& 1
  let mut m24 := m >>> 3
  if g == 1 && (r == 1 || s == 1 || lsb == 1) then m24 := m24 + 1
  if m24 >= (1 <<< (f.sb + 1)) then m24 := m24 >>> 1; E := E + 1                 -- rounding carry
  if m24 < f.hid then enc f sign 0 (m24 &&& f.fracm)                            -- subnormal
  else
    let ef := if E < 1 then 1 else E.toNat
    if ef >= f.maxe then enc f sign f.maxe 0 else enc f sign ef (m24 &&& f.fracm)  -- normal / overflow→inf

/-- Working significand (<<3 for guard bits) + effective biased exponent. -/
def workSig (f : Fmt) (a : F) : Nat × Int :=
  ((if a.exp == 0 then a.frac else a.frac ||| f.hid) <<< 3, if a.exp == 0 then 1 else (a.exp : Int))

/-- Significand in [2^sb, 2^(sb+1)) + effective exponent, subnormals normalized. -/
def normSig (f : Fmt) (a : F) : Nat × Int :=
  if a.exp == 0 then Id.run do
    let mut s := a.frac; let mut e : Int := 1
    for _ in [0:60] do if s != 0 && s < f.hid then s := s <<< 1; e := e - 1
    return (s, e)
  else (a.frac ||| f.hid, (a.exp : Int))

def addSub (f : Fmt) (af bf : Nat) (sub : Bool) : Nat :=
  let a := dec f af; let b0 := dec f bf
  if a.isSNaN f then enc f a.sign f.maxe (a.frac ||| f.qbit)
  else if b0.isSNaN f then enc f b0.sign f.maxe (b0.frac ||| f.qbit)
  else if a.isNaN f then af
  else if b0.isNaN f then bf
  else
    let bf2 := if sub then bf ^^^ (1 <<< f.signp) else bf
    let b := dec f bf2
    if a.isInf f && b.isInf f then (if a.sign == b.sign then af else f.dnan)
    else if a.isInf f then af
    else if b.isInf f then bf2
    else if a.isZero && b.isZero then (if a.sign == b.sign then af else 0)
    else if a.isZero then bf2
    else if b.isZero then af
    else
      let (mA, eA) := workSig f a
      let (mB, eB) := workSig f b
      let (mA, mB, E) := if eA ≥ eB then (mA, srStky mB (eA - eB).toNat, eA)
                         else (srStky mA (eB - eA).toNat, mB, eB)
      if a.sign == b.sign then roundPack f a.sign E (mA + mB)
      else if mA == mB then 0
      else if mA > mB then roundPack f a.sign E (mA - mB)
      else roundPack f b.sign E (mB - mA)

def mul (f : Fmt) (af bf : Nat) : Nat :=
  let a := dec f af; let b := dec f bf
  let sign := a.sign != b.sign
  if a.isSNaN f then enc f a.sign f.maxe (a.frac ||| f.qbit)
  else if b.isSNaN f then enc f b.sign f.maxe (b.frac ||| f.qbit)
  else if a.isNaN f then af
  else if b.isNaN f then bf
  else if (a.isInf f && b.isZero) || (b.isInf f && a.isZero) then f.dnan
  else if a.isInf f || b.isInf f then enc f sign f.maxe 0
  else if a.isZero || b.isZero then enc f sign 0 0
  else
    let (sA, eA) := normSig f a
    let (sB, eB) := normSig f b
    roundPack f sign (eA + eB - (f.bias : Int) - ((f.sb : Int) - 3)) (sA * sB)

def div (f : Fmt) (af bf : Nat) : Nat :=
  let a := dec f af; let b := dec f bf
  let sign := a.sign != b.sign
  if a.isSNaN f then enc f a.sign f.maxe (a.frac ||| f.qbit)
  else if b.isSNaN f then enc f b.sign f.maxe (b.frac ||| f.qbit)
  else if a.isNaN f then af
  else if b.isNaN f then bf
  else if a.isInf f && b.isInf f then f.dnan
  else if a.isZero && b.isZero then f.dnan
  else if a.isInf f then enc f sign f.maxe 0
  else if b.isInf f then enc f sign 0 0
  else if b.isZero then enc f sign f.maxe 0
  else if a.isZero then enc f sign 0 0
  else
    let (sA, eA) := normSig f a
    let (sB, eB) := normSig f b
    let num := sA <<< (f.sb + 7)
    let m := (num / sB) ||| (if num % sB != 0 then 1 else 0)
    roundPack f sign (eA - eB + (f.bias : Int) - 4) m

/-- ⌊√n⌋ via integer Newton (bit-length initial guess so it converges for f64). -/
def isqrt (n : Nat) : Nat := Id.run do
  if n == 0 then return 0
  let mut bl := 0; let mut t := n
  for _ in [0:260] do if t > 0 then t := t >>> 1; bl := bl + 1
  let mut x := 1 <<< ((bl + 1) / 2)
  for _ in [0:200] do
    let nx := (x + n / x) / 2
    if nx < x then x := nx
  return x

def sqrt (f : Fmt) (af : Nat) : Nat :=
  let a := dec f af
  if a.isSNaN f then af ||| f.qbit
  else if a.isNaN f then af
  else if a.isZero then af
  else if a.sign then f.dnan
  else if a.isInf f then af
  else
    let (sA, eA) := normSig f a
    let e2 : Int := eA - (f.bias : Int) - (f.sb : Int)
    let (sA2, e2') := if e2 % 2 != 0 then (sA <<< 1, e2 - 1) else (sA, e2)
    let R := sA2 <<< (2 * f.sb)
    let q := isqrt R
    let m := q ||| (if q * q != R then 1 else 0)
    roundPack f false ((f.bias : Int) + 3 + e2' / 2) m

/-- Fused multiply-add: round(af·bf + cf) with a SINGLE rounding (the product is
    not rounded before the add). -/
def fma (f : Fmt) (af bf cf : Nat) : Nat :=
  let a := dec f af; let b := dec f bf; let c := dec f cf
  -- ARM FPMulAdd NaN handling: SNaN (addend, a, b) wins first; then 0×∞ is the
  -- default NaN EVEN over a QNaN addend (the FPMulAdd `typeA==QNaN && inf*0`
  -- override); then QNaN propagation in FPProcessNaNs3 order (addend, a, b).
  if c.isSNaN f then enc f c.sign f.maxe (c.frac ||| f.qbit)
  else if a.isSNaN f then enc f a.sign f.maxe (a.frac ||| f.qbit)
  else if b.isSNaN f then enc f b.sign f.maxe (b.frac ||| f.qbit)
  else if (a.isInf f && b.isZero) || (b.isInf f && a.isZero) then f.dnan
  else if c.isNaN f then cf
  else if a.isNaN f then af
  else if b.isNaN f then bf
  else
    let pSign := a.sign != b.sign
    if a.isInf f || b.isInf f then addSub f (enc f pSign f.maxe 0) cf false   -- (±inf) + c
    else if a.isZero || b.isZero then addSub f (enc f pSign 0 0) cf false     -- (±0) + c
    else if c.isInf f then cf                                                 -- finite + inf = inf
    else
      let (sA, eA) := normSig f a; let (sB, eB) := normSig f b
      let P := sA * sB
      let pe : Int := eA + eB - 2 * (f.bias : Int) - 2 * (f.sb : Int)         -- product = P·2^pe
      let eoff : Int := (f.bias : Int) + (f.sb : Int) + 3
      if c.isZero then roundPack f pSign (pe + eoff) P
      else
        let (sC, eC) := normSig f c
        let ce : Int := eC - (f.bias : Int) - (f.sb : Int)                    -- c = sC·2^ce
        let eRef := min pe ce
        let Pa := P <<< (pe - eRef).toNat
        let Ca := sC <<< (ce - eRef).toNat
        let E := eRef + eoff
        if pSign == c.sign then roundPack f pSign E (Pa + Ca)
        else if Pa == Ca then 0
        else if Pa > Ca then roundPack f pSign E (Pa - Ca)
        else roundPack f c.sign E (Ca - Pa)

/-- IEEE compare → 4-bit NZCV (unordered 0011, EQ 0110, LT 1000, GT 0010); never
    rounds. ±0 compare equal; any NaN ⇒ unordered. Format-generic. -/
def cmp (f : Fmt) (af bf : Nat) : Nat :=
  let a := dec f af; let b := dec f bf
  let mask := (1 <<< (f.signp + 1)) - 1
  let key (x : Nat) : Nat := if (x >>> f.signp) &&& 1 == 1 then mask - x else x ||| (1 <<< f.signp)
  if a.isNaN f || b.isNaN f then 0b0011
  else if (a.isZero && b.isZero) || af == bf then 0b0110
  else if key af < key bf then 0b1000
  else 0b0010

/-! ### conversions (VCVT) -/

/-- 32-bit integer magnitude → float (RNE). -/
def intToF (f : Fmt) (sign : Bool) (mag : Nat) : Nat :=
  if mag == 0 then enc f false 0 0
  else roundPack f sign ((f.bias : Int) + (f.sb : Int) + 3) mag
def u32ToF (f : Fmt) (x : Nat) : Nat := intToF f false (x &&& 0xffffffff)
def i32ToF (f : Fmt) (x : Nat) : Nat :=
  let x := x &&& 0xffffffff
  if x &&& 0x80000000 != 0 then intToF f true (0x100000000 - x) else intToF f false x

/-- float → 32-bit integer, saturating. `rne = true` rounds to nearest-even (the
    VCVTR form, FPSCR.RMode=RNE); `rne = false` rounds toward zero (VCVT). -/
def fToInt (f : Fmt) (signed rne : Bool) (af : Nat) : Nat :=
  let a := dec f af
  if a.isNaN f then 0
  else if a.isZero then 0
  else if a.isInf f then (if signed then (if a.sign then 0x80000000 else 0x7fffffff)
                          else (if a.sign then 0 else 0xffffffff))
  else
    let (sA, eA) := normSig f a
    let sh : Int := eA - (f.bias : Int) - (f.sb : Int)        -- value magnitude = sA · 2^sh
    let mag : Nat :=
      if sh ≥ 0 then sA <<< (min sh.toNat 40)                 -- integer, no fraction
      else
        let k := (-sh).toNat                                  -- k fractional bits
        let int := sA >>> k
        if ¬ rne then int                                     -- toward zero
        else                                                  -- nearest, ties to even
          let frac := sA &&& ((1 <<< k) - 1)
          let half := 1 <<< (k - 1)
          if frac > half || (frac == half && int &&& 1 == 1) then int + 1 else int
    if signed then
      if a.sign then (if mag ≥ 0x80000000 then 0x80000000 else (0x100000000 - mag) &&& 0xffffffff)
      else (if mag > 0x7fffffff then 0x7fffffff else mag)
    else
      if a.sign then 0 else (if mag > 0xffffffff then 0xffffffff else mag)

/-- fixed-point (low `sx` bits of `x`, `fbits` fraction bits) → float (RNE). -/
def fixedToF (f : Fmt) (signed : Bool) (sx fbits : Nat) (x : Nat) : Nat :=
  let mag := x &&& ((1 <<< sx) - 1)
  let (sign, m) := if signed && (mag >>> (sx - 1)) &&& 1 == 1 then (true, (1 <<< sx) - mag) else (false, mag)
  if m == 0 then enc f false 0 0
  else roundPack f sign ((f.bias : Int) + (f.sb : Int) + 3 - (fbits : Int)) m

/-- float → fixed-point (`sx`-bit, `fbits` fraction), round-toward-zero, saturating;
    the two's-complement result is sign/zero-extended to `width` bits. -/
def fToFixed (f : Fmt) (signed : Bool) (sx fbits width : Nat) (af : Nat) : Nat :=
  let a := dec f af
  let raw : Nat :=
    if a.isNaN f then 0
    else if a.isZero then 0
    else
      let (sA, eA) := normSig f a
      let sh : Int := eA - (f.bias : Int) - (f.sb : Int) + (fbits : Int)   -- value·2^fbits = sA·2^sh
      let mag : Nat := if a.isInf f then 1 <<< 70 else if sh ≥ 0 then sA <<< (min sh.toNat 70) else sA >>> (-sh).toNat
      let mask := (1 <<< sx) - 1
      if signed then
        let hi := (1 <<< (sx - 1)) - 1; let lo := 1 <<< (sx - 1)
        if a.sign then (if mag ≥ lo then lo else ((1 <<< sx) - mag) &&& mask)
        else (if mag > hi then hi else mag)
      else
        if a.sign then 0 else (if mag > mask then mask else mag)
  -- sign-extend (signed, negative) to the destination register width
  if signed && (raw >>> (sx - 1)) &&& 1 == 1 then raw ||| (((1 <<< width) - 1) - ((1 <<< sx) - 1)) else raw

/-- float → float (precision conversion); exact when widening, rounds when narrowing. -/
def fconvert (fsrc fdst : Fmt) (af : Nat) : Nat :=
  let a := dec fsrc af
  if a.isNaN fsrc then
    let pay := if fsrc.sb ≥ fdst.sb then a.frac >>> (fsrc.sb - fdst.sb) else a.frac <<< (fdst.sb - fsrc.sb)
    enc fdst a.sign fdst.maxe (fdst.qbit ||| (pay &&& fdst.fracm))
  else if a.isInf fsrc then enc fdst a.sign fdst.maxe 0
  else if a.isZero then enc fdst a.sign 0 0
  else
    let (sA, eA) := normSig fsrc a
    roundPack fdst a.sign (eA - (fsrc.bias : Int) - (fsrc.sb : Int) + (fdst.bias : Int) + (fdst.sb : Int) + 3) sA
def f32ToF64 (a : Nat) : Nat := fconvert Fmt.f32 Fmt.f64 a
def f64ToF32 (a : Nat) : Nat := fconvert Fmt.f64 Fmt.f32 a
def f16ToF32 (a : Nat) : Nat := fconvert Fmt.f16 Fmt.f32 a
def f32ToF16 (a : Nat) : Nat := fconvert Fmt.f32 Fmt.f16 a

/-- VFPExpandImm: the 8-bit VMOV-immediate → a float pattern (format-generic). -/
def expandImm (f : Fmt) (imm8 : Nat) : Nat :=
  let sign := (imm8 >>> 7) &&& 1
  let b6 := (imm8 >>> 6) &&& 1
  let expHi := (1 - b6) <<< (f.eb - 1)
  let expMid := (if b6 == 1 then (1 <<< (f.eb - 3)) - 1 else 0) <<< 2
  let exp := expHi ||| expMid ||| ((imm8 >>> 4) &&& 3)
  (sign <<< f.signp) ||| (exp <<< f.sb) ||| ((imm8 &&& 0xf) <<< (f.sb - 4))

/-- Flush a subnormal to a signed zero (Advanced SIMD Standard FP mode, FZ). -/
def flush (f : Fmt) (x : Nat) : Nat :=
  let a := dec f x
  if a.exp == 0 && a.frac != 0 then (if a.sign then 1 <<< f.signp else 0) else x

/-! ### binary32 / binary64 entry points -/
def f32Add (a b : Nat) : Nat := addSub Fmt.f32 a b false
def f32Sub (a b : Nat) : Nat := addSub Fmt.f32 a b true
def f32Mul (a b : Nat) : Nat := mul Fmt.f32 a b
def f32Div (a b : Nat) : Nat := div Fmt.f32 a b
def f32Sqrt (a : Nat) : Nat := sqrt Fmt.f32 a
def f64Add (a b : Nat) : Nat := addSub Fmt.f64 a b false
def f64Sub (a b : Nat) : Nat := addSub Fmt.f64 a b true
def f64Mul (a b : Nat) : Nat := mul Fmt.f64 a b
def f64Div (a b : Nat) : Nat := div Fmt.f64 a b
def f64Sqrt (a : Nat) : Nat := sqrt Fmt.f64 a

end Sei.Float
