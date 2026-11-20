module

public import EthLib.Cryptography.Secp256k1.Curve
public import EthLib.Cryptography.Secp256k1.Montgomery
public import EthLib.Cryptography.Secp256k1.Inverse

/-!
# `Secp256k1.MulAdd`

`k P + l Q`, the double scalar multiplication of verification and of public key recovery.

Both take `Q = G`, the generator, and then a faster method applies.

The endomorphism `(x, y) -> (beta x, y)` acts on this curve as multiplication by `lambda`.

Splitting the variable scalar in this basis gives two signed scalars below `2^128` in magnitude.

The generator scalar splits at bit 128, using `G` and `2^128 G`.

All four products share one chain with signed digits and at most 129 doublings.

The fixed generator uses fourteen-bit windows with tables of 4096 odd multiples.

For an affine variable point, a six-entry table shares one denominator.

The two signed components select a joint digit and can use one addition.

Any other input takes the shared chain of doublings in Jacobian coordinates, which the
multiplication of two arbitrary points uses too.

The variable scalar uses the endomorphism method of Gallant, Lambert and Vanstone.

The [Guide to Elliptic Curve Cryptography][guide] describes it in Algorithms 3.35, 3.74 and 3.77.

That book is by Hankerson, Menezes and Vanstone (Springer, 2004).

[guide]: <https://cacr.uwaterloo.ca/ecc/>
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

open Jacobian

namespace MulAdd

/-- The cube root `2^((p - 1) / 3) mod p` in the base field. -/
def beta : Fp := 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

/-- The scalar by which the endomorphism acts on the generator.

It is `3^((n - 1) / 3) mod n`, the root that pairs with `beta`. -/
def lambda : Fn := 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

/-- The first coordinate of the first vector in the scalar lattice.

It is the first remainder below `sqrt(n)` in Euclid's algorithm on `n` and `lambda`. -/
def basisA : Int := 0x3086d221a7d46bcde86c90e49284eb15

/-- The coefficient of `lambda` for that remainder.

The first basis vector is `(basisA, -basisB)`. -/
def basisB : Int := 0xe4437ed6010e88286f547fa90abfe4c3

/-- Projective coordinates in the base field of secp256k1. -/
abbrev Coordinates := Coords Montgomery

/-- `2 P`, with `Z' = Y Z` and the slope numerator `3 X^2 / 2`.

It is formula (6) of Cohen, Miyaji and Ono for `a = 0`, scaled by `1/2` in `Z`.

So its `X`, `Y` and `Z` times 4, 8 and 2 are those of the shared doubling. -/
@[inline] def doubleCore (p : Coordinates) : Coordinates :=
  let xx := Montgomery.square p.x
  let l := xx + Montgomery.halve xx
  let yy := Montgomery.square p.y
  let l2 := Montgomery.square l
  let xyy := p.x * yy
  let x := l2 - (xyy + xyy)
  let z := p.y * p.z
  let y := Montgomery.productSubSquare l (xyy - x) yy
  ⟨x, y, z⟩

/-- `2 P`, kept out of line so the chain calls one copy. -/
@[noinline] def double (p : Coordinates) : Coordinates := doubleCore p

/-- Apply two doublings without allocating the intermediate point. -/
@[noinline] def doubleTwice (p : Coordinates) : Coordinates := doubleCore (doubleCore p)

/-- Apply three doublings without allocating intermediate points. -/
@[noinline] def doubleThrice (p : Coordinates) : Coordinates :=
  doubleCore (doubleCore (doubleCore p))

/-- Scale the X coordinate and copy the other two coordinates. -/
@[inline] def scaleX {F : Type} [Mul F] (factor : F) (p : Coords F) : Coords F :=
  { p with x := factor * p.x }

/-- Apply the curve endomorphism by changing only the X coordinate. -/
@[inline] def endomorphism (p : Coordinates) : Coordinates :=
  scaleX (Montgomery.ofFin beta) p

/-- Negate the affine y coordinate while keeping the same projective denominator. -/
@[inline] def negate {F : Type} [OfNat F 0] [Sub F] (p : Coords F) : Coords F :=
  ⟨p.x, 0 - p.y, p.z⟩

/-- Normalize a Jacobian point using the inverse of its Z coordinate. -/
@[inline] def affineWithInverse (inv : Montgomery) (p : Coordinates) : Coordinates :=
  let inv2 := inv * inv
  ⟨p.x * inv2, p.y * (inv2 * inv), 1⟩

/-- Accumulate a product of denominators and distribute its inverse to the points.

See [Montgomery §10.3.1][batch] for batch inversion.

For a denominator `z` and suffix product `s`, their inverses are `s / (z * s)` and `z / (z * s)`.

[batch]: <https://www.ams.org/journals/mcom/1987-48-177/S0025-5718-1987-0866113-7/>
-/
def prepareBatch : (ps : List Coordinates) →
    Montgomery × (Montgomery → {out : List Coordinates // out.length = ps.length})
  | [] => (1, fun _ => ⟨[], rfl⟩)
  | p :: ps =>
    let suffix := prepareBatch ps
    (p.z * suffix.1, fun inv =>
      let out := suffix.2 (p.z * inv)
      ⟨affineWithInverse (inv * suffix.1) p :: out.val, congrArg Nat.succ out.property⟩)

/-- Normalize the sequence with one inversion when the denominator product is nonzero. -/
def batchNormalize (ps : List Coordinates) : {out : List Coordinates // out.length = ps.length} :=
  let prep := prepareBatch ps
  if prep.1 = 0 then ⟨ps, rfl⟩ else prep.2 (Montgomery.inv prep.1)

/-- List consecutive points spaced by the given step. -/
def oddSequence (step current : Coordinates) : (count : Nat) →
    {out : List Coordinates // out.length = count}
  | 0 => ⟨[], rfl⟩
  | n + 1 =>
    let rest := oddSequence step (Coords.add 0 current step) n
    ⟨current :: rest.val, congrArg Nat.succ rest.property⟩

/-- Consecutive odd multiples computed by repeatedly adding twice the input point. -/
def generatedMultiples (count : Nat) (p : Point) : Vector Coordinates count :=
  let first := Point.toMontgomeryCoords p
  let step := double first
  let raw := oddSequence step first count
  let table := batchNormalize raw.val
  ⟨table.val.toArray, List.size_toArray.trans (table.property.trans raw.property)⟩

/-- The generator multiplied by `2^128`. -/
def generatorHighPoint : Point := Point.mulBits 129 (2^128) Point.generator

/-- The generator's odd multiples for fourteen-bit windows. -/
def generatorTable14 : Vector Coordinates 4096 := generatedMultiples 4096 Point.generator

/-- The odd multiples of `2^128 G` for fourteen-bit windows. -/
def generatorHighTable14 : Vector Coordinates 4096 := generatedMultiples 4096 generatorHighPoint

/-- The width of the signed digits that select entries of the generator tables. -/
inductive Window where
  /-- Fourteen bits, for tables of 4096 odd multiples. -/
  | width14

/-- The number of positive odd digits for the window. -/
@[inline] def Window.entries : Window → Nat
  | .width14 => 4096

/-- The digit's sign changes at this residue. -/
@[inline] def Window.pivot : Window → UInt64
  | .width14 => 8192

/-- A mask for the low bits of the scalar that choose the digit. -/
@[inline] def Window.mask : Window → UInt64
  | .width14 => 16383

/-- A scalar in two 64-bit words, least significant word first. -/
structure WordPair where
  /-- The least significant word. -/
  lo : UInt64
  /-- The most significant word. -/
  hi : UInt64

/-- The low 128 bits of a natural number. -/
def WordPair.ofNat (n : Nat) : WordPair := ⟨n.toUInt64, (n >>> 64).toUInt64⟩

/-- Read the scalar represented by the two words. -/
def WordPair.toNat (pair : WordPair) : Nat := pair.lo.toNat + pair.hi.toNat * 2^64

/-- The next scalar words and the current digit from one recoding step. -/
structure Recoded where
  /-- The low word of the next scalar. -/
  lo : UInt64
  /-- The high word of the next scalar. -/
  hi : UInt64
  /-- The masked low bits, with zero for an even scalar. -/
  digit : UInt64

/-- Recode one step and keep the digit in a machine word. -/
@[inline] def recodeRaw (window : Window) (lo hi : UInt64) : Recoded :=
  let digit := lo &&& window.mask
  let l := (lo >>> 1) + (hi <<< 63)
  let h := hi >>> 1
  if digit &&& 1 == 0 then ⟨l, h, 0⟩
  else
    let down := l - l % window.pivot
    if digit < window.pivot then ⟨down, h, digit⟩
    else
      let up := down + window.pivot
      ⟨up, h + (if up < window.pivot then 1 else 0), digit⟩

/-- Select the odd multiple for a nonzero digit. -/
@[inline] def packedIndex (window : Window) (digit : UInt64) : Fin window.entries :=
  let magnitude := if digit < window.pivot then digit else window.mask + 1 - digit
  ⟨(magnitude >>> 1).toNat % window.entries, Nat.mod_lt _ (by cases window; decide)⟩

/-- Multiply the Jacobian denominator by the shared scale. -/
@[inline] def restoreZ (z : Montgomery) (p : Coordinates) : Coordinates :=
  { p with z := p.z * z }

/-- Scale the numerators by the second and third powers of a factor. -/
@[noinline] def scaleNumerators (z : Montgomery) (p : Coordinates) : Coordinates :=
  let z2 := Montgomery.square z
  ⟨p.x * z2, p.y * z2 * z, p.z⟩

/-- Form the result once the differences of the weighted coordinates are known. -/
@[inline] def addFromDifferences (x y z h r : Montgomery) : Coordinates :=
  let hh := Montgomery.square h
  let r2 := Montgomery.square r
  let v := x * hh
  let hhh := h * hh
  let z3 := z * h
  let x3 := r2 - hhh - (v + v)
  let y3 := Montgomery.productDiff r (v - x3) y hhh
  ⟨x3, y3, z3⟩

/-- Check the four Montgomery residue words for zero. -/
@[inline] def zeroElement (x : Montgomery) : Bool :=
  x.raw.w0 == 0 && x.raw.w1 == 0 && x.raw.w2 == 0 && x.raw.w3 == 0

/-- Add a variable multiple that has the same omitted denominator. -/
@[noinline] def addCommon (p : Coordinates) (qx qy : Montgomery) : Coordinates :=
  if zeroElement p.z then ⟨qx, qy, 1⟩
  else
    let zz := Montgomery.square p.z
    let qyz := qy * p.z
    let h := qx * zz - p.x
    let r := qyz * zz - p.y
    if zeroElement h then
      if zeroElement r then Coords.double 0 p else Coords.infinity
    else addFromDifferences p.x p.y p.z h r

/-- Add a fixed multiple with its original denominator. -/
@[noinline] def addFixed (z : Montgomery) (p : Coordinates) (q : @& Coordinates) (negative : Bool) :
    Coordinates :=
  let y := if negative then (0 : Montgomery) - q.y else q.y
  if zeroElement p.z then scaleNumerators z ⟨q.x, y, q.z⟩
  else if zeroElement q.z then p
  else
    let az := p.z * z
    let az2 := Montgomery.square az
    let (u1, s1, z12) := if q.z = 1 then (p.x, p.y, p.z) else
      let qz2 := Montgomery.square q.z
      (p.x * qz2, p.y * q.z * qz2, p.z * q.z)
    let az3 := az * az2
    let h := q.x * az2 - u1
    let r := y * az3 - s1
    if zeroElement h then
      if zeroElement r then Coords.double 0 p else Coords.infinity
    else addFromDifferences u1 s1 z12 h r

/-- Add equal-denominator forms and carry the new denominator into the second form. -/
@[noinline] def coAdd (p q : Coordinates) : Coordinates × Coordinates × Montgomery :=
  let h := q.x - p.x
  let r := q.y - p.y
  let h2 := Montgomery.square h
  let h3 := h * h2
  let vx := p.x * h2
  let wx := vx + h3
  let xx := Montgomery.square r - wx - vx
  let yy := r * (vx - xx) - p.y * h3
  (⟨xx, yy, 1⟩, ⟨wx, q.y * h3, 1⟩, h)

/-- Add the selected fixed multiple in the original denominator. -/
@[inline] def addPackedFixed (z : Montgomery) (p : Coordinates) (window : Window)
    (table : Vector Coordinates window.entries) (digit : UInt64) : Coordinates :=
  if digit == 0 then p else
    let q := table[(packedIndex window digit).val]
    addFixed z p q (digit >= window.pivot)

/-- Double a finite accumulator or return the canonical infinity coordinates. -/
@[inline] def doubleUnlessInfinity (step : Coordinates → Coordinates) (p : Coordinates) :
    Coordinates :=
  if p.z.raw.w0 == 0 && decide (p.z = 0) then Coords.infinity else step p

open Montgomery (Raw ProductColumn wordProduct plus minus yes subtractBorrow mulHigh)

structure SplitConstants where
  a : WordPair
  b : WordPair
  sum : Raw
  aRecip : Raw
  bRecip : Raw

/-- The lattice basis and its rounded-down reciprocals scaled by `2^272`. -/
@[noinline] def splitConstants : SplitConstants :=
  ⟨⟨0xe86c90e49284eb15, 0x3086d221a7d46bcd⟩,
    ⟨0x6f547fa90abfe4c3, 0xe4437ed6010e8828⟩,
    ⟨0x57c1108d9d44cfd8, 0x14ca50f7a8e2f3f6, 0x1, 0x0⟩,
    ⟨0x90e49284eb153daa, 0xd221a7d46bcde86c, 0x3086, 0x0⟩,
    ⟨0x7fa90abfe4c42212, 0x7ed6010e88286f54, 0xe443, 0x0⟩⟩

/-- Compute the rounded reciprocal product from its upper columns. -/
@[inline] def approximateWeight (k c : Raw) : WordPair :=
  let zero : ProductColumn := ⟨0, 0, 0⟩
  let c3 := ((zero.add (wordProduct k.w1 c.w2)).add (wordProduct k.w2 c.w1)).add
    (wordProduct k.w3 c.w0)
  let c4 := (c3.next.add (wordProduct k.w2 c.w2)).add (wordProduct k.w3 c.w1)
  let c5 := c4.next.add (wordProduct k.w3 c.w2)
  let lo := (c4.lo >>> 16) ||| (c5.lo <<< 48)
  let round := (c4.lo >>> 15) &&& 1
  let hi := (c5.lo >>> 16) ||| (c5.mid <<< 48)
  let lo' := lo + round
  ⟨lo', hi + yes (lo' < lo)⟩

/-- The low words of a short product, through its sign bit. -/
@[inline] def lowProduct (a : WordPair) (b0 b1 b2 : UInt64) : Raw :=
  let w0 := wordProduct a.lo b0
  let c0 : ProductColumn := ⟨w0.hi, 0, 0⟩
  let w1 := (c0.add (wordProduct a.lo b1)).add (wordProduct a.hi b0)
  ⟨w0.lo, w1.lo, w1.mid + a.hi * b1 + a.lo * b2, 0⟩

/-- Subtract two low products modulo the signed representation. -/
@[inline] def lowSub (a b : Raw) : Raw :=
  let l := a.w0 - b.w0
  let c := yes (a.w0 < b.w0)
  let h := a.w1 - b.w1 - c
  let d := subtractBorrow a.w1 b.w1 c
  ⟨l, h, a.w2 - b.w2 - d, 0⟩

/-- Read the sign and magnitude from the low 129 bits. -/
@[inline] def signedMagnitude (a : Raw) : WordPair × Bool :=
  let neg := (a.w2 &&& 1) != 0
  if neg then (⟨0 - a.w0, 0 - a.w1 - yes (a.w0 != 0)⟩, true)
  else (⟨a.w0, a.w1⟩, false)

@[inline] def splitScalarWords (k : Raw) : (WordPair × Bool) × (WordPair × Bool) :=
  let c := splitConstants
  let u := approximateWeight k c.aRecip
  let v := approximateWeight k c.bRecip
  let ua := lowProduct u c.a.lo c.a.hi 0
  let vb := lowProduct v c.sum.w0 c.sum.w1 c.sum.w2
  let ub := lowProduct u c.b.lo c.b.hi 0
  let va := lowProduct v c.a.lo c.a.hi 0
  (signedMagnitude (lowSub (lowSub k ua) vb), signedMagnitude (lowSub ub va))

/-- The second power of the curve endomorphism. -/
@[inline] def endomorphismSquared (p : Coordinates) : Coordinates :=
  scaleX (Montgomery.ofFin (beta * beta)) p

/-- The three X coordinates obtained by applying the curve endomorphism. -/
structure JointEntry where
  x : Montgomery
  phiX : Montgomery
  phi2X : Montgomery
  y : Montgomery

@[inline] def JointEntry.ofCoords (p : Coordinates) : JointEntry :=
  let phiX := (endomorphism p).x
  ⟨p.x, phiX, 0 - (p.x + phiX), p.y⟩

/-- Build the joint table in an omitted common denominator. -/
def commonJointTable (p : Coordinates) : Vector JointEntry 6 × Montgomery :=
  let p0 : Coordinates := {p with z := 1}
  let q0 := negate (endomorphismSquared p0)
  let (p1, q1, h1) := coAdd p0 (q0)
  let (p2, q2, h2) := coAdd p1 (q1)
  let (p3, q3, h3) := coAdd p2 (endomorphismSquared q2)
  let (p4, q4, h4) := coAdd p3 (q3)
  let (p5, _, h5) := coAdd p4 (q4)
  let z5 := h5
  let z4 := z5 * h4
  let z3 := z4 * h3
  let z2 := z3 * h2
  let z1 := z2 * h1
  (#v[
    JointEntry.ofCoords (scaleNumerators z1 p0),
    JointEntry.ofCoords (scaleNumerators z2 p1),
    JointEntry.ofCoords (scaleNumerators z3 p2),
    JointEntry.ofCoords (scaleNumerators z4 p3),
    JointEntry.ofCoords (scaleNumerators z5 p4),
    JointEntry.ofCoords (p5)], z1)

/-- Signed pairs chosen by the low three bits of each coefficient.

The first two six-bit fields store the digits with a bias of 32.

Five bits select the table entry and two more select its endomorphism power.

Bit 19 gives the sign of the point.

The value zero selects two zero digits. -/
def jointDigits : Vector Nat 64 :=
  #v[
    0, 2081, 0, 18467, 0, 542749, 0, 526367,
    133216, 788577, 6242, 14435, 133216, 546909, 141406, 137311,
    0, 792737, 0, 10403, 0, 792737, 0, 145567,
    149728, 796897, 800994, 805091, 809188, 661473, 530398, 264159,
    0, 153889, 0, 526367, 0, 2081, 0, 677663,
    673632, 788577, 6242, 137311, 284508, 280413, 276318, 272223,
    0, 669601, 0, 268191, 0, 534429, 0, 268191,
    657376, 661473, 665570, 22499, 657376, 538589, 530398, 264159]

/-- Negate a scalar in two's complement. -/
@[inline] def WordPair.neg (w : WordPair) : WordPair :=
  ⟨0 - w.lo, 0 - w.hi - (w.lo != 0).toUInt64⟩

/-- Move to the next signed scalar bit after subtracting a small signed digit. -/
@[inline] def signedHalfAfter (lo hi digit : UInt64) : WordPair :=
  let l := lo - digit
  let h := hi + (digit >>> 63) - (decide (l > lo)).toUInt64
  ⟨(l >>> 1) + (h <<< 63), (h.toInt64 >>> 1).toUInt64⟩

/-- Shift the scalar without selecting a digit. -/
@[inline] def signedHalf (lo hi : UInt64) : WordPair :=
  ⟨(lo >>> 1) + (hi <<< 63), (hi.toInt64 >>> 1).toUInt64⟩

structure JointRecoded where
  a0 : UInt64
  a1 : UInt64
  b0 : UInt64
  b1 : UInt64
  digit : UInt64

@[inline] def recodeJoint (a0 a1 b0 b1 : UInt64) : JointRecoded :=
  if ((a0 ||| b0) &&& 1) == 0 then
    let a := signedHalf a0 a1
    let b := signedHalf b0 b1
    ⟨a.lo, a.hi, b.lo, b.hi, 0⟩
  else
    let index := ((a0 &&& (7 : UInt64)) + ((b0 &&& 7) <<< 3)).toNat % 64
    let digit := jointDigits[index].toUInt64
    let da := (digit &&& 63) - 32
    let db := ((digit >>> 6) &&& 63) - 32
    let a := signedHalfAfter a0 a1 da
    let b := signedHalfAfter b0 b1 db
    ⟨a.lo, a.hi, b.lo, b.hi, digit⟩

@[inline] def addPackedJoint (p : Coordinates) (table : Vector JointEntry 6) (digit : UInt64) :
    Coordinates :=
  if digit == 0 then p else
    let index := ((digit >>> 12) &&& 31).toNat % 6
    let q := table[index]
    let rotation := (digit >>> 17) &&& 3
    let x := if rotation == 0 then q.x else if rotation == 1 then q.phiX else q.phi2X
    let y := if digit &&& 524288 == 0 then q.y else (0 : Montgomery) - q.y
    addCommon p x y

/-- Combine up to three doublings when the intervening digits are zero. -/
@[specialize window] def packedJointChain (window : Window) (z : Montgomery)
    (table : Vector JointEntry 6) (rt st : Vector Coordinates window.entries) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → UInt64 → UInt64 → Coordinates
  | 0, _, _, _, _, _, _, _, _ => Coords.infinity
  | fuel + 1, xa0, xa1, xb0, xb1, xc0, xc1, xd0, xd1 =>
    let ⟨al,ah,bl,bh,dv⟩ := recodeJoint xa0 xa1 xb0 xb1
    let ⟨cl,ch,dc⟩ := recodeRaw window xc0 xc1
    let ⟨dl,dh,dd⟩ := recodeRaw window xd0 xd1
    let acc :=
      match fuel with
      | 0 => Coords.infinity
      | next + 1 =>
        if decide (0 < next) && ((al ||| bl ||| cl ||| dl) &&& 3) == 0 then
          let al' := (al >>> 2) + (ah <<< 62)
          let bl' := (bl >>> 2) + (bh <<< 62)
          let cl' := (cl >>> 2) + (ch <<< 62)
          let dl' := (dl >>> 2) + (dh <<< 62)
          doubleUnlessInfinity doubleThrice (packedJointChain window z table rt st (next - 1)
            al' (ah.toInt64 >>> 2).toUInt64 bl' (bh.toInt64 >>> 2).toUInt64
            cl' (ch >>> 2) dl' (dh >>> 2))
        else if ((al ||| bl ||| cl ||| dl) &&& 1) == 0 then
          let al' := (al >>> 1) + (ah <<< 63)
          let bl' := (bl >>> 1) + (bh <<< 63)
          let cl' := (cl >>> 1) + (ch <<< 63)
          let dl' := (dl >>> 1) + (dh <<< 63)
          doubleUnlessInfinity doubleTwice (packedJointChain window z table rt st next
            al' (ah.toInt64 >>> 1).toUInt64 bl' (bh.toInt64 >>> 1).toUInt64
            cl' (ch >>> 1) dl' (dh >>> 1))
        else
          doubleUnlessInfinity double
            (packedJointChain window z table rt st (next + 1) al ah bl bh cl ch dl dh)
    let acc := addPackedJoint acc table dv
    addPackedFixed z (addPackedFixed z acc window rt dc) window st dd
termination_by fuel => fuel
decreasing_by all_goals omega

/-- `k P + l G` in Jacobian form, for a form `P` of a point on the curve.

An affine form takes the joint chain.

Any other form, and the rare case where a table denominator vanishes, take the shared chain of
doublings instead. -/
@[no_expose] def mulProjective (k : Fn) (p : Coordinates) (l : Fn) : Coordinates :=
  let fallback := fun () =>
    Coords.mulAdd 0 256 k.val p l.val (Point.toMontgomeryCoords .generator)
  if p.z = 1 then
    let lw := Montgomery.rawOfNat l.val
    let split := splitScalarWords (Montgomery.rawOfNat k.val)
    let a := split.1
    let b := split.2
    if a.1.hi < 0x7fffffffffffffff && b.1.hi < 0x7fffffffffffffff then
      let (table, z) := commonJointTable p
      if z = 0 then fallback () else
        let aw := if a.2 then a.1.neg else a.1
        let bw := if b.2 then b.1.neg else b.1
        let out := packedJointChain .width14 z table generatorTable14 generatorHighTable14 129
          aw.lo aw.hi bw.lo bw.hi lw.w0 lw.w1 lw.w2 lw.w3
        restoreZ z out
    else fallback ()
  else fallback ()

/-- `k P + l G`, for a point `P` on the curve. -/
@[no_expose] def mul (k : Fn) (p : Point) (l : Fn) : Point :=
  Point.ofMontgomeryCoords (mulProjective k (Point.toMontgomeryCoords p) l)

end MulAdd

namespace Point

/-- `k P + l Q`, for scalars mod `n`.

When one point is the generator and the other lies on the curve, the joint chain above computes
it.

Otherwise one chain of doublings serves both scalars, in Jacobian coordinates.

On points of the curve it is the sum of the two products. -/
def mulAdd (k : Fn) (p : Point) (l : Fn) (q : Point) : Point :=
  if q = generator ∧ p.isOnCurve = true then MulAdd.mul k p l
  else if p = generator ∧ q.isOnCurve = true then MulAdd.mul l q k
  else
    ofMontgomeryCoords
      (Jacobian.Coords.mulAdd 0 256 k.val (toMontgomeryCoords p) l.val (toMontgomeryCoords q))

end Point

end EthLib.Cryptography.Secp256k1
