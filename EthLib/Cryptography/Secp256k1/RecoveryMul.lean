module

public import EthLib.Cryptography.Secp256k1.Curve
public import EthLib.Cryptography.Secp256k1.RecoveryField
public import EthLib.Cryptography.Secp256k1.RecoveryInverse

/-!
# Simultaneous scalar multiplication for public key recovery

Recovery multiplies a point whose coordinates come from the signature, and the fixed generator.

The endomorphism `(x, y) -> (beta x, y)` acts on this curve as multiplication by `lambda`.

Splitting the variable scalar in this basis gives two signed scalars below `2^128` in magnitude.

The generator scalar splits at bit 128, using `G` and `2^128 G`.

All four products share one chain with signed digits and at most 129 doublings.

The fixed generator uses fourteen-bit windows with tables of 4096 odd multiples.

For an affine variable point, a six-entry table shares one denominator.

The two signed components select a joint digit and can use one addition.

The fallback uses five-bit windows with eight odd multiples.

The variable scalar uses the endomorphism method of Gallant, Lambert and Vanstone.

The [Guide to Elliptic Curve Cryptography][guide] describes it in Algorithms 3.35, 3.74 and 3.77.

That book is by Hankerson, Menezes and Vanstone (Springer, 2004).

[guide]: <https://cacr.uwaterloo.ca/ecc/>
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

open Jacobian

namespace RecoveryMul

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

/-- Round `x / n` to the nearest integer. -/
def roundQuotient (x : Int) : Int := (x + (Fn.modulus : Int) / 2) / (Fn.modulus : Int)

/-- Split a scalar using the lattice with basis `(a, -b)` and `(a + b, a)`.

Both vectors give zero under `(u, v) -> u + lambda v` modulo `n`.

The second vector comes from the preceding Euclidean remainder.

Subtract the nearest basis multiples, as in Algorithm 3.74. -/
def splitScalar (k : Nat) : Int × Int :=
  let u := roundQuotient (basisA * k)
  let v := roundQuotient (basisB * k)
  (k - u * basisA - v * (basisA + basisB), u * basisB - v * basisA)

/-- Projective coordinates in the base field of secp256k1. -/
abbrev Coordinates := Coords Fp.RecoveryField.Element

/-- Move a point into the Montgomery representation used by the recovery chain. -/
@[inline] def toRecoveryCoords (p : Point) : Coordinates :=
  (Point.toJacobian p).toCoords.map Fp.RecoveryField.ofFin

/-- Normalize a result of the recovery chain. -/
@[inline] def ofRecoveryCoords (p : Coordinates) : Point :=
  Point.ofCoords
    RecoveryInverse.invMontgomery
    Fp.RecoveryField.toFin p

/-- Double with `a = 0` using shifts for the small powers of two. -/
@[inline] def doubleScaled {F : Type} [Add F] [Sub F] [Mul F]
    (twice fourTimes eightTimes : F → F) (p : Coords F) : Coords F :=
  let xx := p.x * p.x
  let yy := p.y * p.y
  let xyy := p.x * yy
  let s := fourTimes xyy
  let l := twice xx + xx
  let t := l * l - twice s
  let y4 := yy * yy
  let yz := p.y * p.z
  ⟨t, l * (s - t) - eightTimes y4, twice yz⟩

/-- Double using `Z' = Y Z` and a slope numerator of `3 X^2 / 2`.

The [libsecp256k1 doubling formula][double] uses the same scaling.

Scaling the resulting X, Y and Z coordinates by 4, 8 and 2 gives `Coords.double 0`.

[double]: <https://github.com/bitcoin-core/secp256k1/blob/v0.6.0/src/group_impl.h#L395-L425>
-/
@[inline] def doubleCore (p : Coordinates) : Coordinates :=
  let xx := Fp.RecoveryField.square p.x
  let l := xx + Fp.RecoveryField.halve xx
  let yy := Fp.RecoveryField.square p.y
  let l2 := Fp.RecoveryField.square l
  let xyy := p.x * yy
  let x := l2 - (xyy + xyy)
  let z := p.y * p.z
  let y := Fp.RecoveryField.productSubSquare l (xyy - x) yy
  ⟨x, y, z⟩

/-- Double a point in the recovery field. -/
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
  scaleX (Fp.RecoveryField.ofFin beta) p

/-- Negate the affine y coordinate while keeping the same projective denominator. -/
@[inline] def negate {F : Type} [OfNat F 0] [Sub F] (p : Coords F) : Coords F :=
  ⟨p.x, 0 - p.y, p.z⟩

/-- Add a point when the square and cube of the second denominator are available. -/
@[noinline] def addCached (p q : Coordinates) (qz2 qz3 : Fp.RecoveryField.Element) :
    Coordinates :=
  if p.z = 0 then q
  else if q.z = 0 then p
  else
    let zz := Fp.RecoveryField.square p.z
    let (u1, s1, z) := if q.z = 1 then (p.x, p.y, p.z) else
      (p.x * qz2, p.y * qz3, p.z * q.z)
    let h := q.x * zz - u1
    let r := q.y * p.z * zz - s1
    if h = 0 then
      if r = 0 then Coords.double 0 p else Coords.infinity
    else
      let hh := Fp.RecoveryField.square h
      let hhh := h * hh
      let v := u1 * hh
      let x := Fp.RecoveryField.square r - hhh - (v + v)
      ⟨x, r * (v - x) - s1 * hhh, z * h⟩

/-- Apply a fixed step to build eight consecutive odd multiples. -/
@[inline] def oddMultiplesBy (p : Coordinates) (next : Coordinates → Coordinates) :
    Vector Coordinates 8 :=
  let p3 := next p
  let p5 := next p3
  let p7 := next p5
  let p9 := next p7
  let p11 := next p9
  let p13 := next p11
  let p15 := next p13
  #v[p, p3, p5, p7, p9, p11, p13, p15]

/-- The odd multiples from `P` to `15 P`, indexed by `(multiple - 1) / 2`. -/
def oddMultiples (p : Coordinates) : Vector Coordinates 8 :=
  let d := Coords.double 0 p
  let z2 := Fp.RecoveryField.square d.z
  let z3 := z2 * d.z
  oddMultiplesBy p fun q => addCached q d z2 z3

/-- Normalize a form so its table entries can use mixed addition. -/
def normalize (p : Coordinates) : Coordinates :=
  toRecoveryCoords (ofRecoveryCoords p)

open Fp.RecoveryField (Element)

/-- Normalize a Jacobian point using the inverse of its Z coordinate. -/
@[inline] def affineWithInverse (inv : Element) (p : Coordinates) : Coordinates :=
  let inv2 := inv * inv
  ⟨p.x * inv2, p.y * (inv2 * inv), 1⟩

/-- Accumulate a product of denominators and distribute its inverse to the points.

See [Montgomery §10.3.1][batch] for batch inversion.

For a denominator `z` and suffix product `s`, their inverses are `s / (z * s)` and `z / (z * s)`.

[batch]: <https://www.ams.org/journals/mcom/1987-48-177/S0025-5718-1987-0866113-7/>
-/
def prepareBatch : (ps : List Coordinates) →
    Element × (Element → {out : List Coordinates // out.length = ps.length})
  | [] => (1, fun _ => ⟨[], rfl⟩)
  | p :: ps =>
    let suffix := prepareBatch ps
    (p.z * suffix.1, fun inv =>
      let out := suffix.2 (p.z * inv)
      ⟨affineWithInverse (inv * suffix.1) p :: out.val, congrArg Nat.succ out.property⟩)

/-- Invert the combined denominator in the recovery field. -/
@[inline] def batchInverse (z : Element) : Element :=
  RecoveryInverse.invMontgomery z

/-- Normalize the sequence with one inversion when the denominator product is nonzero. -/
def batchNormalize (ps : List Coordinates) : {out : List Coordinates // out.length = ps.length} :=
  let prep := prepareBatch ps
  if prep.1 = 0 then ⟨ps, rfl⟩ else prep.2 (batchInverse prep.1)

/-- List consecutive points spaced by the given step. -/
def oddSequence (step current : Coordinates) : (count : Nat) →
    {out : List Coordinates // out.length = count}
  | 0 => ⟨[], rfl⟩
  | n + 1 =>
    let rest := oddSequence step (Coords.add 0 current step) n
    ⟨current :: rest.val, congrArg Nat.succ rest.property⟩

/-- Consecutive odd multiples computed by repeatedly adding twice the input point. -/
def generatedMultiples (count : Nat) (p : Point) : Vector Coordinates count :=
  let first := toRecoveryCoords p
  let step := double first
  let raw := oddSequence step first count
  let table := batchNormalize raw.val
  ⟨table.val.toArray, List.size_toArray.trans (table.property.trans raw.property)⟩

/-- The odd multiples of a fixed point, through `127 P`. -/
def fixedMultiples (p : Point) : Vector Coordinates 64 :=
  Vector.ofFn fun i => toRecoveryCoords (Point.mulBits 7 (2 * i.val + 1) p)

/-- The generator's odd multiples. -/
def generatorTable : Vector Coordinates 64 := fixedMultiples Point.generator

/-- The generator multiplied by `2^128`. -/
def generatorHighPoint : Point := Point.mulBits 129 (2^128) Point.generator

/-- The Jacobian coordinates of `2^128 G`. -/
def generatorHigh : Coordinates := toRecoveryCoords generatorHighPoint

/-- The odd multiples of `2^128 G`. -/
def generatorHighTable : Vector Coordinates 64 := fixedMultiples generatorHighPoint

/-- The generator's odd multiples for twelve-bit windows. -/
def generatorTable12 : Vector Coordinates 1024 := generatedMultiples 1024 Point.generator

/-- The odd multiples of `2^128 G` for twelve-bit windows. -/
def generatorHighTable12 : Vector Coordinates 1024 := generatedMultiples 1024 generatorHighPoint

/-- The generator's odd multiples for fourteen-bit windows. -/
def generatorTable14 : Vector Coordinates 4096 := generatedMultiples 4096 Point.generator

/-- The odd multiples of `2^128 G` for fourteen-bit windows. -/
def generatorHighTable14 : Vector Coordinates 4096 := generatedMultiples 4096 generatorHighPoint

/-- Each width uses a signed digit from its own table. -/
inductive Window where
  /-- The width-five window of the variable point. -/
  | width5
  /-- The width-eight window of the generator. -/
  | width8
  /-- The width-twelve window of the recovery generator. -/
  | width12
  /-- The width-fourteen window of the recovery generator. -/
  | width14

/-- The number of positive odd digits for the window. -/
@[inline] def Window.entries : Window → Nat
  | .width5 => 8
  | .width8 => 64
  | .width12 => 1024
  | .width14 => 4096

/-- The digit's sign changes at this residue. -/
@[inline] def Window.pivot : Window → UInt64
  | .width5 => 16
  | .width8 => 128
  | .width12 => 2048
  | .width14 => 8192

/-- A mask for the low bits of the scalar that choose the digit. -/
@[inline] def Window.mask : Window → UInt64
  | .width5 => 31
  | .width8 => 255
  | .width12 => 4095
  | .width14 => 16383

/-- The index of an odd multiple and whether to subtract it. -/
abbrev Digit (n : Nat) := Fin n × Bool

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

/-- Shift both words right by one bit. -/
@[inline] def WordPair.half (w : WordPair) : WordPair :=
  ⟨(w.lo >>> 1) + (w.hi <<< 63), w.hi >>> 1⟩

/-- Round down to a multiple of the pivot. -/
@[inline] def WordPair.roundDown (w : WordPair) (pivot : UInt64) : WordPair :=
  ⟨w.lo - w.lo % pivot, w.hi⟩

/-- Add a word with carry. -/
@[inline] def WordPair.addWord (w : WordPair) (increment : UInt64) : WordPair :=
  let lo := w.lo + increment
  ⟨lo, w.hi + (if lo < increment then 1 else 0)⟩

/-- Read one signed digit from the two-word scalar. -/
@[inline] def recodeWords (window : Window) (w : WordPair) :
    WordPair × Option (Digit window.entries) :=
  let low := (w.lo &&& window.mask).toNat
  let half := w.half
  if he : low % 2 = 0 then (half, none)
  else
    have hlow : low < 4 * window.entries := by
      change (w.lo &&& window.mask).toNat < 4 * window.entries
      rw [UInt64.toNat_and]
      cases window with
      | width5 =>
        change w.lo.toNat &&& (2^5 - 1) < 2^5
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      | width8 =>
        change w.lo.toNat &&& (2^8 - 1) < 2^8
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      | width12 =>
        change w.lo.toNat &&& (2^12 - 1) < 2^12
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      | width14 =>
        change w.lo.toNat &&& (2^14 - 1) < 2^14
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
    let down := half.roundDown window.pivot
    if hr : low < 2 * window.entries then (down, some (⟨low / 2, by omega⟩, false))
    else
      (down.addWord window.pivot, some (⟨(4 * window.entries - low) / 2, by omega⟩, true))

/-- One scalar and its odd-multiple table. -/
structure Stream (n : Nat) where
  /-- The scalar bits still to read. -/
  scalar : WordPair
  /-- The odd multiples of the point for this scalar. -/
  table : Vector Coordinates n

/-- Add or subtract the selected odd multiple. -/
@[inline] def addDigit {n : Nat} (p : Coordinates) (table : Vector Coordinates n) :
    Option (Digit n) → Coordinates
  | none => p
  | some (i, negative) =>
    let q := table[i.val]
    Coords.add 0 p (if negative then negate q else q)

/-- Run the doubling chain with the given recoder for the fixed generator. -/
@[specialize window] def chainWordsFor (window : Window)
    (pt qt : Vector Coordinates 8) (rt st : Vector Coordinates window.entries) :
    Nat → WordPair → WordPair → WordPair → WordPair → Coordinates
  | 0, _, _, _, _ => Coords.infinity
  | fuel + 1, p, q, r, s =>
    let (a, da) := recodeWords .width5 p
    let (b, db) := recodeWords .width5 q
    let (c, dc) := recodeWords window r
    let (d, dd) := recodeWords window s
    let rest := chainWordsFor window pt qt rt st fuel a b c d
    let acc := double rest
    addDigit (addDigit (addDigit (addDigit acc pt da) qt db) rt dc) st dd

/-- Run the shared doubling chain with eight-bit generator windows. -/
@[inline] def chainWords (pt qt : Vector Coordinates 8) (rt st : Vector Coordinates 64) :
    Nat → WordPair → WordPair → WordPair → WordPair → Coordinates :=
  chainWordsFor .width8 pt qt rt st

/-- Run the chain with the selected window for the generator. -/
@[inline] def chainFor (window : Window) (fuel : Nat) (p q : Stream 8)
    (r s : Stream window.entries) : Coordinates :=
  chainWordsFor window p.table q.table r.table s.table
    fuel p.scalar q.scalar r.scalar s.scalar

/-- Run the doubling chain and read one signed digit per scalar at each step. -/
@[inline] def chain (fuel : Nat) (p q : Stream 8) (r s : Stream 64) : Coordinates :=
  chainWords p.table q.table r.table s.table fuel p.scalar q.scalar r.scalar s.scalar

/-- Negate the entries when a scalar from the lattice split is negative. -/
@[inline] def signedTable (scalar : Int) (table : Vector Coordinates 8) :
    Vector Coordinates 8 :=
  if scalar < 0 then table.map negate else table

/-- One odd multiple and the data shared by its two scalar streams. -/
structure Prepared where
  /-- The original X coordinate. -/
  x : Element
  /-- The X coordinate after applying the endomorphism. -/
  phiX : Element
  /-- The Y coordinate of both points. -/
  y : Element
  /-- The projective denominator of both points. -/
  z : Element
  /-- The square of the projective denominator. -/
  z2 : Element
  /-- The cube of the projective denominator. -/
  z3 : Element

/-- Compute the shared denominator powers once for each odd multiple. -/
@[inline] def prepare (p : Coordinates) : Prepared :=
  let z2 := p.z * p.z
  ⟨p.x, (endomorphism p).x, p.y, p.z, z2, z2 * p.z⟩

/-- Add a signed odd multiple using its cached denominator powers.

The field products use the same scaled coordinates as `Coords.add 0`.
-/
@[noinline] def addPrepared (p : Coordinates) (q : @& Prepared) (phi negative : Bool) :
    Coordinates :=
  let qx := if phi then q.phiX else q.x
  let qy := if negative then (0 : Element) - q.y else q.y
  if p.z = 0 then ⟨qx, qy, q.z⟩
  else if q.z = 0 then p
  else
    let z1z1 := p.z * p.z
    let (u1, s1, z1z2) := if q.z = 1 then (p.x, p.y, p.z) else
      (p.x * q.z2, p.y * q.z3, p.z * q.z)
    let u2 := qx * z1z1
    let s2 := qy * p.z * z1z1
    let h := u2 - u1
    let r := s2 - s1
    if h = 0 then
      if r = 0 then Coords.double 0 p else Coords.infinity
    else
      let hh := h * h
      let hhh := h * hh
      let v := u1 * hh
      let x3 := r * r - hhh - (v + v)
      ⟨x3, r * (v - x3) - s1 * hhh, z1z2 * h⟩

/-- Combine the scalar sign and digit sign before selecting the odd multiple. -/
@[inline] def addPreparedDigit (p : Coordinates) (table : Vector Prepared 8)
    (phi negative : Bool) : Option (Digit 8) → Coordinates
  | none => p
  | some (i, neg) => addPrepared p table[i.val] phi (negative != neg)

/-- Read both variable digits from one table during the shared doubling chain. -/
@[specialize window] def preparedChain (window : Window) (table : Vector Prepared 8)
    (pn qn : Bool) (rt st : Vector Coordinates window.entries) :
    Nat → WordPair → WordPair → WordPair → WordPair → Coordinates
  | 0, _, _, _, _ => Coords.infinity
  | fuel + 1, p, q, r, s =>
    let (a, da) := recodeWords .width5 p
    let (b, db) := recodeWords .width5 q
    let (c, dc) := recodeWords window r
    let (d, dd) := recodeWords window s
    let rest := preparedChain window table pn qn rt st fuel a b c d
    let acc := double rest
    let acc := addPreparedDigit acc table false pn da
    let acc := addPreparedDigit acc table true qn db
    addDigit (addDigit acc rt dc) st dd

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
  ⟨(magnitude >>> 1).toNat % window.entries, Nat.mod_lt _ (by cases window <;> decide)⟩

/-- Add the selected variable point after combining the scalar and digit signs. -/
@[inline] def addPackedPrepared (p : Coordinates) (table : Vector Prepared 8)
    (phi negative : Bool) (digit : UInt64) : Coordinates :=
  if digit == 0 then p else
    let i := packedIndex .width5 digit
    addPrepared p table[i.val] phi (negative != (digit >= Window.pivot .width5))

/-- Add a generator table entry using mixed addition when its Z coordinate is one. -/
@[noinline] def addGenerator (p : Coordinates) (q : @& Coordinates) (negative : Bool) :
    Coordinates :=
  let y := if negative then (0 : Element) - q.y else q.y
  if q.z = 1 then
    if p.z = 0 then ⟨q.x, y, q.z⟩ else
      let zz := Fp.RecoveryField.square p.z
      let h := q.x * zz - p.x
      let r := y * (p.z * zz) - p.y
      if h = 0 then
        if r = 0 then Coords.double 0 p else Coords.infinity
      else
        let hh := Fp.RecoveryField.square h
        let hhh := h * hh
        let v := p.x * hh
        let x := Fp.RecoveryField.square r - hhh - (v + v)
        ⟨x, r * (v - x) - p.y * hhh, p.z * h⟩
  else Coords.add 0 p ⟨q.x, y, q.z⟩

/-- Add the selected generator multiple with the digit's sign. -/
@[inline] def addPacked (p : Coordinates) (window : Window)
    (table : Vector Coordinates window.entries) (digit : UInt64) : Coordinates :=
  if digit == 0 then p else
    let i := packedIndex window digit
    let q := table[i.val]
    addGenerator p q (digit >= window.pivot)

/-- Combine adjacent doublings when the intervening digits are zero. -/
@[specialize window] def packedChain (window : Window) (table : Vector Prepared 8)
    (pn qn : Bool) (rt st : Vector Coordinates window.entries) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → UInt64 → UInt64 → Coordinates
  | 0, _, _, _, _, _, _, _, _ => Coords.infinity
  | fuel + 1, xa0, xa1, xb0, xb1, xc0, xc1, xd0, xd1 =>
    let ⟨al,ah,da⟩ := recodeRaw .width5 xa0 xa1
    let ⟨bl,bh,db⟩ := recodeRaw .width5 xb0 xb1
    let ⟨cl,ch,dc⟩ := recodeRaw window xc0 xc1
    let ⟨dl,dh,dd⟩ := recodeRaw window xd0 xd1
    let acc :=
      match fuel with
      | 0 => double Coords.infinity
      | next + 1 =>
        if ((al ||| bl ||| cl ||| dl) &&& 1) == 0 then
          let al' := (al >>> 1) + (ah <<< 63)
          let bl' := (bl >>> 1) + (bh <<< 63)
          let cl' := (cl >>> 1) + (ch <<< 63)
          let dl' := (dl >>> 1) + (dh <<< 63)
          doubleTwice (packedChain window table pn qn rt st next
            al' (ah >>> 1) bl' (bh >>> 1) cl' (ch >>> 1) dl' (dh >>> 1))
        else
          double (packedChain window table pn qn rt st (next + 1) al ah bl bh cl ch dl dh)
    let acc := addPackedPrepared acc table false pn da
    let acc := addPackedPrepared acc table true qn db
    addPacked (addPacked acc window rt dc) window st dd

/-- Split each scalar into the two words used by `packedChain`. -/
@[specialize window] def preparedChainPacked (window : Window) (table : Vector Prepared 8)
    (pn qn : Bool) (rt st : Vector Coordinates window.entries) (fuel : Nat)
    (p q r s : WordPair) : Coordinates :=
  packedChain window table pn qn rt st fuel p.lo p.hi q.lo q.hi r.lo r.hi s.lo s.hi

/-- Multiply the Jacobian denominator by the shared scale. -/
@[inline] def restoreZ (z : Element) (p : Coordinates) : Coordinates :=
  { p with z := p.z * z }

/-- Scale the numerators by the second and third powers of a factor. -/
@[noinline] def scaleNumerators (z : Element) (p : Coordinates) : Coordinates :=
  let z2 := Fp.RecoveryField.square z
  ⟨p.x * z2, p.y * z2 * z, p.z⟩

/-- Form the result once the differences of the weighted coordinates are known. -/
@[inline] def addFromDifferences (x y z h r : Element) : Coordinates :=
  let hh := Fp.RecoveryField.square h
  let r2 := Fp.RecoveryField.square r
  let v := x * hh
  let hhh := h * hh
  let z3 := z * h
  let x3 := r2 - hhh - (v + v)
  let y3 := Fp.RecoveryField.productDiff r (v - x3) y hhh
  ⟨x3, y3, z3⟩

/-- Check the four Montgomery residue words for zero. -/
@[inline] def zeroElement (x : Element) : Bool :=
  x.raw.w0 == 0 && x.raw.w1 == 0 && x.raw.w2 == 0 && x.raw.w3 == 0

/-- Add a variable multiple that has the same omitted denominator. -/
@[noinline] def addCommon (p : Coordinates) (qx qy : Element) : Coordinates :=
  if zeroElement p.z then ⟨qx, qy, 1⟩
  else
    let zz := Fp.RecoveryField.square p.z
    let qyz := qy * p.z
    let h := qx * zz - p.x
    let r := qyz * zz - p.y
    if zeroElement h then
      if zeroElement r then Coords.double 0 p else Coords.infinity
    else addFromDifferences p.x p.y p.z h r

/-- Add a fixed multiple with its original denominator. -/
@[noinline] def addFixed (z : Element) (p : Coordinates) (q : @& Coordinates) (negative : Bool) :
    Coordinates :=
  let y := if negative then (0 : Element) - q.y else q.y
  if zeroElement p.z then scaleNumerators z ⟨q.x, y, q.z⟩
  else if zeroElement q.z then p
  else
    let az := p.z * z
    let az2 := Fp.RecoveryField.square az
    let (u1, s1, z12) := if q.z = 1 then (p.x, p.y, p.z) else
      let qz2 := Fp.RecoveryField.square q.z
      (p.x * qz2, p.y * q.z * qz2, p.z * q.z)
    let az3 := az * az2
    let h := q.x * az2 - u1
    let r := y * az3 - s1
    if zeroElement h then
      if zeroElement r then Coords.double 0 p else Coords.infinity
    else addFromDifferences u1 s1 z12 h r

/-- Add equal-denominator forms and carry the new denominator into the second form. -/
@[noinline] def coAdd (p q : Coordinates) : Coordinates × Coordinates × Element :=
  let h := q.x - p.x
  let r := q.y - p.y
  let h2 := Fp.RecoveryField.square h
  let h3 := h * h2
  let vx := p.x * h2
  let wx := vx + h3
  let xx := Fp.RecoveryField.square r - wx - vx
  let yy := r * (vx - xx) - p.y * h3
  (⟨xx, yy, 1⟩, ⟨wx, q.y * h3, 1⟩, h)

/-- List odd multiples with a shared omitted denominator. -/
def collectOdd (p q : Coordinates) : (more : Nat) →
    {out : List Coordinates // out.length = more + 1} × Element
  | 0 => (⟨[p], rfl⟩, 1)
  | n + 1 =>
    let (p', q', h) := coAdd p q
    let (following, suffix) := collectOdd p' q' n
    let z := suffix * h
    (⟨scaleNumerators z p :: following.val, congrArg Nat.succ following.property⟩, z)

/-- Pair the variable table with the denominator shared by its eight entries. -/
def commonTable (p : Coordinates) : Vector Coordinates 8 × Element :=
  let d := double p
  let p' : Coordinates := scaleNumerators d.z p
  let out := collectOdd { p' with z := 1 } { d with z := 1 } 7
  (⟨out.1.val.toArray, List.size_toArray.trans out.1.property⟩, out.2 * d.z)

/-- Coordinates of a variable odd multiple and the image of its X coordinate. -/
structure CommonEntry where
  /-- The original point with its shared denominator omitted. -/
  point : Coordinates
  /-- The X coordinate with the endomorphism applied. -/
  phiX : Element

/-- Cache the X coordinate of the endomorphism image. -/
@[inline] def prepareCommon (q : Coordinates) : CommonEntry :=
  ⟨q, (endomorphism q).x⟩

/-- Add the selected multiple from the shared-denominator table. -/
@[inline] def addPackedCommon (p : Coordinates) (table : Vector CommonEntry 8)
    (phi negative : Bool) (digit : UInt64) : Coordinates :=
  if digit == 0 then p else
    let q := table[(packedIndex .width5 digit).val]
    let x := if phi then q.phiX else q.point.x
    let y := if negative != (digit >= Window.pivot .width5) then (0 : Element) - q.point.y
      else q.point.y
    addCommon p x y

/-- Add the selected fixed multiple in the original denominator. -/
@[inline] def addPackedFixed (z : Element) (p : Coordinates) (window : Window)
    (table : Vector Coordinates window.entries) (digit : UInt64) : Coordinates :=
  if digit == 0 then p else
    let q := table[(packedIndex window digit).val]
    addFixed z p q (digit >= window.pivot)

/-- Double a finite accumulator or return the canonical infinity coordinates. -/
@[inline] def doubleUnlessInfinity (step : Coordinates → Coordinates) (p : Coordinates) :
    Coordinates :=
  if p.z.raw.w0 == 0 && decide (p.z = 0) then Coords.infinity else step p

set_option maxHeartbeats 400000 in
/-- Combine up to three doublings when the intervening digits are zero. -/
@[specialize window] def packedCommonChain (window : Window) (z : Element)
    (table : Vector CommonEntry 8) (pn qn : Bool) (rt st : Vector Coordinates window.entries) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → UInt64 → UInt64 → Coordinates
  | 0, _, _, _, _, _, _, _, _ => Coords.infinity
  | fuel + 1, xa0, xa1, xb0, xb1, xc0, xc1, xd0, xd1 =>
    let ⟨al,ah,da⟩ := recodeRaw .width5 xa0 xa1
    let ⟨bl,bh,db⟩ := recodeRaw .width5 xb0 xb1
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
          doubleUnlessInfinity doubleThrice (packedCommonChain window z table pn qn rt st (next - 1)
            al' (ah >>> 2) bl' (bh >>> 2) cl' (ch >>> 2) dl' (dh >>> 2))
        else if ((al ||| bl ||| cl ||| dl) &&& 1) == 0 then
          let al' := (al >>> 1) + (ah <<< 63)
          let bl' := (bl >>> 1) + (bh <<< 63)
          let cl' := (cl >>> 1) + (ch <<< 63)
          let dl' := (dl >>> 1) + (dh <<< 63)
          doubleUnlessInfinity doubleTwice (packedCommonChain window z table pn qn rt st next
            al' (ah >>> 1) bl' (bh >>> 1) cl' (ch >>> 1) dl' (dh >>> 1))
        else
          doubleUnlessInfinity double
            (packedCommonChain window z table pn qn rt st (next + 1) al ah bl bh cl ch dl dh)
    let acc := addPackedCommon acc table false pn da
    let acc := addPackedCommon acc table true qn db
    addPackedFixed z (addPackedFixed z acc window rt dc) window st dd
termination_by fuel => fuel
decreasing_by all_goals omega

/-- Compute projective coordinates of `k P + l G`. -/
@[no_expose] def mulProjectivePrepared (k : Fn) (p : Coordinates) (l : Fn) : Coordinates :=
  let entries := (oddMultiples p).map prepare
  let (a, b) := splitScalar k.val
  preparedChainPacked .width14 entries (a < 0) (b < 0)
    generatorTable14 generatorHighTable14 129
    (WordPair.ofNat a.natAbs) (WordPair.ofNat b.natAbs)
    (WordPair.ofNat (l.val % 2^128)) (WordPair.ofNat (l.val / 2^128))

open Fp.RecoveryField (Raw ProductColumn wordProduct plus minus yes subtractBorrow mulHigh)

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
  scaleX (Fp.RecoveryField.ofFin (beta * beta)) p

/-- The three X coordinates obtained by applying the curve endomorphism. -/
structure JointEntry where
  x : Element
  phiX : Element
  phi2X : Element
  y : Element

@[inline] def JointEntry.ofCoords (p : Coordinates) : JointEntry :=
  let phiX := (endomorphism p).x
  ⟨p.x, phiX, 0 - (p.x + phiX), p.y⟩

/-- Build the joint table in an omitted common denominator. -/
def commonJointTable (p : Coordinates) : Vector JointEntry 6 × Element :=
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
    let y := if digit &&& 524288 == 0 then q.y else (0 : Element) - q.y
    addCommon p x y

set_option maxHeartbeats 400000 in
/-- Combine up to three doublings when the intervening digits are zero. -/
@[specialize window] def packedJointChain (window : Window) (z : Element)
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

/-- Use one denominator for the affine variable table. -/
@[no_expose] def mulProjectiveWordsIndependent (k : Raw) (p : Coordinates) (l : Raw) :
    Coordinates :=
  if p.z = 1 then
    let (entries, z) := commonTable p
    if z = 0 then mulProjectivePrepared (FnRecoveryWords.toFin k) p (FnRecoveryWords.toFin l) else
      let split := splitScalarWords k
      let a := split.1
      let b := split.2
      let out := packedCommonChain .width14 z (entries.map prepareCommon) a.2 b.2
        generatorTable14 generatorHighTable14 129 a.1.lo a.1.hi b.1.lo b.1.hi
        l.w0 l.w1 l.w2 l.w3
      restoreZ z out
  else mulProjectivePrepared (FnRecoveryWords.toFin k) p (FnRecoveryWords.toFin l)

/-- Multiply using scalar words that represent canonical residues modulo `n`. -/
@[no_expose] def mulProjectiveWords (k : Raw) (p : Coordinates) (l : Raw) : Coordinates :=
  if p.z = 1 then
    let split := splitScalarWords k
    let a := split.1
    let b := split.2
    if a.1.hi < 0x7fffffffffffffff && b.1.hi < 0x7fffffffffffffff then
      let (table, z) := commonJointTable p
      if z = 0 then mulProjectiveWordsIndependent k p l else
        let aw := if a.2 then a.1.neg else a.1
        let bw := if b.2 then b.1.neg else b.1
        let out := packedJointChain .width14 z table
          generatorTable14 generatorHighTable14 129 aw.lo aw.hi bw.lo bw.hi l.w0 l.w1 l.w2 l.w3
        restoreZ z out
    else mulProjectiveWordsIndependent k p l
  else mulProjectiveWordsIndependent k p l

@[no_expose] def mulProjective (k : Fn) (p : Coordinates) (l : Fn) : Coordinates :=
  mulProjectiveWords (FnRecoveryWords.fromFin k) p (FnRecoveryWords.fromFin l)

/-- Compute `k P + l G` from the field coordinates of `P`. -/
@[inline] def mulCoords (k : Fn) (p : Coordinates) (l : Fn) : Point :=
  ofRecoveryCoords (mulProjective k p l)

/-- Compute `k P + l G` in the recovery equation for a point `P` on the curve. -/
@[no_expose] def mul (k : Fn) (p : Point) (l : Fn) : Point :=
  mulCoords k (toRecoveryCoords p) l

end RecoveryMul

end EthLib.Cryptography.Secp256k1
