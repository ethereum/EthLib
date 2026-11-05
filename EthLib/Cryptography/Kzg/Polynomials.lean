module

public import EthLib.Base.Bytes
public import EthLib.Cryptography.Bls
public import EthLib.Cryptography.Kzg.Constants
public import EthLib.Cryptography.Kzg.BitReversal
public import EthLib.Cryptography.Kzg.Errors
public import EthLib.Cryptography.Kzg.Fft

/-!
# `Polynomials`

Polynomial helpers of KZG, which do not read the trusted setup.

A polynomial in evaluation form is an array of 4096 elements of `Fr`.

The length is checked where a polynomial enters an operation.

A polynomial in coefficient form is also an array of `Fr`, for the cells.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Base (Bytes32)
open EthLib.Cryptography.Bls (Fr)

open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal

/-! ## Type aliases -/

abbrev Polynomial      := Array Fr
abbrev PolynomialCoeff := Array Fr

/-- A blob: 4096 field elements of 32 bytes each. -/
abbrev Blob := Vector UInt8 BYTES_PER_BLOB

/-- 48 bytes, the size of a compressed `G1` point. -/
abbrev Bytes48 := Vector UInt8 48

/-- Read untyped bytes as a byte vector of length `n`.

Bytes of any other length are rejected with the error that `err` builds from that length. -/
def parseBytes (n : Nat) (err : Nat → KzgError) (b : ByteArray) :
    Except KzgError (Vector UInt8 n) :=
  if h : b.size = n then .ok ⟨b.data, h⟩ else .error (err b.size)

/-! ## Bytes <-> field element helpers -/

/-- Encode `n` as `len` big-endian bytes. -/
def intToBytesBE (n : Nat) (len : Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := len) fun i =>
    UInt8.ofNat ((n >>> ((len - 1 - i.val) * 8)) &&& 0xff)

/-- Big-endian accumulation of `bytes` onto `acc`. -/
def bytesBEToNatAux (acc : Nat) : List UInt8 → Nat
  | [] => acc
  | b :: rest => bytesBEToNatAux ((acc <<< 8) ||| b.toNat) rest

/-- Decode big-endian bytes as a `Nat`. -/
def bytesBEToNat (b : ByteArray) : Nat :=
  bytesBEToNatAux 0 b.data.toList

/-- Convert untrusted bytes to an element of the BLS scalar field.

It rejects an integer of at least the modulus. -/
def bytesToBlsField (b : Bytes32) : Except KzgError Fr :=
  match Fr.fromBytesBE ⟨b.toArray⟩ with
  | .ok f    => .ok f
  | .error _ => .error (.invalidFieldElement none)

/-- Encode `x` as 32 big-endian bytes. -/
@[inline] def blsFieldToBytes (x : Fr) : Bytes32 := ⟨x.toBytesBE.data, rfl⟩

/-- The 32 bytes of field element `i`, in bytes that hold `k` field elements in a row. -/
def fieldElementBytes {k : Nat} (bytes : Vector UInt8 (k * BYTES_PER_FIELD_ELEMENT))
    (i : Fin k) : Bytes32 :=
  Vector.ofFn fun j => bytes[i.val * BYTES_PER_FIELD_ELEMENT + j.val]'(by
    -- Field element `i < k` ends at byte `32 * (i + 1) ≤ 32 * k`.
    have hi := i.isLt
    have hj := j.isLt
    simp only [BYTES_PER_FIELD_ELEMENT] at *
    omega)

/-- Decode the `k` field elements of `bytes`, in order.

The first one that is not below `BLS_MODULUS` is rejected, with its index. -/
def bytesToBlsFields {k : Nat} (bytes : Vector UInt8 (k * BYTES_PER_FIELD_ELEMENT)) :
    Except KzgError (Array Fr) :=
  (Array.finRange k).mapM fun i =>
    (bytesToBlsField (fieldElementBytes bytes i)).mapError fun _ => .invalidFieldElement (some i)

/-- `[current, current * x, ..., current * x^(n-1)]`. -/
def computePowersAux (x current : Fr) : Nat → List Fr
  | 0 => []
  | n + 1 => current :: computePowersAux x (current * x) n

/-- Return `[x^0, x^1, ..., x^(n-1)]`. -/
def computePowers (x : Fr) (n : Nat) : Array Fr :=
  (computePowersAux x Fr.one n).toArray

/-- The `order`-th roots of unity in `Fr`: the powers of a primitive `order`-th root.

`order` must divide `r - 1`, for the modulus `r` of `Fr`.

Every caller passes 64, 128, 4096 or 8192, which divide `r - 1`.

For another order, the powers are those of an element that is not a primitive `order`-th root. -/
def computeRootsOfUnity (order : Nat) : Array Fr :=
  let exponent := (BLS_MODULUS - 1) / order
  let root :=
    (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY) ^ (Fr.ofNat exponent)
  computePowers root order

/-! ## Polynomials in coefficient form -/

/-- Sum the coefficient-form polynomials `a` and `b`. -/
def addPolynomialcoeff (a b : PolynomialCoeff) : PolynomialCoeff :=
  let (a, b) := if a.size ≥ b.size then (a, b) else (b, a)
  Array.ofFn (n := a.size) fun i =>
    let bi := if h : i.val < b.size then b[i.val] else Fr.zero
    a[i] + bi

/-- Multiply the coefficient-form polynomials `a` and `b`.

It rejects factors whose sizes sum to more than 8192.

So a product has at most 8191 coefficients. -/
def multiplyPolynomialcoeff (a b : PolynomialCoeff) :
    Except KzgError PolynomialCoeff := do
  if a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB then
    throw (.polynomialProductTooLong a.size b.size)
  return (Array.finRange a.size).foldl (init := #[Fr.zero]) fun r power =>
    let coef := a[power]
    let summand : PolynomialCoeff :=
      Array.replicate power.val Fr.zero ++ b.map (· * coef)
    addPolynomialcoeff r summand

/-- Long division of two coefficient-form polynomials.

Each step removes the leading coefficient of `a` and prepends one quotient coefficient.

It rejects an empty divisor.

It also rejects a divisor with a zero leading coefficient, when the loop would run. -/
def dividePolynomialcoeff (a b : PolynomialCoeff) :
    Except KzgError PolynomialCoeff := do
  -- An empty divisor is invalid.
  if hb : b.size = 0 then
    throw .zeroDivisorPolynomial
  -- A dividend shorter than the divisor has quotient zero.
  -- The specification's loop runs zero times and returns the empty list.
  else if hab : a.size < b.size then
    return #[]
  else
    let bpos := b.size - 1
    let lead := b[bpos]'(by omega)
    -- A zero leading coefficient would make every quotient step a division by zero.
    --
    -- Field division by zero returns 0 here, so it would fail silently.
    if lead.isZero then
      throw .zeroDivisorPolynomial
    -- The divisor's leading coefficient does not change, so its costly inverse is computed once.
    let bLeadInv := lead.inverse
    -- One quotient coefficient per step, while `apos - t ≥ bpos`.
    --
    -- The remainder keeps the length of `a`, so each step reads and writes inside it.
    let steps := a.size + 1 - max b.size 1
    let (_, o) := (Array.finRange steps).foldl
      (init := (a.toVector, (Array.empty : PolynomialCoeff)))
      fun (r, o) t =>
        have ht : t.val < a.size + 1 - b.size := by have := t.isLt; omega
        let apos := a.size - 1 - t.val
        let diff := apos - bpos
        let quot := r[apos]'(by omega) * bLeadInv
        let r := (Array.finRange b.size).foldl
          (fun r i =>
            have hi := i.isLt
            r.set (diff + i.val) (r[diff + i.val]'(by omega) - b[i] * quot) (by omega)) r
        (r, #[quot] ++ o)
    return o

/-- Lagrange interpolation: the polynomial of lowest degree with value `ys[i]` at `xs[i]`.

It comes in coefficient form, and its leading coefficients may be zero.

The points `xs` must be pairwise distinct.

The weights invert `xs[i] - xs[j]`, and inversion in `Fr` sends 0 to 0. -/
def interpolatePolynomialcoeff
    (xs ys : Array Fr) : Except KzgError PolynomialCoeff :=
  -- The interpolation nodes and values must come in equal numbers
  if h : xs.size ≠ ys.size then
    throw (.inputLengthMismatch "ys" xs.size ys.size)
  else
    (Array.finRange xs.size).foldlM (init := #[Fr.zero]) fun r i => do
      let summand ← (Array.finRange ys.size).foldlM (init := #[ys[i.val]'(by omega)])
        fun summand j =>
          if j.val ≠ i.val then
            let xj := xs[j.val]'(by omega)
            let weightAdj := (xs[i] - xj).inverse
            multiplyPolynomialcoeff summand #[(-weightAdj) * xj, weightAdj]
          else
            pure summand
      return addPolynomialcoeff r summand

/-- Compute the vanishing polynomial on `xs` (coefficient form). -/
def vanishingPolynomialcoeff (xs : Array Fr) : Except KzgError PolynomialCoeff :=
  xs.foldlM (init := #[Fr.one]) fun p x =>
    multiplyPolynomialcoeff p #[-x, Fr.one]

/-- Evaluate a coefficient-form polynomial at `z` by Horner's rule, from the last coefficient. -/
def evaluatePolynomialcoeff
    (polynomialCoeff : PolynomialCoeff) (z : Fr) : Fr :=
  polynomialCoeff.foldr (init := Fr.zero) fun c y => y * z + c

/-- Convert evaluation form to coefficient form via inverse FFT. -/
def polynomialEvalToCoeff (polynomial : Polynomial) : PolynomialCoeff :=
  let roots := computeRootsOfUnity FIELD_ELEMENTS_PER_BLOB
  fftField (bitReversalPermutation polynomial) roots (inv := true)


/-! ## Blob <-> Polynomial -/

/-- Convert a blob to a sequence of elements of `Fr`.

It rejects a 32-byte chunk of at least the modulus. -/
def blobToPolynomial (blob : Blob) : Except KzgError Polynomial :=
  bytesToBlsFields (k := FIELD_ELEMENTS_PER_BLOB) blob

/-! ## Evaluating a polynomial in evaluation form -/

/-- The bit-reversed `size`-th roots of unity. Recomputed on every call. -/
def rootsOfUnityBrp (size : Nat) : Array Fr :=
  bitReversalPermutation (computeRootsOfUnity size)

/-- Evaluation of an evaluation-form polynomial, over an explicit domain.

Value `i` of the polynomial is its value at point `i` of the domain.

The two arrays must have the same length, and the evaluation reads them as pairs. -/
def evaluatePolynomialInEvaluationFormAux
    (polynomial domain : Array Fr) (z : Fr) : Fr :=
  let width := polynomial.size
  let inverseWidth := (Fr.ofNat width).inverse
  let points := polynomial.zip domain
  match points.find? (·.2 == z) with
  -- Fast path: z is in the domain.
  | some (y, _) => y
  | none =>
    -- The barycentric formula, where `z` is not in the domain, so no `z - domain[i]` is zero.
    --
    -- One batch inversion gives every `1 / (z - D[i])`.
    let inverses := Fr.batchInverse (points.map fun (_, d) => z - d)
    let acc := (points.zip inverses).foldl (init := Fr.zero) fun acc ((y, d), inv) =>
      acc + y * d * inv
    let r := z ^ (Fr.ofNat width) - Fr.one
    acc * r * inverseWidth

/-- Evaluate an evaluation-form polynomial at `z`.

When `z` is a point `D[i]` of the domain, the value is entry `i`.

Otherwise it is the barycentric formula, for the domain size `W`:

`f(z) = (z^W − 1) / W · Σ_i (f(D[i]) · D[i]) / (z − D[i])`.

It rejects a polynomial that does not have exactly 4096 elements. -/
def evaluatePolynomialInEvaluationForm
    (polynomial : Polynomial) (z : Fr) : Except KzgError Fr :=
  if polynomial.size ≠ FIELD_ELEMENTS_PER_BLOB then
    .error (.badPolynomialSize polynomial.size)
  else
    .ok (evaluatePolynomialInEvaluationFormAux polynomial
      (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB) z)

end EthLib.Cryptography.Kzg
