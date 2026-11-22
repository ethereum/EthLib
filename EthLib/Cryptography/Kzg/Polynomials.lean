module

public import EthLib.Base.Bytes
public import EthLib.Cryptography.Bls
public import EthLib.Cryptography.Kzg.Constants
public import EthLib.Cryptography.Kzg.BitReversal
public import EthLib.Cryptography.Kzg.Errors
public import EthLib.Cryptography.Kzg.Fft
public import EthLib.Base.BigEndian

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

/-! ## Bytes <-> field element helpers -/

/-- Convert untrusted bytes to an element of the BLS scalar field.

It rejects an integer of at least the modulus. -/
def bytesToBlsField (b : Bytes32) : Except KzgError Fr :=
  -- The 32 bytes are read as a big-endian integer `x`.
  --
  -- It fails unless `x < r`, for the modulus `r` of `Fr`.
  match Fr.fromBytesBE b with
  | .ok f    => .ok f
  | .error _ => .error (.invalidFieldElement none)

/-- Encode `x` as 32 big-endian bytes. -/
@[inline] def blsFieldToBytes (x : Fr) : Bytes32 :=
  -- The integer `0 <= x < r`, as 32 big-endian bytes.
  ⟨x.toBytesBE.data, Montgomery.toBytesBE_size x⟩

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

The first one that is not below the modulus `r` of `Fr` is rejected, with its index. -/
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
  -- The powers start at `x^0 = 1`, and each next one is the previous times `x`, `n` in all.
  (computePowersAux x Fr.one n).toArray

/-- The `order`-th roots of unity in `Fr`: the powers of a primitive `order`-th root.

`order` must divide `r - 1`, for the modulus `r` of `Fr`.

Every caller passes 64, 128, 4096 or 8192, which divide `r - 1`.

For another order, the powers are those of an element that is not a primitive `order`-th root. -/
def computeRootsOfUnity (order : Nat) : Array Fr :=
  -- `order` must divide `r - 1`; that check is left out.
  --
  -- Every caller passes an order that divides `r - 1`.
  --
  -- The root is `w = 7^((r - 1) / order) mod r`, where 7 generates the group of units of `Fr`.
  let exponent := (BLS_MODULUS - 1) / order
  let root :=
    (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY) ^ (Fr.ofNat exponent)
  -- The roots are `w^0, w^1, ..., w^(order - 1)`.
  computePowers root order

@[simp] theorem length_computePowersAux (x current : Fr) (n : Nat) :
    (computePowersAux x current n).length = n := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih => simp [computePowersAux, ih]

@[simp] theorem size_computePowers (x : Fr) (n : Nat) :
    (computePowers x n).size = n := by
  simp [computePowers]

@[simp] theorem size_computeRootsOfUnity (order : Nat) :
    (computeRootsOfUnity order).size = order := by
  simp [computeRootsOfUnity]

/-! ## Polynomials in coefficient form -/

/-- Sum the coefficient-form polynomials `a` and `b`. -/
def addPolynomialcoeff (a b : PolynomialCoeff) : PolynomialCoeff :=
  -- The longer polynomial comes first, and `a` on a tie.
  let (a, b) := if a.size ≥ b.size then (a, b) else (b, a)
  -- Coefficient `i` of the sum is `a_i + b_i`, with `b_i = 0` beyond the length of `b`.
  Array.ofFn (n := a.size) fun i =>
    let bi := if h : i.val < b.size then b[i.val] else Fr.zero
    a[i] + bi

/-- Multiply the coefficient-form polynomials `a` and `b`.

It rejects factors whose sizes sum to more than 8192.

So a product has at most 8191 coefficients. -/
def multiplyPolynomialcoeff (a b : PolynomialCoeff) :
    Except KzgError PolynomialCoeff := do
  -- The sizes of `a` and `b` must sum to at most 8192.
  if a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB then
    throw (.polynomialProductTooLong a.size b.size)
  -- The product starts as the zero polynomial `[0]`, then gains one summand per coefficient of `a`.
  return (Array.finRange a.size).foldl (init := #[Fr.zero]) fun r power =>
    let coef := a[power]
    -- The summand of coefficient `a_k` is `a_k x^k b(x)`: `k` zeros, then `a_k b_j` for each `j`.
    let summand : PolynomialCoeff :=
      Array.replicate power.val Fr.zero ++ b.map (· * coef)
    -- The summand is added to the product.
    addPolynomialcoeff r summand

/-- Long division of two coefficient-form polynomials.

Each step removes the leading coefficient of `a` and prepends one quotient coefficient.

It rejects an empty divisor.

It also rejects a divisor with a zero leading coefficient, when the loop would run. -/
def dividePolynomialcoeff (a b : PolynomialCoeff) :
    Except KzgError PolynomialCoeff := do
  -- An empty divisor has no leading coefficient, so it is rejected.
  if hb : b.size = 0 then
    throw .zeroDivisorPolynomial
  -- When `a` is shorter than `b`, no step runs, and the quotient is empty.
  else if hab : a.size < b.size then
    return #[]
  else
    -- The leading coefficient of `b` has index `|b| - 1`.
    let bpos := b.size - 1
    let lead := b[bpos]'(by omega)
    -- EthLib's own check: a zero leading coefficient of `b` is rejected.
    --
    -- Every step would divide by zero, and division by zero in `Fr` returns 0: a silent failure.
    if lead.isZero then
      throw .zeroDivisorPolynomial
    -- The divisor's leading coefficient does not change, so its costly inverse is computed once.
    let bLeadInv := lead.inverse
    -- One quotient coefficient per step `t`, while `|a| - 1 - t >= |b| - 1`.
    --
    -- The remainder keeps the length of `a`, so each step reads and writes inside it.
    let steps := a.size + 1 - max b.size 1
    let (_, o) := (Array.finRange steps).foldl
      (init := (a.toVector, (Array.empty : PolynomialCoeff)))
      fun (r, o) t =>
        have ht : t.val < a.size + 1 - b.size := by have := t.isLt; omega
        -- Step `t` reads coefficient `m = |a| - 1 - t` of the remainder, and `d = m - (|b| - 1)`.
        let apos := a.size - 1 - t.val
        let diff := apos - bpos
        -- The quotient coefficient `q = a_m / b_(|b| - 1)`, with `a` the current remainder.
        let quot := r[apos]'(by omega) * bLeadInv
        -- `a_(d + i) := a_(d + i) - q b_i`, for `i` from `|b| - 1` down to 0.
        --
        -- The order of `i` does not matter: each step writes a distinct entry.
        let r := (Array.finRange b.size).foldl
          (fun r i =>
            have hi := i.isLt
            r.set (diff + i.val) (r[diff + i.val]'(by omega) - b[i] * quot) (by omega)) r
        -- The quotient coefficient goes in front of the earlier ones.
        (r, #[quot] ++ o)
    return o

/-- Lagrange interpolation: the polynomial of lowest degree with value `ys[i]` at `xs[i]`.

It comes in coefficient form, and its leading coefficients may be zero.

The points `xs` must be pairwise distinct.

The weights invert `xs[i] - xs[j]`, and inversion in `Fr` sends 0 to 0. -/
def interpolatePolynomialcoeff
    (xs ys : Array Fr) : Except KzgError PolynomialCoeff :=
  -- There must be as many values `ys` as points `xs`.
  if h : xs.size ≠ ys.size then
    throw (.inputLengthMismatch "ys" xs.size ys.size)
  else
    -- The result starts as the zero polynomial `[0]`, then gains one summand per point `i`.
    (Array.finRange xs.size).foldlM (init := #[Fr.zero]) fun r i => do
      -- The summand of point `i` is `ys[i] * prod_(j ≠ i) (x - xs[j]) / (xs[i] - xs[j])`.
      let summand ← (Array.finRange ys.size).foldlM (init := #[ys[i.val]'(by omega)])
        fun summand j =>
          if j.val ≠ i.val then
            let xj := xs[j.val]'(by omega)
            -- The weight `c = 1 / (xs[i] - xs[j])`.
            let weightAdj := (xs[i] - xj).inverse
            -- The summand is multiplied by `c x - c xs[j]`, the coefficients `-c xs[j]` and `c`.
            multiplyPolynomialcoeff summand #[(-weightAdj) * xj, weightAdj]
          else
            pure summand
      -- The summand is added to the result.
      return addPolynomialcoeff r summand

/-- Compute the vanishing polynomial on `xs` (coefficient form). -/
def vanishingPolynomialcoeff (xs : Array Fr) : Except KzgError PolynomialCoeff :=
  -- `p(x) = prod_k (x - xs[k])`, from `p = 1` times `x - xs[k]` for each point in order.
  xs.foldlM (init := #[Fr.one]) fun p x =>
    multiplyPolynomialcoeff p #[-x, Fr.one]

/-- Evaluate a coefficient-form polynomial at `z` by Horner's rule, from the last coefficient. -/
def evaluatePolynomialcoeff
    (polynomialCoeff : PolynomialCoeff) (z : Fr) : Fr :=
  -- From `y = 0`, `y := y z + c_k` for `k` from the last index down to 0.
  polynomialCoeff.foldr (init := Fr.zero) fun c y => y * z + c

/-- Convert evaluation form to coefficient form via inverse FFT. -/
def polynomialEvalToCoeff (polynomial : Polynomial) : PolynomialCoeff :=
  -- The 4096-th roots of unity, in their natural order.
  let roots := computeRootsOfUnity FIELD_ELEMENTS_PER_BLOB
  -- The values go from bit-reversed to natural order, then the inverse FFT gives the coefficients.
  fftField (bitReversalPermutation polynomial) roots (inv := true)


/-! ## Blob <-> Polynomial -/

/-- Convert a blob to a sequence of elements of `Fr`.

It rejects a 32-byte chunk of at least the modulus. -/
def blobToPolynomial (blob : Blob) : Except KzgError Polynomial :=
  -- Element `i` is the 32-byte slice `i` of the blob, read as an element of `Fr`, in order.
  bytesToBlsFields (k := FIELD_ELEMENTS_PER_BLOB) blob

/-! ## Evaluating a polynomial in evaluation form -/

/-- The bit-reversed `size`-th roots of unity. Recomputed on every call. -/
def rootsOfUnityBrp (size : Nat) : Array Fr :=
  bitReversalPermutation (computeRootsOfUnity size)

@[simp] theorem size_rootsOfUnityBrp (size : Nat) :
    (rootsOfUnityBrp size).size = size := by
  simp [rootsOfUnityBrp, bitReversalPermutation]

/-- Evaluation of an evaluation-form polynomial, over an explicit domain.

Value `i` of the polynomial is its value at point `i` of the domain.

The two arrays must have the same length, and the evaluation reads them as pairs. -/
def evaluatePolynomialInEvaluationFormAux
    (polynomial domain : Array Fr) (z : Fr) : Fr :=
  -- The caller checks the width and passes the roots of unity in bit-reversed order.
  --
  -- The width `W` is the number of values.
  let width := polynomial.size
  -- `1 / W` in `Fr`.
  let inverseWidth := (Fr.ofNat width).inverse
  let points := polynomial.zip domain
  -- If `z = D[i]` for a point of the domain, the value is entry `i`.
  match points.find? (·.2 == z) with
  | some (y, _) => y
  | none =>
    -- The barycentric formula, where `z` is not in the domain, so no `z - D[i]` is zero.
    --
    -- The denominators `z - D[i]`, all inverted with one batch inversion.
    let inverses := Fr.batchInverse (points.map fun (_, d) => z - d)
    -- The sum `S = sum_i f(D[i]) D[i] / (z - D[i])`.
    let acc := (points.zip inverses).foldl (init := Fr.zero) fun acc ((y, d), inv) =>
      acc + y * d * inv
    -- `z^W - 1`.
    let r := z ^ (Fr.ofNat width) - Fr.one
    -- `f(z) = S (z^W - 1) / W`.
    acc * r * inverseWidth

/-- Evaluate an evaluation-form polynomial at `z`.

When `z` is a point `D[i]` of the domain, the value is entry `i`.

Otherwise it is the barycentric formula, for the domain size `W`:

`f(z) = (z^W − 1) / W · Σ_i (f(D[i]) · D[i]) / (z − D[i])`.

It rejects a polynomial that does not have exactly 4096 elements. -/
def evaluatePolynomialInEvaluationForm
    (polynomial : Polynomial) (z : Fr) : Except KzgError Fr :=
  -- The width must be 4096 values.
  if polynomial.size ≠ FIELD_ELEMENTS_PER_BLOB then
    .error (.badPolynomialSize polynomial.size)
  -- The domain is the 4096-th roots of unity in bit-reversed order.
  else
    .ok (evaluatePolynomialInEvaluationFormAux polynomial
      (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB) z)

end EthLib.Cryptography.Kzg
