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

The step comments of the evaluation form quote consensus-specs at `8a3df1d7`:
<https://github.com/ethereum/consensus-specs/blob/8a3df1d79d70000801407e33d660171be9cd06d1/specs/deneb/polynomial-commitments.md>
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
  -- bytes_to_bls_field: `field_element = int.from_bytes(b, KZG_ENDIANNESS)`.
  --
  -- `assert field_element < BLS_MODULUS`.
  match Fr.fromBytesBE b with
  | .ok f    => .ok f
  | .error _ => .error (.invalidFieldElement none)

/-- Encode `x` as 32 big-endian bytes. -/
@[inline] def blsFieldToBytes (x : Fr) : Bytes32 :=
  -- bls_field_to_bytes: `int.to_bytes(int(x), 32, KZG_ENDIANNESS)`.
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
  -- compute_powers: `current_power = BLSFieldElement(1)`, then `current_power * x`, `n` times.
  (computePowersAux x Fr.one n).toArray

/-- The `order`-th roots of unity in `Fr`: the powers of a primitive `order`-th root.

`order` must divide `r - 1`, for the modulus `r` of `Fr`.

Every caller passes 64, 128, 4096 or 8192, which divide `r - 1`.

For another order, the powers are those of an element that is not a primitive `order`-th root. -/
def computeRootsOfUnity (order : Nat) : Array Fr :=
  -- compute_roots_of_unity: `assert (BLS_MODULUS - 1) % int(order) == 0` is left out.
  --
  -- Every caller passes an order that divides `BLS_MODULUS - 1`.
  --
  -- `root_of_unity = pow(PRIMITIVE_ROOT_OF_UNITY, (BLS_MODULUS - 1) // int(order), BLS_MODULUS)`.
  let exponent := (BLS_MODULUS - 1) / order
  let root :=
    (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY) ^ (Fr.ofNat exponent)
  -- `return compute_powers(root_of_unity, order)`.
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

/-! ## Polynomials in coefficient form

The step comments of this section quote consensus-specs at `8a3df1d7`.

They quote its section "Polynomials in coefficient form", of the Fulu file:
<https://github.com/ethereum/consensus-specs/blob/8a3df1d79d70000801407e33d660171be9cd06d1/specs/fulu/polynomial-commitments-sampling.md#polynomials-in-coefficient-form>
-/

/-- Sum the coefficient-form polynomials `a` and `b`. -/
def addPolynomialcoeff (a b : PolynomialCoeff) : PolynomialCoeff :=
  -- add_polynomialcoeff: `a, b = (a, b) if len(a) >= len(b) else (b, a)`.
  let (a, b) := if a.size ≥ b.size then (a, b) else (b, a)
  -- `[a[i] + (b[i] if i < length_b else BLSFieldElement(0)) for i in range(length_a)]`.
  Array.ofFn (n := a.size) fun i =>
    let bi := if h : i.val < b.size then b[i.val] else Fr.zero
    a[i] + bi

/-- Multiply the coefficient-form polynomials `a` and `b`.

It rejects factors whose sizes sum to more than 8192.

So a product has at most 8191 coefficients. -/
def multiplyPolynomialcoeff (a b : PolynomialCoeff) :
    Except KzgError PolynomialCoeff := do
  -- multiply_polynomialcoeff: `assert len(a) + len(b) <= FIELD_ELEMENTS_PER_EXT_BLOB`.
  if a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB then
    throw (.polynomialProductTooLong a.size b.size)
  -- `r = PolynomialCoeff([BLSFieldElement(0)])`, then the loop over `power, coef`.
  return (Array.finRange a.size).foldl (init := #[Fr.zero]) fun r power =>
    let coef := a[power]
    -- `summand = [BLSFieldElement(0)] * power + [coef * x for x in b]`.
    let summand : PolynomialCoeff :=
      Array.replicate power.val Fr.zero ++ b.map (· * coef)
    -- `r = add_polynomialcoeff(r, summand)`.
    addPolynomialcoeff r summand

/-- Long division of two coefficient-form polynomials.

Each step removes the leading coefficient of `a` and prepends one quotient coefficient.

It rejects an empty divisor.

It also rejects a divisor with a zero leading coefficient, when the loop would run. -/
def dividePolynomialcoeff (a b : PolynomialCoeff) :
    Except KzgError PolynomialCoeff := do
  -- Not in divide_polynomialcoeff, which reads `b[bpos]` and fails on an empty divisor.
  if hb : b.size = 0 then
    throw .zeroDivisorPolynomial
  -- `while diff >= 0` runs zero times when `a` is shorter than `b`, so `o` stays empty.
  else if hab : a.size < b.size then
    return #[]
  else
    -- `bpos = len(b) - 1`.
    let bpos := b.size - 1
    let lead := b[bpos]'(by omega)
    -- Not in the source: a zero `b[bpos]` would make every `a[apos] / b[bpos]` divide by zero.
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
        -- `apos = len(a) - 1`, then `apos -= 1` and `diff -= 1` at each step.
        let apos := a.size - 1 - t.val
        let diff := apos - bpos
        -- `quot = a[apos] / b[bpos]`.
        let quot := r[apos]'(by omega) * bLeadInv
        -- `a[diff + i] = a[diff + i] - b[i] * quot`, for `i` from `bpos` down to 0.
        --
        -- The order of `i` does not matter: each step writes a distinct entry.
        let r := (Array.finRange b.size).foldl
          (fun r i =>
            have hi := i.isLt
            r.set (diff + i.val) (r[diff + i.val]'(by omega) - b[i] * quot) (by omega)) r
        -- `o.insert(0, quot)`.
        (r, #[quot] ++ o)
    return o

/-- Lagrange interpolation: the polynomial of lowest degree with value `ys[i]` at `xs[i]`.

It comes in coefficient form, and its leading coefficients may be zero.

The points `xs` must be pairwise distinct.

The weights invert `xs[i] - xs[j]`, and inversion in `Fr` sends 0 to 0. -/
def interpolatePolynomialcoeff
    (xs ys : Array Fr) : Except KzgError PolynomialCoeff :=
  -- interpolate_polynomialcoeff: `assert len(xs) == len(ys)`.
  if h : xs.size ≠ ys.size then
    throw (.inputLengthMismatch "ys" xs.size ys.size)
  else
    -- `r = PolynomialCoeff([BLSFieldElement(0)])`, then the loop over `i`.
    (Array.finRange xs.size).foldlM (init := #[Fr.zero]) fun r i => do
      -- `summand = PolynomialCoeff([ys[i]])`, then the loop over `j != i`.
      let summand ← (Array.finRange ys.size).foldlM (init := #[ys[i.val]'(by omega)])
        fun summand j =>
          if j.val ≠ i.val then
            let xj := xs[j.val]'(by omega)
            -- `weight_adjustment = (xs[i] - xs[j]).inverse()`.
            let weightAdj := (xs[i] - xj).inverse
            -- `summand = multiply_polynomialcoeff(summand, [-weight_adjustment * xs[j], ...])`.
            multiplyPolynomialcoeff summand #[(-weightAdj) * xj, weightAdj]
          else
            pure summand
      -- `r = add_polynomialcoeff(r, summand)`.
      return addPolynomialcoeff r summand

/-- Compute the vanishing polynomial on `xs` (coefficient form). -/
def vanishingPolynomialcoeff (xs : Array Fr) : Except KzgError PolynomialCoeff :=
  -- vanishing_polynomialcoeff: `p = [1]`, then `p = multiply_polynomialcoeff(p, [-x, 1])`.
  xs.foldlM (init := #[Fr.one]) fun p x =>
    multiplyPolynomialcoeff p #[-x, Fr.one]

/-- Evaluate a coefficient-form polynomial at `z` by Horner's rule, from the last coefficient. -/
def evaluatePolynomialcoeff
    (polynomialCoeff : PolynomialCoeff) (z : Fr) : Fr :=
  -- evaluate_polynomialcoeff: `y = 0`, then `y = y * z + coef` over `polynomial_coeff[::-1]`.
  polynomialCoeff.foldr (init := Fr.zero) fun c y => y * z + c

/-- Convert evaluation form to coefficient form via inverse FFT. -/
def polynomialEvalToCoeff (polynomial : Polynomial) : PolynomialCoeff :=
  -- polynomial_eval_to_coeff: `roots_of_unity = compute_roots_of_unity(FIELD_ELEMENTS_PER_BLOB)`.
  let roots := computeRootsOfUnity FIELD_ELEMENTS_PER_BLOB
  -- `fft_field(bit_reversal_permutation(polynomial), roots_of_unity, inv=True)`.
  fftField (bitReversalPermutation polynomial) roots (inv := true)


/-! ## Blob <-> Polynomial -/

/-- Convert a blob to a sequence of elements of `Fr`.

It rejects a 32-byte chunk of at least the modulus. -/
def blobToPolynomial (blob : Blob) : Except KzgError Polynomial :=
  -- blob_to_polynomial: `bytes_to_bls_field` of each 32-byte slice `i`, in order.
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
  -- The caller checks the width and passes `roots_of_unity_brp`.
  --
  -- evaluate_polynomial_in_evaluation_form: `width = len(polynomial)`.
  let width := polynomial.size
  -- `inverse_width = BLSFieldElement(width).inverse()`.
  let inverseWidth := (Fr.ofNat width).inverse
  let points := polynomial.zip domain
  -- `if z in roots_of_unity_brp: return polynomial[eval_index]`.
  match points.find? (·.2 == z) with
  | some (y, _) => y
  | none =>
    -- The barycentric formula, where `z` is not in the domain, so no `z - domain[i]` is zero.
    --
    -- `b = z - roots_of_unity_brp[i]`, all inverted with one batch inversion.
    let inverses := Fr.batchInverse (points.map fun (_, d) => z - d)
    -- `a = polynomial[i] * roots_of_unity_brp[i]`, and `result += a / b`.
    let acc := (points.zip inverses).foldl (init := Fr.zero) fun acc ((y, d), inv) =>
      acc + y * d * inv
    -- `r = z.pow(BLSFieldElement(width)) - BLSFieldElement(1)`.
    let r := z ^ (Fr.ofNat width) - Fr.one
    -- `result = result * r * inverse_width`.
    acc * r * inverseWidth

/-- Evaluate an evaluation-form polynomial at `z`.

When `z` is a point `D[i]` of the domain, the value is entry `i`.

Otherwise it is the barycentric formula, for the domain size `W`:

`f(z) = (z^W − 1) / W · Σ_i (f(D[i]) · D[i]) / (z − D[i])`.

It rejects a polynomial that does not have exactly 4096 elements. -/
def evaluatePolynomialInEvaluationForm
    (polynomial : Polynomial) (z : Fr) : Except KzgError Fr :=
  -- evaluate_polynomial_in_evaluation_form: `assert width == FIELD_ELEMENTS_PER_BLOB`.
  if polynomial.size ≠ FIELD_ELEMENTS_PER_BLOB then
    .error (.badPolynomialSize polynomial.size)
  -- `roots_of_unity_brp = bit_reversal_permutation(compute_roots_of_unity(...))`.
  else
    .ok (evaluatePolynomialInEvaluationFormAux polynomial
      (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB) z)

end EthLib.Cryptography.Kzg
