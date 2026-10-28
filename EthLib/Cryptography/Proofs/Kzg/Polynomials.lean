import EthLib.Cryptography.Kzg.Polynomials
import EthLib.Cryptography.Proofs.Bls.Fr
import EthLib.Cryptography.Proofs.Kzg.BitReversal

/-!
# Proofs: `Polynomials`

Properties of the polynomial helpers: byte <-> field element
conversions round-trip, `computePowers` really returns powers,
`blobToPolynomial` is characterized on its success and failure paths,
and evaluation at a domain point is a table lookup.
-/

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal

/-- `bytesBEToNatAux` coincides with `Fr.fromBytesBEAux` (they implement
the same fold). -/
private theorem bytesBEToNatAux_eq_fromBytesBEAux (acc : Nat)
    (l : List UInt8) :
    bytesBEToNatAux acc l = Bls.Fr.fromBytesBEAux acc l := by
  induction l generalizing acc with
  | nil => rfl
  | cons u rest ih =>
    simp only [bytesBEToNatAux, Bls.Fr.fromBytesBEAux]
    exact ih _

/-- Shifting left by a byte and or-ing in a byte is base-256 arithmetic. -/
theorem shiftLeft_eight_or (a u : Nat) (hu : u < 256) :
    (a <<< 8) ||| u = a * 256 + u := by
  have h28 : (2 : Nat) ^ 8 = 256 := by decide
  have h1 : ((a <<< 8) ||| u) % 2 ^ 8 = u := by
    rw [Nat.or_mod_two_pow, Nat.shiftLeft_eq, Nat.mul_mod_left,
      Nat.mod_eq_of_lt (h28 ▸ hu), Nat.zero_or]
  have h2 : ((a <<< 8) ||| u) / 2 ^ 8 = a := by
    rw [Nat.or_div_two_pow, Nat.shiftLeft_eq,
      Nat.mul_div_cancel a (Nat.two_pow_pos 8),
      Nat.div_eq_of_lt (h28 ▸ hu), Nat.or_zero]
  have h3 := Nat.div_add_mod ((a <<< 8) ||| u) (2 ^ 8)
  rw [h1, h2, h28] at h3
  omega

/-- The accumulator contributes linearly: `acc` is worth
`acc * 256 ^ length`. -/
theorem bytesBEToNatAux_linear (acc : Nat) (l : List UInt8) :
    bytesBEToNatAux acc l = acc * 256 ^ l.length + bytesBEToNatAux 0 l := by
  induction l generalizing acc with
  | nil => simp [bytesBEToNatAux]
  | cons u rest ih =>
    rw [bytesBEToNatAux, ih, shiftLeft_eight_or acc u.toNat u.toNat_lt_size,
      bytesBEToNatAux, Nat.zero_shiftLeft, Nat.zero_or, ih u.toNat,
      List.length_cons, Nat.pow_succ]
    generalize (256 : Nat) ^ rest.length = P
    rw [Nat.add_mul, Nat.mul_comm P 256, ← Nat.mul_assoc, Nat.add_assoc]

/-- A big-endian decoding of a byte list fits in `8 * length` bits. -/
theorem bytesBEToNatAux_lt (l : List UInt8) : bytesBEToNatAux 0 l < 256 ^ l.length := by
  induction l with
  | nil => simp [bytesBEToNatAux]
  | cons u rest ih =>
    rw [bytesBEToNatAux, Nat.zero_shiftLeft, Nat.zero_or,
      bytesBEToNatAux_linear, List.length_cons, Nat.pow_succ]
    have h1 : u.toNat * 256 ^ rest.length + 256 ^ rest.length
        ≤ 256 * 256 ^ rest.length := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ u.toNat_lt_size
    omega

/-- A big-endian decoding fits in `8 * size` bits. -/
theorem bytesBEToNat_lt (b : ByteArray) : bytesBEToNat b < 256 ^ b.size := by
  have := bytesBEToNatAux_lt b.data.toList
  simpa [bytesBEToNat] using this

/-- Decoding the encoding of `n` over `len` bytes recovers `n` modulo
`256 ^ len`. -/
theorem bytesBEToNat_intToBytesBE (n len : Nat) :
    bytesBEToNat (intToBytesBE n len) = n % 256 ^ len := by
  induction len with
  | zero => simp [bytesBEToNat, intToBytesBE, bytesBEToNatAux, Nat.mod_one]
  | succ len ih =>
    have hdecomp : (intToBytesBE n (len + 1)).data.toList
        = UInt8.ofNat ((n >>> (len * 8)) &&& 0xff) ::
          (intToBytesBE n len).data.toList := by
      have h0 : len + 1 - 1 - 0 = len := by omega
      have hs : ∀ i : Fin len, len + 1 - 1 - (i.val + 1) = len - 1 - i.val :=
        fun i => by omega
      simp only [intToBytesBE, Array.toList_ofFn, List.ofFn_succ,
        Fin.val_zero, Fin.val_succ, h0, hs]
    have hlen : (intToBytesBE n len).data.toList.length = len := by
      simp [intToBytesBE]
    have hbyte : (UInt8.ofNat ((n >>> (len * 8)) &&& 0xff)).toNat
        = n / 256 ^ len % 256 := by
      rw [UInt8.toNat_ofNat', show (0xff : Nat) = 2 ^ 8 - 1 by decide,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod,
        Nat.shiftRight_eq_div_pow, Nat.pow_mul',
        show (2 : Nat) ^ 8 = 256 by decide]
    rw [bytesBEToNat, hdecomp, bytesBEToNatAux, Nat.zero_shiftLeft,
      Nat.zero_or, bytesBEToNatAux_linear, hlen, hbyte]
    rw [bytesBEToNat] at ih
    rw [ih, Nat.pow_succ, Nat.mod_mul, Nat.mul_comm (n / 256 ^ len % 256)]
    exact Nat.add_comm _ _

/-- Decoding inverts encoding for values that fit in `len` bytes. -/
theorem bytesBEToNat_intToBytesBE_of_lt {n len : Nat}
    (h : n < 256 ^ len) :
    bytesBEToNat (intToBytesBE n len) = n := by
  rw [bytesBEToNat_intToBytesBE, Nat.mod_eq_of_lt h]

/-- Decoding is injective on byte lists of one length.

Two lists of length `n` are two base-256 numbers with `n` digits.
Equal values force equal digits, read from the most significant one down.
-/
theorem bytesBEToNatAux_inj {l₁ l₂ : List UInt8}
    (hlen : l₁.length = l₂.length)
    (h : bytesBEToNatAux 0 l₁ = bytesBEToNatAux 0 l₂) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    -- Two empty lists are equal, and an empty list never matches a non-empty one in length.
    cases l₂ with
    | nil => rfl
    | cons _ _ => cases hlen
  | cons u₁ r₁ ih =>
    cases l₂ with
    | nil => cases hlen
    | cons u₂ r₂ =>
      -- The two tails have the same length n, so both heads carry the weight 256^n.
      have hlen' : r₁.length = r₂.length := Nat.succ.inj hlen
      -- Split each value into its head digit and its tail:
      --
      --     u₁ * 256^n + tail₁ = u₂ * 256^n + tail₂
      have hsplit : ∀ (u : UInt8) (r : List UInt8),
          bytesBEToNatAux 0 (u :: r) = u.toNat * 256 ^ r.length + bytesBEToNatAux 0 r :=
        fun u r => by
          rw [bytesBEToNatAux, Nat.zero_shiftLeft, Nat.zero_or, bytesBEToNatAux_linear]
      rw [hsplit, hsplit, ← hlen'] at h
      -- Each tail is a remainder below 256^n.
      have hr₁ := bytesBEToNatAux_lt r₁
      have hr₂ : bytesBEToNatAux 0 r₂ < 256 ^ r₁.length := hlen' ▸ bytesBEToNatAux_lt r₂
      -- Dividing both sides by 256^n keeps exactly the head digit.
      have hpos : 0 < 256 ^ r₁.length := Nat.pow_pos (by decide)
      have hu : u₁.toNat = u₂.toNat := by
        have hdiv := congrArg (· / 256 ^ r₁.length) h
        simp only [Nat.mul_comm _ (256 ^ r₁.length), Nat.mul_add_div hpos,
          Nat.div_eq_of_lt hr₁, Nat.div_eq_of_lt hr₂] at hdiv
        simpa using hdiv
      -- Equal heads leave equal tails, and the induction hypothesis finishes them.
      rw [hu] at h
      rw [UInt8.toNat_inj.mp hu, ih hlen' (by omega)]

/-- Decoding is injective on byte arrays of one size. -/
theorem bytesBEToNat_inj {a b : ByteArray} (hsz : a.size = b.size)
    (h : bytesBEToNat a = bytesBEToNat b) : a = b := by
  -- Pass to the underlying byte lists, which have the same length.
  have hlen : a.data.toList.length = b.data.toList.length := by
    rw [Array.length_toList, Array.length_toList]
    exact hsz
  exact ByteArray.ext (Array.ext' (bytesBEToNatAux_inj hlen h))

/-- Encoding a decoded byte array at its own size gives back the same bytes.

Big-endian encoding has no slack once the length is fixed.
So any byte array is the canonical encoding of its own value.
-/
theorem intToBytesBE_bytesBEToNat (b : ByteArray) :
    intToBytesBE (bytesBEToNat b) b.size = b :=
  -- The decoded value fits in the size, so encoding then decoding returns it.
  -- Both arrays then have the same size and the same value, hence the same bytes.
  bytesBEToNat_inj Array.size_ofFn
    (bytesBEToNat_intToBytesBE_of_lt (bytesBEToNat_lt b))

/-- A successful `bytesToBlsField` implies: the input was 32 bytes, the
value is the big-endian decoding, and the value is canonical. -/
theorem bytesToBlsField_ok {b : Bytes32} {f : Fr}
    (h : bytesToBlsField b = .ok f) :
    b.size = BYTES_PER_FIELD_ELEMENT ∧ f.val = bytesBEToNat b ∧
      f.val < Fr.modulus := by
  rw [bytesToBlsField] at h
  split at h
  · cases h
  · split at h
    · rename_i g hg
      cases h
      obtain ⟨hsz, hval, hlt⟩ := Bls.Fr.fromBytesBE_ok hg
      refine ⟨hsz, ?_, hlt⟩
      rw [hval, bytesBEToNat, bytesBEToNatAux_eq_fromBytesBEAux]
    · cases h

@[simp] theorem size_blsFieldToBytes (x : Fr) :
    (blsFieldToBytes x).size = BYTES_PER_FIELD_ELEMENT := by
  simp only [blsFieldToBytes, Fr.toBytesBE, ByteArray.size, Array.size_ofFn,
    BYTES_PER_FIELD_ELEMENT]

/-- `bytesToBlsField` is a left inverse of `blsFieldToBytes`. -/
@[simp] theorem bytesToBlsField_blsFieldToBytes (x : Fr) :
    bytesToBlsField (blsFieldToBytes x) = .ok x := by
  have heq : blsFieldToBytes x = intToBytesBE x.val 32 := rfl
  have hlt256 : x.val < 256 ^ 32 :=
    Nat.lt_trans x.isLt (by decide : Fr.modulus < 256 ^ 32)
  have hdec : Bls.Fr.bytesBEToNat (blsFieldToBytes x) = x.val := by
    rw [Bls.Fr.bytesBEToNat, ← bytesBEToNatAux_eq_fromBytesBEAux,
        ← bytesBEToNat, heq, bytesBEToNat_intToBytesBE_of_lt hlt256]
  have hfrom : Bls.Fr.fromBytesBE (blsFieldToBytes x) = .ok x := by
    unfold Bls.Fr.fromBytesBE
    have hsz : ¬ (blsFieldToBytes x).size ≠ 32 := by
      simp [size_blsFieldToBytes, BYTES_PER_FIELD_ELEMENT]
    rw [ite_eq_right hsz]
    dsimp only []
    simp only [hdec, dite_eq_ite, ite_eq_left x.isLt, Fin.eta]
  unfold bytesToBlsField
  have hsz : ¬ (blsFieldToBytes x).size ≠ BYTES_PER_FIELD_ELEMENT := by
    simp [size_blsFieldToBytes]
  rw [ite_eq_right hsz, hfrom]

/-- Drop trailing zero coefficients from a list of field elements. -/
def stripTrailingZerosList : List Fr → List Fr
  | [] => []
  | x :: xs =>
    match stripTrailingZerosList xs with
    | [] => if x.isZero then [] else [x]
    | y :: ys => x :: y :: ys

/-- Drop trailing zero coefficients from a coefficient-form polynomial. -/
def stripTrailingZeros (p : PolynomialCoeff) : PolynomialCoeff :=
  (stripTrailingZerosList p.toList).toArray

private theorem stripTrailingZerosList_eq_nil_iff (l : List Fr) :
    stripTrailingZerosList l = [] ↔ ∀ x ∈ l, x.isZero = true := by
  induction l with
  | nil => simp [stripTrailingZerosList]
  | cons x xs ih =>
    simp only [stripTrailingZerosList, List.mem_cons, forall_eq_or_imp]
    cases hxs : stripTrailingZerosList xs with
    | nil =>
      have hxs' : ∀ a ∈ xs, a.isZero = true := ih.mp hxs
      constructor
      · intro h
        by_cases hx : x.isZero = true
        · exact ⟨hx, hxs'⟩
        · rw [ite_eq_right hx] at h; cases h
      · rintro ⟨hx, _⟩
        rw [ite_eq_left hx]
    | cons y ys =>
      have hne : stripTrailingZerosList xs ≠ [] := by simp [hxs]
      have hnot : ¬ (∀ a ∈ xs, a.isZero = true) := fun hall => hne (ih.mpr hall)
      constructor
      · intro h
        by_cases hx : x.isZero = true
        · rw [ite_eq_left hx] at h; cases h
        · rw [ite_eq_right hx] at h; cases h
      · intro h
        exact absurd h.2 hnot

/-- Stripping trailing zeros yields `#[]` iff every coefficient is zero. -/
theorem stripTrailingZeros_all_zero (p : PolynomialCoeff) :
    stripTrailingZeros p = #[] ↔ ∀ x ∈ p, x.isZero = true := by
  rw [stripTrailingZeros, ← Array.toList_inj, List.toList_toArray,
      Array.toList_empty, stripTrailingZerosList_eq_nil_iff]
  exact ⟨fun h x hx => h x (Array.mem_toList_iff.mpr hx),
    fun h x hx => h x (Array.mem_toList_iff.mp hx)⟩

private theorem stripTrailingZerosList_last_ne_zero (l : List Fr)
    (h : stripTrailingZerosList l ≠ []) :
    (stripTrailingZerosList l)[(stripTrailingZerosList l).length - 1]!.isZero = false := by
  induction l with
  | nil => exact absurd rfl h
  | cons x xs ih =>
    dsimp only [stripTrailingZerosList] at h ⊢
    revert h
    cases hxs : stripTrailingZerosList xs with
    | nil =>
      by_cases hx : x.isZero = true
      · simp [hx]
      · rw [ite_eq_right hx]
        intro _
        simpa [Bool.not_eq_true] using hx
    | cons y ys =>
      intro _
      have hne : stripTrailingZerosList xs ≠ [] := by simp [hxs]
      have hih := ih hne
      rw [hxs] at hih
      simpa using hih

/-- A non-empty stripped polynomial has a non-zero leading coefficient. -/
theorem stripTrailingZeros_nonempty_last_ne_zero {p : PolynomialCoeff}
    (h : (stripTrailingZeros p).isEmpty = false) :
    (stripTrailingZeros p)[(stripTrailingZeros p).size - 1]!.isZero = false := by
  have hne : stripTrailingZerosList p.toList ≠ [] := by
    intro hnil
    simp [stripTrailingZeros, hnil] at h
  have hlast := stripTrailingZerosList_last_ne_zero p.toList hne
  simpa [stripTrailingZeros] using hlast

private theorem stripTrailingZerosList_idempotent (l : List Fr) :
    stripTrailingZerosList (stripTrailingZerosList l) = stripTrailingZerosList l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hih := ih
    rw [stripTrailingZerosList]
    cases hxs : stripTrailingZerosList xs with
    | nil =>
      by_cases hx : x.isZero = true
      · rw [ite_eq_left hx]; rfl
      · rw [ite_eq_right hx]
        show (if x.isZero = true then [] else [x]) = [x]
        rw [ite_eq_right hx]
    | cons y ys =>
      dsimp only
      rw [stripTrailingZerosList, ← hxs, hih, hxs]

/-- Stripping trailing zeros is idempotent. -/
@[simp] theorem stripTrailingZeros_idempotent (p : PolynomialCoeff) :
    stripTrailingZeros (stripTrailingZeros p) = stripTrailingZeros p := by
  simp [stripTrailingZeros, stripTrailingZerosList_idempotent]

/-- Summing coefficient-form polynomials spans the longer of the two. -/
@[simp] theorem size_addPolynomialcoeff (a b : PolynomialCoeff) :
    (addPolynomialcoeff a b).size = max a.size b.size := by
  rw [addPolynomialcoeff]
  by_cases h : a.size ≥ b.size
  · rw [ite_eq_left h]
    simp only [Array.size_ofFn]
    exact (Nat.max_eq_left h).symm
  · rw [ite_eq_right h]
    simp only [Array.size_ofFn]
    exact (Nat.max_eq_right (Nat.le_of_not_le h)).symm

private theorem getElem!_of_ge_size (p : PolynomialCoeff) {i : Nat}
    (h : ¬ i < p.size) : p[i]! = Fr.zero := by
  rw [getElem!_neg p i h]
  rfl

private theorem ite_lt_size_getElem! (p : PolynomialCoeff) (i : Nat) :
    (if i < p.size then p[i]! else Fr.zero) = p[i]! := by
  by_cases h : i < p.size
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, getElem!_of_ge_size p h]

/-- Coefficient `i` of `addPolynomialcoeff a b` is `a[i]! + b[i]!` for all `i`
(since out-of-bounds accesses default to `Fr.zero`). -/
@[simp] theorem addPolynomialcoeff_getElem! (a b : PolynomialCoeff) (i : Nat) :
    (addPolynomialcoeff a b)[i]! = a[i]! + b[i]! := by
  rw [addPolynomialcoeff]
  by_cases hab : a.size ≥ b.size
  · rw [ite_eq_left hab]
    dsimp only []
    by_cases hi : i < a.size
    · rw [getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn,
          ite_lt_size_getElem!]
    · have hib : ¬ i < b.size := by omega
      rw [getElem!_of_ge_size _ (by simp [hi]),
          getElem!_of_ge_size a hi, getElem!_of_ge_size b hib]
      rfl
  · rw [ite_eq_right hab]
    dsimp only []
    by_cases hi : i < b.size
    · rw [getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn,
          ite_lt_size_getElem!, Fr.add_comm]
    · have hia : ¬ i < a.size := by omega
      rw [getElem!_of_ge_size _ (by simp [hi]),
          getElem!_of_ge_size a hia, getElem!_of_ge_size b hi]
      rfl

private theorem fr_add_zero (a : Fr) : a + Fr.zero = a :=
  Fin.add_zero a

private theorem fr_zero_add (a : Fr) : Fr.zero + a = a :=
  Fin.zero_add a

private theorem fr_zero_mul (a : Fr) : Fr.zero * a = Fr.zero :=
  Fin.zero_mul a

private theorem fr_add_mul (a b c : Fr) : (a + b) * c = a * c + b * c := by
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_mul, Nat.add_mod_mod, Nat.mod_add_mod,
    Nat.mod_mul_mod, Nat.add_mul]

/-- Direct monomial sum evaluation `∑_{i < n} p[i] * x^i` of the first `n`
coefficients of `p` at `x`. -/
def evalCoeffPolyAux (p : PolynomialCoeff) (x : Fr) : Nat → Fr
  | 0 => Fr.zero
  | n + 1 => evalCoeffPolyAux p x n + p[n]! * Fr.powNat x n

/-- Evaluate a coefficient-form polynomial `p` at `x` as `∑_{i < p.size} p[i] * x^i`. -/
def evalCoeffPoly (p : PolynomialCoeff) (x : Fr) : Fr :=
  evalCoeffPolyAux p x p.size

private theorem evalCoeffPolyAux_addPolynomialcoeff (a b : PolynomialCoeff)
    (x : Fr) (n : Nat) :
    evalCoeffPolyAux (addPolynomialcoeff a b) x n =
      evalCoeffPolyAux a x n + evalCoeffPolyAux b x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [evalCoeffPolyAux, ih, addPolynomialcoeff_getElem!, fr_add_mul]
    rw [← Fr.add_assoc, ← Fr.add_assoc,
        Fr.add_right_comm (evalCoeffPolyAux a x n) (evalCoeffPolyAux b x n)]

private theorem evalCoeffPolyAux_of_le (p : PolynomialCoeff) (x : Fr) {n : Nat}
    (h : p.size ≤ n) : evalCoeffPolyAux p x n = evalCoeffPoly p x := by
  induction n with
  | zero =>
    have h0 : p.size = 0 := by omega
    simp [evalCoeffPoly, h0]
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · rw [← heq]
      rfl
    · have hn : p.size ≤ n := by omega
      rw [evalCoeffPolyAux, ih hn, getElem!_of_ge_size p (by omega),
          fr_zero_mul, fr_add_zero]

/-- Evaluating the sum of two coefficient-form polynomials equals the sum of
their evaluations. -/
theorem evalCoeffPoly_addPolynomialcoeff (a b : PolynomialCoeff) (x : Fr) :
    evalCoeffPoly (addPolynomialcoeff a b) x =
      evalCoeffPoly a x + evalCoeffPoly b x := by
  rw [evalCoeffPoly, size_addPolynomialcoeff,
      evalCoeffPolyAux_addPolynomialcoeff,
      evalCoeffPolyAux_of_le a x (Nat.le_max_left _ _),
      evalCoeffPolyAux_of_le b x (Nat.le_max_right _ _)]

/-- Alias of `evalCoeffPoly_addPolynomialcoeff`. -/
theorem evalPoly_addPolynomialcoeff (a b : PolynomialCoeff) (x : Fr) :
    evalCoeffPoly (addPolynomialcoeff a b) x =
      evalCoeffPoly a x + evalCoeffPoly b x :=
  evalCoeffPoly_addPolynomialcoeff a b x

/-- Alias of `evalCoeffPoly` used in external specifications. -/
abbrev evalPolyAt (p : PolynomialCoeff) (x : Fr) : Fr :=
  evalCoeffPoly p x

/-- Evaluating `addPolynomialcoeff a b` at `x` equals `evalPolyAt a x + evalPolyAt b x`. -/
theorem evalPolyAt_addPoly (a b : PolynomialCoeff) (x : Fr) :
    evalPolyAt (addPolynomialcoeff a b) x = evalPolyAt a x + evalPolyAt b x :=
  evalCoeffPoly_addPolynomialcoeff a b x

/-- Multiplying an empty left polynomial by a bounded right polynomial returns `#[Fr.zero]`. -/
@[simp] theorem multiplyPolynomialcoeff_empty_left {b : PolynomialCoeff}
    (hb : b.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB) :
    multiplyPolynomialcoeff #[] b = .ok #[Fr.zero] := by
  have hnot : ¬ ((#[] : PolynomialCoeff).size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB) := by
    simp
    omega
  rw [multiplyPolynomialcoeff, ite_eq_right hnot]
  rfl

private theorem addPolynomialcoeff_replicate_zero (m n : Nat) :
    addPolynomialcoeff (Array.replicate m Fr.zero) (Array.replicate n Fr.zero) =
      Array.replicate (max m n) Fr.zero := by
  apply Array.ext
  · simp [size_addPolynomialcoeff]
  · intro i hi1 hi2
    rw [ ← getElem!_pos _ i hi1, ← getElem!_pos _ i hi2,
        addPolynomialcoeff_getElem!]
    have hm : (Array.replicate m Fr.zero)[i]! = Fr.zero := by
      by_cases h : i < m
      · rw [getElem!_pos _ i (by simp [h]), Array.getElem_replicate]
      · exact getElem!_of_ge_size _ (by simp [h])
    have hn : (Array.replicate n Fr.zero)[i]! = Fr.zero := by
      by_cases h : i < n
      · rw [getElem!_pos _ i (by simp [h]), Array.getElem_replicate]
      · exact getElem!_of_ge_size _ (by simp [h])
    have hmn : (Array.replicate (max m n) Fr.zero)[i]! = Fr.zero := by
      rw [getElem!_pos _ i hi2, Array.getElem_replicate]
    rw [hm, hn, hmn, fr_add_zero]

/-- `multiplyPolynomialcoeff` rejects polynomials whose combined length
exceeds `FIELD_ELEMENTS_PER_EXT_BLOB`. -/
theorem multiplyPolynomialcoeff_too_large {a b : PolynomialCoeff}
    (h : a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB) :
    multiplyPolynomialcoeff a b =
      .error (.polynomialProductTooLong a.size b.size) := by
  unfold multiplyPolynomialcoeff
  rw [ite_eq_left h]
  rfl

private def mulFoldStep (a b : PolynomialCoeff) (r : PolynomialCoeff)
    (power : Nat) : PolynomialCoeff :=
  let coef := a[power]!
  let summand : PolynomialCoeff :=
    Array.replicate power Fr.zero ++ b.map (· * coef)
  addPolynomialcoeff r summand

private theorem foldl_mulFoldStep_empty_right (a : PolynomialCoeff) (k : Nat) :
    (List.range k).foldl (mulFoldStep a #[]) #[Fr.zero] =
      Array.replicate (max (k - 1) 1) Fr.zero := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih, mulFoldStep]
    simp only [Array.map_empty, Array.append_empty]
    rw [addPolynomialcoeff_replicate_zero]
    congr 1
    omega

/-- Multiplying a bounded polynomial by `#[]` produces a zero polynomial of size
`max (a.size - 1) 1`. -/
@[simp] theorem multiplyPolynomialcoeff_empty_right {a : PolynomialCoeff}
    (ha : a.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB) :
    multiplyPolynomialcoeff a #[] =
      .ok (Array.replicate (max (a.size - 1) 1) Fr.zero) := by
  have hnot : ¬ (a.size + (#[] : PolynomialCoeff).size > FIELD_ELEMENTS_PER_EXT_BLOB) := by
    simp
    omega
  rw [multiplyPolynomialcoeff, ite_eq_right hnot]
  change Except.ok ((Array.range a.size).foldl (mulFoldStep a #[]) #[Fr.zero]) = _
  rw [← Array.foldl_toList, Array.toList_range, foldl_mulFoldStep_empty_right]

private theorem size_mulFoldStep (a b r : PolynomialCoeff) (power : Nat) :
    (mulFoldStep a b r power).size = max r.size (power + b.size) := by
  simp [mulFoldStep, size_addPolynomialcoeff, Array.size_append]

private theorem size_foldl_mulFoldStep (a b : PolynomialCoeff) (k : Nat) :
    ((List.range k).foldl (mulFoldStep a b) #[Fr.zero]).size =
      if k = 0 then 1 else max (k + b.size - 1) 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        size_mulFoldStep, ih, ite_eq_right (Nat.succ_ne_zero k)]
    by_cases hk : k = 0
    · subst hk
      rw [ite_eq_left rfl]
      omega
    · rw [ite_eq_right hk]
      omega

/-- A successful `multiplyPolynomialcoeff` returns `#[Fr.zero]` (size `1`) when
`a` is empty, and a polynomial of size `max (a.size + b.size - 1) 1` otherwise. -/
theorem size_multiplyPolynomialcoeff {a b p : PolynomialCoeff}
    (h : multiplyPolynomialcoeff a b = .ok p) :
    p.size = if a.isEmpty then 1 else max (a.size + b.size - 1) 1 := by
  rw [multiplyPolynomialcoeff] at h
  by_cases hgt : a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB
  · rw [ite_eq_left hgt] at h
    cases h
  · rw [ite_eq_right hgt] at h
    change Except.ok _ = Except.ok p at h
    injection h with hp
    subst hp
    have hfold : (Array.range a.size).foldl (mulFoldStep a b) #[Fr.zero] =
        (List.range a.size).foldl (mulFoldStep a b) #[Fr.zero] := by
      rw [← Array.foldl_toList, Array.toList_range]
    change ((Array.range a.size).foldl (mulFoldStep a b) #[Fr.zero]).size = _
    rw [hfold, size_foldl_mulFoldStep a b a.size]
    by_cases ha : a.isEmpty = true
    · have ha0 : a.size = 0 := Array.isEmpty_iff_size_eq_zero.mp ha
      simp [ha, ha0]
    · have ha0 : a.size ≠ 0 := by
        simpa [Array.isEmpty_iff_size_eq_zero] using ha
      simp [ha, ha0]

private theorem getElem!_zero_singleton (i : Nat) :
    (#[Fr.zero] : PolynomialCoeff)[i]! = Fr.zero := by
  by_cases hi : i < 1
  · have hi0 : i = 0 := by omega
    subst hi0
    rfl
  · exact getElem!_of_ge_size #[Fr.zero] hi

private theorem getElem!_foldl_mulFoldStep_before_top (a b : PolynomialCoeff)
    (hb : 0 < b.size) (k : Nat) :
    ((List.range k).foldl (mulFoldStep a b) #[Fr.zero])[k + b.size - 1]! =
      Fr.zero := by
  by_cases hk : k = 0
  · subst hk
    exact getElem!_zero_singleton (0 + b.size - 1)
  · apply getElem!_of_ge_size
    rw [size_foldl_mulFoldStep a b k, ite_eq_right hk]
    omega

/-- For non-empty inputs `a` and `b`, the leading coefficient of
`multiplyPolynomialcoeff a b` is `a[a.size - 1]! * b[b.size - 1]!`. -/
theorem leadingCoeff_multiplyPolynomialcoeff {a b p : PolynomialCoeff}
    (ha : a.isEmpty = false) (hb : b.isEmpty = false)
    (h : multiplyPolynomialcoeff a b = .ok p) :
    p[a.size + b.size - 2]! = a[a.size - 1]! * b[b.size - 1]! := by
  have ha0 : 0 < a.size := by
    simpa [Array.isEmpty_iff_size_eq_zero, Nat.pos_iff_ne_zero] using ha
  have hb0 : 0 < b.size := by
    simpa [Array.isEmpty_iff_size_eq_zero, Nat.pos_iff_ne_zero] using hb
  rw [multiplyPolynomialcoeff] at h
  by_cases hgt : a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB
  · rw [ite_eq_left hgt] at h
    cases h
  · rw [ite_eq_right hgt] at h
    change Except.ok _ = Except.ok p at h
    injection h with hp
    subst hp
    have hfold : (Array.range a.size).foldl (mulFoldStep a b) #[Fr.zero] =
        (List.range a.size).foldl (mulFoldStep a b) #[Fr.zero] := by
      rw [← Array.foldl_toList, Array.toList_range]
    change ((Array.range a.size).foldl (mulFoldStep a b) #[Fr.zero])[a.size + b.size - 2]! = _
    rw [hfold]
    obtain ⟨k, hk⟩ : ∃ k, a.size = k + 1 := ⟨a.size - 1, by omega⟩
    rw [hk, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hidx : k + 1 + b.size - 2 = k + b.size - 1 := by omega
    have hsub : k + 1 - 1 = k := by omega
    rw [hidx, hsub, mulFoldStep, addPolynomialcoeff_getElem!,
        getElem!_foldl_mulFoldStep_before_top a b hb0 k, fr_zero_add]
    have hpos : k + b.size - 1 <
        (Array.replicate k Fr.zero ++ b.map (· * a[k]!)).size := by
      simp [Array.size_append]
      omega
    rw [getElem!_pos _ (k + b.size - 1) hpos,
        Array.getElem_append_right (by simp; omega)]
    simp only [Array.size_replicate, Array.getElem_map]
    have hbi : k + b.size - 1 - k = b.size - 1 := by omega
    rw [getElem!_pos b (b.size - 1) (by omega), Fr.mul_comm]
    congr 2

private theorem foldlM_vanishing_size_and_lead (xs : List Fr)
    (init : PolynomialCoeff) (hinit_pos : 0 < init.size)
    (hinit_lead : init[init.size - 1]! = Fr.one)
    (p : PolynomialCoeff)
    (h : xs.foldlM (fun q x => multiplyPolynomialcoeff q #[-x, Fr.one]) init = .ok p) :
    p.size = init.size + xs.length ∧ p[p.size - 1]! = Fr.one := by
  induction xs generalizing init with
  | nil =>
    cases h
    exact ⟨by simp, hinit_lead⟩
  | cons x rest ih =>
    simp only [List.foldlM_cons, Bind.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i q hq
      have hq_ne : init.isEmpty = false := by
        simpa [Array.isEmpty_iff_size_eq_zero] using Nat.ne_of_gt hinit_pos
      have hbin_ne : (#[-x, Fr.one] : PolynomialCoeff).isEmpty = false := rfl
      have hq_sz : q.size = init.size + 1 := by
        have := size_multiplyPolynomialcoeff hq
        rw [ite_eq_right (by simp [hq_ne])] at this
        simpa using this
      have hq_lead : q[q.size - 1]! = Fr.one := by
        have hlead := leadingCoeff_multiplyPolynomialcoeff hq_ne hbin_ne hq
        have hidx : q.size - 1 = init.size + (#[-x, Fr.one] : PolynomialCoeff).size - 2 := by
          simp [hq_sz]
        rw [hidx, hlead, hinit_lead]
        rfl
      obtain ⟨hsz, hld⟩ := ih q (by omega) hq_lead h
      refine ⟨?_, hld⟩
      simp [hsz, hq_sz, Nat.add_right_comm, Nat.add_assoc]

/-- A successful `vanishingPolynomialcoeff xs` produces a polynomial of size
`xs.size + 1` with leading coefficient `Fr.one`. -/
theorem size_and_leadingCoeff_vanishingPolynomialcoeff
    {xs : Array Fr} {p : PolynomialCoeff}
    (h : vanishingPolynomialcoeff xs = .ok p) :
    p.size = xs.size + 1 ∧ p[xs.size]! = Fr.one := by
  rw [vanishingPolynomialcoeff, ← Array.foldlM_toList] at h
  obtain ⟨hsz, hlead⟩ := foldlM_vanishing_size_and_lead xs.toList #[Fr.one]
    (by decide) rfl p h
  have hsz' : p.size = xs.size + 1 := by simpa [Nat.add_comm] using hsz
  refine ⟨hsz', ?_⟩
  simpa [hsz'] using hlead

/-- A successful `multiplyPolynomialcoeff` implies the input sizes sum to at
most `FIELD_ELEMENTS_PER_EXT_BLOB`. -/
theorem multiplyPolynomialcoeff_le_of_ok {a b p : PolynomialCoeff}
    (h : multiplyPolynomialcoeff a b = .ok p) :
    a.size + b.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB :=
  Decidable.byContradiction fun hgt => by
    rw [multiplyPolynomialcoeff_too_large (by omega)] at h
    cases h

/-- `multiplyPolynomialcoeff` succeeds whenever the input sizes sum to at
most `FIELD_ELEMENTS_PER_EXT_BLOB`. -/
theorem multiplyPolynomialcoeff_ok_of_le {a b : PolynomialCoeff}
    (h : a.size + b.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB) :
    ∃ p, multiplyPolynomialcoeff a b = .ok p ∧
      p.size = (if a.isEmpty then 1 else max (a.size + b.size - 1) 1) := by
  have hok : ∃ p, multiplyPolynomialcoeff a b = .ok p := by
    unfold multiplyPolynomialcoeff
    rw [ite_eq_right (by omega)]
    exact ⟨_, rfl⟩
  rcases hok with ⟨p, hp⟩
  exact ⟨p, hp, size_multiplyPolynomialcoeff hp⟩

private theorem foldlM_vanishing_bound (xs : List Fr)
    (init : PolynomialCoeff) (hinit_pos : 0 < init.size)
    (p : PolynomialCoeff)
    (h : xs.foldlM (fun q x => multiplyPolynomialcoeff q #[-x, Fr.one]) init = .ok p) :
    xs = [] ∨ init.size + xs.length < FIELD_ELEMENTS_PER_EXT_BLOB := by
  induction xs generalizing init with
  | nil => exact Or.inl rfl
  | cons x rest ih =>
    right
    simp only [List.foldlM_cons, Bind.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i q hq
      have hle := multiplyPolynomialcoeff_le_of_ok hq
      have hbin : (#[-x, Fr.one] : PolynomialCoeff).size = 2 := rfl
      have hq_ne : init.isEmpty = false := by
        simpa [Array.isEmpty_iff_size_eq_zero] using Nat.ne_of_gt hinit_pos
      have hq_sz : q.size = init.size + 1 := by
        have := size_multiplyPolynomialcoeff hq
        rw [ite_eq_right (by simp [hq_ne])] at this
        simpa using this
      rcases ih q (by omega) h with rfl | hlt
      · simp only [List.length_cons, List.length_nil]
        omega
      · simp only [List.length_cons]
        omega

private theorem foldlM_vanishing_ok (xs : List Fr)
    (init : PolynomialCoeff) (hinit_pos : 0 < init.size)
    (hbound : xs = [] ∨ init.size + xs.length < FIELD_ELEMENTS_PER_EXT_BLOB) :
    ∃ p, xs.foldlM (fun q x => multiplyPolynomialcoeff q #[-x, Fr.one]) init = .ok p := by
  induction xs generalizing init with
  | nil => exact ⟨init, rfl⟩
  | cons x rest ih =>
    rcases hbound with hnil | hlt
    · cases hnil
    · simp only [List.length_cons] at hlt
      have hle : init.size + (#[-x, Fr.one] : PolynomialCoeff).size ≤ FIELD_ELEMENTS_PER_EXT_BLOB := by
        have : (#[-x, Fr.one] : PolynomialCoeff).size = 2 := rfl
        omega
      obtain ⟨q, hq, hq_sz⟩ := multiplyPolynomialcoeff_ok_of_le hle
      have hq_ne : init.isEmpty = false := by
        simpa [Array.isEmpty_iff_size_eq_zero] using Nat.ne_of_gt hinit_pos
      rw [ite_eq_right (by simp [hq_ne])] at hq_sz
      have hq_sz' : q.size = init.size + 1 := by simpa using hq_sz
      obtain ⟨p, hp⟩ := ih q (by omega) (by right; omega)
      refine ⟨p, ?_⟩
      simp only [List.foldlM_cons, Bind.bind, Except.bind, hq, hp]

/-- A successful `vanishingPolynomialcoeff xs` requires `xs.size + 1 < FIELD_ELEMENTS_PER_EXT_BLOB`. -/
theorem vanishingPolynomialcoeff_lt_of_ok {xs : Array Fr} {p : PolynomialCoeff}
    (h : vanishingPolynomialcoeff xs = .ok p) :
    xs.size + 1 < FIELD_ELEMENTS_PER_EXT_BLOB := by
  rw [vanishingPolynomialcoeff, ← Array.foldlM_toList] at h
  rcases foldlM_vanishing_bound xs.toList #[Fr.one] (by decide) p h with hnil | hlt
  · have hsz : xs.size = 0 := by simpa using congrArg List.length hnil
    rw [hsz]
    decide
  · simpa [Nat.add_comm] using hlt

/-- `vanishingPolynomialcoeff xs` succeeds with a monic polynomial of size
`xs.size + 1` whenever `xs.size + 1 < FIELD_ELEMENTS_PER_EXT_BLOB`. -/
theorem vanishingPolynomialcoeff_ok_of_lt {xs : Array Fr}
    (h : xs.size + 1 < FIELD_ELEMENTS_PER_EXT_BLOB) :
    ∃ p, vanishingPolynomialcoeff xs = .ok p ∧
      p.size = xs.size + 1 ∧ p[xs.size]! = Fr.one := by
  have hok : ∃ p, vanishingPolynomialcoeff xs = .ok p := by
    rw [vanishingPolynomialcoeff, ← Array.foldlM_toList]
    exact foldlM_vanishing_ok xs.toList #[Fr.one] (by decide)
      (Or.inr (by simpa [Nat.add_comm] using h))
  rcases hok with ⟨p, hp⟩
  obtain ⟨hsz, hlead⟩ := size_and_leadingCoeff_vanishingPolynomialcoeff hp
  exact ⟨p, hp, hsz, hlead⟩

/-- `vanishingPolynomialcoeff xs` succeeds iff `xs.size + 1 < FIELD_ELEMENTS_PER_EXT_BLOB`. -/
theorem vanishingPolynomialcoeff_ok_iff {xs : Array Fr} :
    (∃ p, vanishingPolynomialcoeff xs = .ok p) ↔
      xs.size + 1 < FIELD_ELEMENTS_PER_EXT_BLOB :=
  ⟨fun ⟨_, hp⟩ => vanishingPolynomialcoeff_lt_of_ok hp,
   fun h => let ⟨p, hp, _, _⟩ := vanishingPolynomialcoeff_ok_of_lt h; ⟨p, hp⟩⟩

private theorem fr_mul_zero (a : Fr) : a * Fr.zero = Fr.zero :=
  Fin.mul_zero a

private theorem fr_mul_one (a : Fr) : a * Fr.one = a :=
  Fin.mul_one a

private theorem fr_one_mul (a : Fr) : Fr.one * a = a :=
  Fin.one_mul a

private theorem fr_powNat_add (x : Fr) (a b : Nat) :
    Fr.powNat x (a + b) = Fr.powNat x a * Fr.powNat x b := by
  induction b with
  | zero =>
    rw [Nat.add_zero, Fr.powNat_zero, fr_mul_one]
  | succ b ih =>
    rw [Nat.add_succ, Fr.powNat_succ, Fr.powNat_succ, ih,
        ← Fr.mul_assoc, Fr.mul_comm x (Fr.powNat x a), Fr.mul_assoc]

private theorem map_mul_getElem! (b : PolynomialCoeff) (c : Fr) (n : Nat) :
    (b.map (· * c))[n]! = b[n]! * c := by
  by_cases hn : n < b.size
  · rw [getElem!_pos _ n (by simp [hn]), getElem!_pos b n hn, Array.getElem_map]
  · rw [getElem!_of_ge_size _ (by simp [hn]), getElem!_of_ge_size b hn, fr_zero_mul]

private theorem evalCoeffPolyAux_scale_right (b : PolynomialCoeff) (c x : Fr) (n : Nat) :
    evalCoeffPolyAux (b.map (· * c)) x n = evalCoeffPolyAux b x n * c := by
  induction n with
  | zero =>
    simp [evalCoeffPolyAux, fr_zero_mul]
  | succ n ih =>
    simp only [evalCoeffPolyAux, ih, map_mul_getElem!]
    rw [fr_add_mul, Fr.mul_assoc, Fr.mul_comm c (Fr.powNat x n), ← Fr.mul_assoc]

private theorem evalCoeffPoly_scale_right (b : PolynomialCoeff) (c x : Fr) :
    evalCoeffPoly (b.map (· * c)) x = evalCoeffPoly b x * c := by
  simp only [evalCoeffPoly, Array.size_map, evalCoeffPolyAux_scale_right]

private theorem evalCoeffPolyAux_replicate_zero_append_le (q : PolynomialCoeff) (x : Fr)
    (k n : Nat) (h : n ≤ k) :
    evalCoeffPolyAux (Array.replicate k Fr.zero ++ q) x n = Fr.zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : n < k := by omega
    have hlt : n < (Array.replicate k Fr.zero ++ q).size := by
      simp [Array.size_append]; omega
    rw [evalCoeffPolyAux, ih (by omega), getElem!_pos _ n hlt,
        Array.getElem_append_left (by simp [hn]), Array.getElem_replicate,
        fr_zero_mul, fr_add_zero]

private theorem replicate_zero_append_getElem!_add (q : PolynomialCoeff) (k m : Nat) :
    (Array.replicate k Fr.zero ++ q)[k + m]! = q[m]! := by
  by_cases hm : m < q.size
  · have hlt : k + m < (Array.replicate k Fr.zero ++ q).size := by
      simp [Array.size_append]; omega
    rw [getElem!_pos _ (k + m) hlt, getElem!_pos q m hm,
        Array.getElem_append_right (by simp)]
    simp
  · have hge : ¬ k + m < (Array.replicate k Fr.zero ++ q).size := by
      simp [Array.size_append]; omega
    rw [getElem!_of_ge_size _ hge, getElem!_of_ge_size q hm]

private theorem evalCoeffPolyAux_replicate_zero_append_add (q : PolynomialCoeff) (x : Fr)
    (k m : Nat) :
    evalCoeffPolyAux (Array.replicate k Fr.zero ++ q) x (k + m) =
      evalCoeffPolyAux q x m * Fr.powNat x k := by
  induction m with
  | zero =>
    rw [Nat.add_zero, evalCoeffPolyAux_replicate_zero_append_le q x k k (Nat.le_refl k),
        evalCoeffPolyAux, fr_zero_mul]
  | succ m ih =>
    rw [Nat.add_succ, evalCoeffPolyAux, ih, evalCoeffPolyAux,
        replicate_zero_append_getElem!_add, fr_add_mul,
        fr_powNat_add x k m, Fr.mul_comm (Fr.powNat x k) (Fr.powNat x m),
        ← Fr.mul_assoc]

private theorem evalCoeffPoly_replicate_zero_append (q : PolynomialCoeff) (x : Fr) (k : Nat) :
    evalCoeffPoly (Array.replicate k Fr.zero ++ q) x =
      evalCoeffPoly q x * Fr.powNat x k := by
  unfold evalCoeffPoly
  rw [Array.size_append, Array.size_replicate,
      evalCoeffPolyAux_replicate_zero_append_add]

private theorem evalCoeffPoly_zero_singleton (x : Fr) :
    evalCoeffPoly #[Fr.zero] x = Fr.zero := by
  show Fr.zero + (#[Fr.zero] : PolynomialCoeff)[0]! * Fr.powNat x 0 = Fr.zero
  have h0 : (#[Fr.zero] : PolynomialCoeff)[0]! = Fr.zero := rfl
  rw [h0, fr_zero_mul, fr_add_zero]

private theorem evalCoeffPoly_foldl_mulFoldStep (a b : PolynomialCoeff) (x : Fr) (k : Nat) :
    evalCoeffPoly ((List.range k).foldl (mulFoldStep a b) #[Fr.zero]) x =
      evalCoeffPolyAux a x k * evalCoeffPoly b x := by
  induction k with
  | zero =>
    simp [evalCoeffPoly_zero_singleton, evalCoeffPolyAux, fr_zero_mul]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        mulFoldStep, evalCoeffPoly_addPolynomialcoeff, ih,
        evalCoeffPoly_replicate_zero_append, evalCoeffPoly_scale_right,
        evalCoeffPolyAux, fr_add_mul]
    congr 1
    rw [Fr.mul_assoc, Fr.mul_comm (evalCoeffPoly b x)]

/-- Evaluating the product of two coefficient-form polynomials at `x` equals the
product of their evaluations at `x`. -/
theorem evalPolyAt_mulPoly {a b p : PolynomialCoeff} (x : Fr)
    (h : multiplyPolynomialcoeff a b = .ok p) :
    evalPolyAt p x = evalPolyAt a x * evalPolyAt b x := by
  rw [multiplyPolynomialcoeff] at h
  by_cases hgt : a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB
  · rw [ite_eq_left hgt] at h
    cases h
  · rw [ite_eq_right hgt] at h
    change Except.ok _ = Except.ok p at h
    injection h with hp
    subst hp
    have hfold : (Array.range a.size).foldl (mulFoldStep a b) #[Fr.zero] =
        (List.range a.size).foldl (mulFoldStep a b) #[Fr.zero] := by
      rw [← Array.foldl_toList, Array.toList_range]
    change evalCoeffPoly ((Array.range a.size).foldl (mulFoldStep a b) #[Fr.zero]) x = _
    rw [hfold, evalCoeffPoly_foldl_mulFoldStep]
    rfl

private theorem evalPolyAt_linear_factor_self (z : Fr) :
    evalPolyAt #[-z, Fr.one] z = Fr.zero := by
  show (Fr.zero + (#[-z, Fr.one] : PolynomialCoeff)[0]! * Fr.powNat z 0) +
       (#[-z, Fr.one] : PolynomialCoeff)[1]! * Fr.powNat z 1 = Fr.zero
  have h0 : (#[-z, Fr.one] : PolynomialCoeff)[0]! = -z := rfl
  have h1 : (#[-z, Fr.one] : PolynomialCoeff)[1]! = Fr.one := rfl
  have hp1 : Fr.powNat z 1 = z := by
    rw [Fr.powNat_succ, Fr.powNat_zero, fr_mul_one]
  rw [h0, h1, Fr.powNat_zero, hp1, fr_zero_add, fr_mul_one, fr_one_mul]
  apply Fin.ext
  have hzlt := z.isLt
  simp only [Fin.val_add, Fin.val_neg]
  by_cases hz : z = 0
  · subst hz; rfl
  · rw [ite_eq_right hz]
    show (Fr.modulus - z.val + z.val) % Fr.modulus = 0
    rw [Nat.sub_add_cancel (Nat.le_of_lt hzlt), Nat.mod_self]

private theorem foldlM_vanishing_eval_zero_of_init_zero (xs : List Fr)
    (init v : PolynomialCoeff) (z : Fr)
    (hz : evalPolyAt init z = Fr.zero)
    (h : xs.foldlM (fun q x => multiplyPolynomialcoeff q #[-x, Fr.one]) init = .ok v) :
    evalPolyAt v z = Fr.zero := by
  induction xs generalizing init with
  | nil =>
    cases h
    exact hz
  | cons x rest ih =>
    simp only [List.foldlM_cons, Bind.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i q hq
      have hqz : evalPolyAt q z = Fr.zero := by
        rw [evalPolyAt_mulPoly z hq, hz, fr_zero_mul]
      exact ih q hqz h

private theorem foldlM_vanishing_eval_root (xs : List Fr)
    (init v : PolynomialCoeff) {z : Fr} (hz : z ∈ xs)
    (h : xs.foldlM (fun q x => multiplyPolynomialcoeff q #[-x, Fr.one]) init = .ok v) :
    evalPolyAt v z = Fr.zero := by
  induction xs generalizing init with
  | nil => cases hz
  | cons x rest ih =>
    simp only [List.foldlM_cons, Bind.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i q hq
      rcases List.mem_cons.mp hz with rfl | hmem
      · have hqz : evalPolyAt q z = Fr.zero := by
          rw [evalPolyAt_mulPoly z hq, evalPolyAt_linear_factor_self, fr_mul_zero]
        exact foldlM_vanishing_eval_zero_of_init_zero rest q v z hqz h
      · exact ih q hmem h

/-- Every root `z ∈ zs.toList` evaluates to `Fr.zero` on `vanishingPolynomialcoeff zs`. -/
theorem vanishingPolynomialcoeff_eval_root {zs : Array Fr} {v : PolynomialCoeff}
    (hv : vanishingPolynomialcoeff zs = .ok v) {z : Fr} (hz : z ∈ zs.toList) :
    evalPolyAt v z = Fr.zero := by
  rw [vanishingPolynomialcoeff, ← Array.foldlM_toList] at hv
  exact foldlM_vanishing_eval_root zs.toList #[Fr.one] v hz hv

/-- `dividePolynomialcoeff` rejects an empty divisor, or a divisor whose
leading coefficient is zero when `b.size ≤ a.size`. -/
theorem dividePolynomialcoeff_zero_divisor (a b : PolynomialCoeff)
    (h : b.size = 0 ∨ (b.size ≤ a.size ∧ b[b.size - 1]!.isZero = true)) :
    dividePolynomialcoeff a b = .error .zeroDivisorPolynomial := by
  rcases h with h | ⟨hle, hzero⟩
  · simp [dividePolynomialcoeff, h, Bind.bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw]
  · have hnotlt : ¬ a.size < b.size := by omega
    by_cases hb0 : b.size = 0
    · simp [dividePolynomialcoeff, hb0, Bind.bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw]
    · simp [dividePolynomialcoeff, hb0, hnotlt, hzero, Bind.bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw]

/-- When the dividend has strictly fewer coefficients than the divisor,
`dividePolynomialcoeff` returns the empty quotient `#[]`. -/
theorem dividePolynomialcoeff_lt_size {a b : PolynomialCoeff}
    (hlt : a.size < b.size) :
    dividePolynomialcoeff a b = .ok #[] := by
  have hb0 : b.size ≠ 0 := by omega
  simp [dividePolynomialcoeff, hb0, hlt, pure, Except.pure]

/-- `interpolatePolynomialcoeff` rejects mismatched node and value array lengths. -/
theorem interpolatePolynomialcoeff_size_mismatch {xs ys : Array Fr}
    (h : xs.size ≠ ys.size) :
    interpolatePolynomialcoeff xs ys =
      .error (.inputLengthMismatch "ys" xs.size ys.size) := by
  unfold interpolatePolynomialcoeff
  rw [ite_eq_left h]
  rfl

@[simp] theorem length_computePowersAux (x current : Fr) (n : Nat) :
    (computePowersAux x current n).length = n := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih => simp [computePowersAux, ih]

@[simp] theorem size_computePowers (x : Fr) (n : Nat) :
    (computePowers x n).size = n := by
  simp [computePowers]

/-- Element `i` of `computePowersAux x current n` is `current * x ^ i`
(stated with an `if` so that it also holds for non-canonical `current`,
which is returned unchanged at index `0`). -/
theorem getElem_computePowersAux (x current : Fr) (n i : Nat)
    (h : i < (computePowersAux x current n).length) :
    (computePowersAux x current n)[i] =
      if i = 0 then current else current * Fr.powNat x i := by
  induction n generalizing current i with
  | zero => exact absurd h (by simp)
  | succ n ih =>
    cases i with
    | zero => simp [computePowersAux]
    | succ i =>
      simp only [computePowersAux, List.getElem_cons_succ]
      rw [ih]
      cases i with
      | zero =>
        rw [ite_eq_left rfl, ite_eq_right (Nat.succ_ne_zero 0), Fr.powNat_succ,
          Fr.powNat_zero, Fr.mul_mul_one]
      | succ i =>
        rw [ite_eq_right (Nat.succ_ne_zero i), ite_eq_right (Nat.succ_ne_zero (i + 1)),
          Fr.powNat_succ x (i + 1), ← Fr.mul_assoc]

/-- `computePowers x n` is `[x^0, x^1, ..., x^(n-1)]`, as its docstring
claims. -/
theorem getElem_computePowers (x : Fr) (n i : Nat)
    (h : i < (computePowers x n).size) :
    (computePowers x n)[i] = Fr.powNat x i := by
  have hl : i < (computePowersAux x Fr.one n).length := by
    simpa [computePowers] using h
  show (computePowersAux x Fr.one n).toArray[i] = _
  rw [List.getElem_toArray, getElem_computePowersAux x Fr.one n i hl]
  cases i with
  | zero => rw [ite_eq_left rfl, Fr.powNat_zero]
  | succ i =>
    rw [ite_eq_right (Nat.succ_ne_zero i), Fr.powNat_succ, Fr.one_mul_mul,
      ← Fr.powNat_succ]

/-- The divisibility guard in `computeRootsOfUnity` is logically the
identity: the function always computes the powers of the domain root. -/
theorem computeRootsOfUnity_def (order : Nat) :
    computeRootsOfUnity order =
      computePowers
        ((Fr.ofNat PRIMITIVE_ROOT_OF_UNITY) ^
          (Fr.ofNat ((BLS_MODULUS - 1) / order))) order := by
  rw [computeRootsOfUnity]
  split
  · rfl
  · exact panicWith_eq _ _

@[simp] theorem size_computeRootsOfUnity (order : Nat) :
    (computeRootsOfUnity order).size = order := by
  simp [computeRootsOfUnity_def]

/-- A successful `blobToPolynomialAux` returns exactly `count` elements. -/
theorem length_blobToPolynomialAux (blob : Blob) (i count : Nat)
    (l : List Fr) (h : blobToPolynomialAux blob i count = .ok l) :
    l.length = count := by
  induction count generalizing i l with
  | zero =>
    rw [blobToPolynomialAux] at h
    cases h
    rfl
  | succ count ih =>
    rw [blobToPolynomialAux] at h
    split at h
    · rename_i f hf
      cases hrec : blobToPolynomialAux blob (i + 1) count with
      | ok rest =>
        rw [hrec] at h
        cases h
        simp [ih (i + 1) rest hrec]
      | error e =>
        rw [hrec] at h
        cases h
    · cases h

/-- Element `j` of a successful `blobToPolynomialAux` decode is the
decoding of chunk `start + j`. -/
theorem getElem_blobToPolynomialAux (blob : Blob) (start count : Nat)
    (l : List Fr) (h : blobToPolynomialAux blob start count = .ok l)
    (j : Nat) (hj : j < l.length) :
    bytesToBlsField (blob.extract ((start + j) * BYTES_PER_FIELD_ELEMENT)
      ((start + j + 1) * BYTES_PER_FIELD_ELEMENT)) = .ok l[j] := by
  induction count generalizing start l j with
  | zero =>
    rw [blobToPolynomialAux] at h
    cases h
    exact absurd hj (by simp)
  | succ count ih =>
    rw [blobToPolynomialAux] at h
    split at h
    · rename_i f hf
      cases hrec : blobToPolynomialAux blob (start + 1) count with
      | ok rest =>
        rw [hrec] at h
        cases h
        cases j with
        | zero => simpa using hf
        | succ j =>
          have := ih (start + 1) rest hrec j (by simpa using hj)
          simpa [show start + 1 + j = start + (j + 1) by omega] using this
      | error e =>
        rw [hrec] at h
        cases h
    · cases h

/-- `blobToPolynomialAux` fails exactly with the index of the *first*
invalid chunk: that chunk does not decode, and every chunk before it
does. -/
theorem blobToPolynomialAux_error (blob : Blob) (start count : Nat)
    (e : KzgError) (h : blobToPolynomialAux blob start count = .error e) :
    ∃ j, start ≤ j ∧ j < start + count ∧
      e = .invalidFieldElement (some j) ∧
      (∀ f, bytesToBlsField (blob.extract (j * BYTES_PER_FIELD_ELEMENT)
        ((j + 1) * BYTES_PER_FIELD_ELEMENT)) ≠ .ok f) ∧
      (∀ k, start ≤ k → k < j →
        ∃ f, bytesToBlsField (blob.extract (k * BYTES_PER_FIELD_ELEMENT)
          ((k + 1) * BYTES_PER_FIELD_ELEMENT)) = .ok f) := by
  induction count generalizing start e with
  | zero =>
    rw [blobToPolynomialAux] at h
    cases h
  | succ count ih =>
    rw [blobToPolynomialAux] at h
    split at h
    · rename_i f hf
      cases hrec : blobToPolynomialAux blob (start + 1) count with
      | ok rest =>
        rw [hrec] at h
        cases h
      | error e' =>
        rw [hrec] at h
        cases h
        obtain ⟨j, hj1, hj2, hj3, hj4, hj5⟩ := ih (start + 1) e hrec
        refine ⟨j, by omega, by omega, hj3, hj4, fun k hk1 hk2 => ?_⟩
        rcases Nat.eq_or_lt_of_le hk1 with rfl | hk
        · exact ⟨f, hf⟩
        · exact hj5 k hk hk2
    · rename_i herr
      cases h
      refine ⟨start, Nat.le_refl _, by omega, rfl, fun f hf => ?_,
        fun k hk1 hk2 => absurd (Nat.lt_of_le_of_lt hk1 hk2)
          (Nat.lt_irrefl _)⟩
      rw [herr] at hf
      cases hf

/-- A successful `blobToPolynomial` returns exactly
`FIELD_ELEMENTS_PER_BLOB` field elements. -/
theorem size_blobToPolynomial (blob : Blob) (poly : Polynomial)
    (h : blobToPolynomial blob = .ok poly) :
    poly.size = FIELD_ELEMENTS_PER_BLOB := by
  rw [blobToPolynomial] at h
  split at h
  · cases h
  · generalize FIELD_ELEMENTS_PER_BLOB = N at h ⊢
    cases hrec : blobToPolynomialAux blob 0 N with
    | ok l =>
      rw [hrec] at h
      cases h
      simpa using length_blobToPolynomialAux blob 0 N l hrec
    | error e =>
      rw [hrec] at h
      cases h

/-- Element `i` of a successful `blobToPolynomial` is the decoding of
the `i`-th 32-byte chunk of the blob. -/
theorem getElem_blobToPolynomial (blob : Blob) (poly : Polynomial)
    (h : blobToPolynomial blob = .ok poly) (i : Nat) (hi : i < poly.size) :
    bytesToBlsField (blob.extract (i * BYTES_PER_FIELD_ELEMENT)
      ((i + 1) * BYTES_PER_FIELD_ELEMENT)) = .ok poly[i] := by
  rw [blobToPolynomial] at h
  split at h
  · cases h
  · generalize FIELD_ELEMENTS_PER_BLOB = N at h
    cases hrec : blobToPolynomialAux blob 0 N with
    | ok l =>
      rw [hrec] at h
      cases h
      have hj : i < l.length := by simpa using hi
      have := getElem_blobToPolynomialAux blob 0 N l hrec i hj
      simpa using this
    | error e =>
      rw [hrec] at h
      cases h

/-- A `blobToPolynomial` failure with `invalidFieldElement (some j)`
means: the blob size was right, `j` is in range, chunk `j` does not
decode, and all chunks before `j` do. -/
theorem blobToPolynomial_error_invalidFieldElement (blob : Blob) (j : Nat)
    (h : blobToPolynomial blob = .error (.invalidFieldElement (some j))) :
    blob.size = BYTES_PER_BLOB ∧ j < FIELD_ELEMENTS_PER_BLOB ∧
      (∀ f, bytesToBlsField (blob.extract (j * BYTES_PER_FIELD_ELEMENT)
        ((j + 1) * BYTES_PER_FIELD_ELEMENT)) ≠ .ok f) ∧
      (∀ k, k < j →
        ∃ f, bytesToBlsField (blob.extract (k * BYTES_PER_FIELD_ELEMENT)
          ((k + 1) * BYTES_PER_FIELD_ELEMENT)) = .ok f) := by
  rw [blobToPolynomial] at h
  split at h
  · rename_i hsz
    cases h
  · rename_i hsz
    refine ⟨by omega, ?_⟩
    generalize hN : FIELD_ELEMENTS_PER_BLOB = N at h ⊢
    cases hrec : blobToPolynomialAux blob 0 N with
    | ok l =>
      rw [hrec] at h
      cases h
    | error e =>
      rw [hrec] at h
      cases h
      obtain ⟨j', _, hj2, hj3, hj4, hj5⟩ :=
        blobToPolynomialAux_error blob 0 N _ hrec
      cases hj3
      exact ⟨by omega, hj4, fun k hk => hj5 k (Nat.zero_le k) hk⟩

/-- `blobToPolynomial` fails with `badBlobSize` exactly when the blob has
the wrong size (and reports that size). -/
theorem blobToPolynomial_error_badBlobSize (blob : Blob) (n : Nat) :
    blobToPolynomial blob = .error (.badBlobSize n) ↔
      blob.size ≠ BYTES_PER_BLOB ∧ n = blob.size := by
  rw [blobToPolynomial]
  split
  · rename_i hsz
    constructor
    · intro h
      cases h
      exact ⟨hsz, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl
  · rename_i hsz
    constructor
    · intro h
      generalize FIELD_ELEMENTS_PER_BLOB = N at h
      cases hrec : blobToPolynomialAux blob 0 N with
      | ok l =>
        rw [hrec] at h
        cases h
      | error e =>
        rw [hrec] at h
        cases h
        obtain ⟨j, _, _, hj3, _, _⟩ :=
          blobToPolynomialAux_error blob 0 N _ hrec
        cases hj3
    · rintro ⟨hcontra, _⟩
      exact absurd hcontra hsz

@[simp] theorem size_rootsOfUnityBrp (size : Nat) :
    (rootsOfUnityBrp size).size = size := by
  simp [rootsOfUnityBrp, size_bitReversalPermutation]

/-- When `z` is the `i`-th element of `domain`, evaluation is a table
lookup. -/
theorem evaluatePolynomialInEvaluationFormAux_fastPath
    (polynomial domain : Array Fr) (z : Fr) (i : Nat)
    (h : domain.idxOf? z = some i) :
    evaluatePolynomialInEvaluationFormAux polynomial domain z
      = polynomial[i]! := by
  rw [evaluatePolynomialInEvaluationFormAux]
  simp only [h]

/-- When `z` is the `i`-th element of the evaluation domain, evaluating
the polynomial at `z` is a table lookup. -/
theorem evaluatePolynomialInEvaluationForm_fastPath
    (polynomial : Polynomial) (z : Fr) (i : Nat)
    (hsize : polynomial.size = FIELD_ELEMENTS_PER_BLOB)
    (h : (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).idxOf? z = some i) :
    evaluatePolynomialInEvaluationForm polynomial z = .ok polynomial[i]! := by
  rw [evaluatePolynomialInEvaluationForm, ite_eq_right (by simp [hsize])]
  exact congrArg Except.ok
    (evaluatePolynomialInEvaluationFormAux_fastPath polynomial _ z i h)


-- Proofs about barycentricSumAux and evaluation outside of the fast path--

/-- Base case of the barycentric-sum fold: with no remaining terms, the
accumulator is returned unchanged. Registered as `simp` so downstream
reasoning normalizes the empty-count case automatically. -/
@[simp] theorem barycentricSumAux_zero
    (polynomial domain : Array Fr) (z acc : Fr) (i : Nat) :
    barycentricSumAux polynomial domain z acc i 0 = acc := rfl

/-- The initial accumulator contributes additively to the barycentric fold:
adding `extra` to the starting accumulator is the same as adding `extra` to
the final result. -/
theorem barycentricSumAux_acc_add
    (polynomial domain : Array Fr) (z acc extra : Fr) (i count : Nat) :
    barycentricSumAux polynomial domain z (acc + extra) i count =
      barycentricSumAux polynomial domain z acc i count + extra := by
  induction count generalizing acc i with
  | zero => rfl
  | succ n ih =>
    simp only [barycentricSumAux]
    rw [Fr.add_right_comm]
    exact ih _ _

/-- Splitting the count decomposes the fold: summing over `a + b` terms
starting at `i` equals summing over the first `a` (yielding some
intermediate accumulator), then summing over the next `b` starting at
`i + a`. The workhorse for reasoning about `barycentricSumAux`
inductively. -/
theorem barycentricSumAux_add
    (polynomial domain : Array Fr) (z acc : Fr) (i a b : Nat) :
    barycentricSumAux polynomial domain z acc i (a + b) =
      barycentricSumAux polynomial domain z
        (barycentricSumAux polynomial domain z acc i a) (i + a) b := by
  induction a generalizing acc i with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + b = (n + b) + 1 from by omega]
    simp only [barycentricSumAux]
    rw [ih, show i + 1 + n = i + (n + 1) from by omega]

/-- Direct recursive form of the barycentric sum: the sum of chunks
`polynomial[i]! * domain[i]! / (z - domain[i]!)` for `i ∈ [0, n)`.
Structurally a "sum from the right" — expressing the intended
mathematical shape of `barycentricSumAux`. -/
def barycentricRefSum (polynomial domain : Array Fr) (z : Fr) : Nat → Fr
  | 0 => Fr.zero
  | n + 1 => barycentricRefSum polynomial domain z n +
             polynomial[n]! * domain[n]! / (z - domain[n]!)

/-- `barycentricSumAux` starting from `Fr.zero` at index `0` equals the
direct sum `barycentricRefSum`. This is the mathematically natural
formulation the docstring on `evaluatePolynomialInEvaluationFormAux`
refers to. -/
theorem barycentricSumAux_zero_eq_refSum
    (polynomial domain : Array Fr) (z : Fr) (n : Nat) :
    barycentricSumAux polynomial domain z Fr.zero 0 n =
      barycentricRefSum polynomial domain z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [barycentricSumAux_add polynomial domain z Fr.zero 0 n 1]
    simp only [barycentricSumAux, Nat.zero_add]
    rw [ih]
    rfl

/-- Given the inverse of every visited `z - domain[k]`, the sum with inverses is the barycentric sum.

Each term `a / b` is `a * b.inverse` by definition, so the two folds take the same steps. -/
theorem barycentricSumInvAux_eq (polynomial domain inverses : Array Fr) (z acc : Fr) (i count : Nat)
    (h : ∀ k, i ≤ k → k < i + count → inverses[k]! = (z - domain[k]!).inverse) :
    barycentricSumInvAux polynomial domain inverses acc i count =
      barycentricSumAux polynomial domain z acc i count := by
  induction count generalizing acc i with
  | zero => rfl
  | succ n ih =>
    simp only [barycentricSumInvAux, barycentricSumAux]
    rw [h i (Nat.le_refl i) (by omega)]
    exact ih _ _ (fun k hk1 hk2 => h k (by omega) (by omega))

end EthLib.Cryptography.Kzg
