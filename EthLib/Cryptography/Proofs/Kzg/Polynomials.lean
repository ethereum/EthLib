module

public import EthLib.Base.Proofs.MapM
public import EthLib.Cryptography.Kzg.Polynomials
public import EthLib.Cryptography.Proofs.Bls.Fr
public import EthLib.Cryptography.Proofs.Kzg.BitReversal

/-!
# Proofs: the polynomial helpers

The conversions between bytes and field elements round trip.

The powers helper returns powers.

The decoding of a blob is described on its success and its failure paths.

Evaluation at a domain point is a table lookup.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Base (Bytes32)
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal

/-! ## Folds over the indices of an array -/

/-- The indices of `Array.finRange n`, as numbers, are `List.range n`. -/
theorem map_val_toList_finRange (n : Nat) :
    (Array.finRange n).toList.map Fin.val = List.range n := by
  apply List.ext_getElem (by simp [Array.finRange])
  intro i h1 h2
  simp [Array.finRange]

/-- A fold over `Array.finRange n` that reads only index values is a fold over `List.range n`. -/
theorem foldl_finRange_eq_foldl_range {β : Type _} {n : Nat} (g : β → Fin n → β)
    (f : β → Nat → β) (hgf : ∀ r (i : Fin n), g r i = f r i.val) (init : β) :
    (Array.finRange n).foldl g init = (List.range n).foldl f init := by
  rw [← Array.foldl_toList, ← map_val_toList_finRange, List.foldl_map]
  exact congrArg (fun g => List.foldl g init _) (funext fun r => funext fun i => hgf r i)

/-- The monadic form of `foldl_finRange_eq_foldl_range`. -/
theorem foldlM_finRange_eq_foldlM_range {m : Type _ → Type _} [Monad m] [LawfulMonad m]
    {β : Type _} {n : Nat} (g : β → Fin n → m β) (f : β → Nat → m β)
    (hgf : ∀ r (i : Fin n), g r i = f r i.val) (init : β) :
    (Array.finRange n).foldlM g init = (List.range n).foldlM f init := by
  rw [← Array.foldlM_toList, ← map_val_toList_finRange, List.foldlM_map]
  exact congrArg (fun g => List.foldlM g init _) (funext fun r => funext fun i => hgf r i)

/-- A thrown error skips the rest of an `Except` computation.

The rejection theorems of the KZG operations rewrite with it. -/
theorem throw_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (throw e >>= f : Except ε β) = throw e :=
  rfl

/-- Decoding the encoding of `n` over `len` bytes recovers `n` modulo
`256 ^ len`. -/
theorem bytesToNat_intToBytesBE (n len : Nat) :
    Base.bytesToNat (intToBytesBE n len).data.toList = n % 256 ^ len := by
  induction len with
  | zero => simp [intToBytesBE, Base.bytesToNat, Nat.mod_one]
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
    rw [hdecomp, Base.bytesToNat_cons, hlen, hbyte, ih, Nat.pow_succ, Nat.mod_mul,
      Nat.mul_comm (n / 256 ^ len % 256)]
    exact Nat.add_comm _ _

/-- Decoding inverts encoding for values that fit in `len` bytes. -/
theorem bytesToNat_intToBytesBE_of_lt {n len : Nat}
    (h : n < 256 ^ len) :
    Base.bytesToNat (intToBytesBE n len).data.toList = n := by
  rw [bytesToNat_intToBytesBE, Nat.mod_eq_of_lt h]

/-- Encoding a decoded byte array at its own size gives back the same bytes.

Big-endian encoding has no slack once the length is fixed.
So any byte array is the canonical encoding of its own value.
-/
theorem intToBytesBE_bytesToNat (b : ByteArray) :
    intToBytesBE (Base.bytesToNat b.data.toList) b.size = b := by
  -- The decoded value fits in the size, so encoding then decoding returns it.
  -- Both arrays then have the same size and the same value, hence the same bytes.
  have fits : Base.bytesToNat b.data.toList < 256 ^ b.size := by
    simpa using Base.bytesToNat_lt b.data.toList
  refine ByteArray.ext (Array.ext' (Base.bytesToNat_inj ?_ ?_))
  · simp [intToBytesBE]
  · exact bytesToNat_intToBytesBE_of_lt fits

/-- A decoded field element is the big-endian value of its bytes.

That value is below the modulus. -/
theorem bytesToBlsField_ok {b : Bytes32} {f : Fr}
    (h : bytesToBlsField b = .ok f) :
    f.val = Base.bytesToNat b.toList ∧ f.val < Fr.modulus := by
  rw [bytesToBlsField] at h
  split at h
  · rename_i g hg
    cases h
    obtain ⟨_, hval, hlt⟩ := Bls.Fr.fromBytesBE_ok hg
    exact ⟨hval, hlt⟩
  · cases h

/-- A field element that the bytes decode to is the result of the KZG decoder. -/
private theorem bytesToBlsField_of_fromBytesBE {y : Bytes32} {x : Fr}
    (h : Fr.fromBytesBE ⟨y.toArray⟩ = .ok x) : bytesToBlsField y = .ok x := by
  unfold bytesToBlsField
  rw [h]

/-- Decoding the encoding of a field element gives it back. -/
@[simp] theorem bytesToBlsField_blsFieldToBytes (x : Fr) :
    bytesToBlsField (blsFieldToBytes x) = .ok x := by
  -- The decoder is opened on a variable, so the kernel never evaluates the encoding.
  have heta : ∀ b : ByteArray, (⟨b.data⟩ : ByteArray) = b := fun _ => rfl
  apply bytesToBlsField_of_fromBytesBE
  rw [show (blsFieldToBytes x).toArray = x.toBytesBE.data from rfl, heta,
    Bls.Fr.fromBytesBE_toBytesBE]

/-- Field element `i` of a flattened vector of 32-byte chunks is chunk `i`. -/
@[simp] theorem fieldElementBytes_flatten {k : Nat} (v : Vector Bytes32 k) (i : Fin k) :
    fieldElementBytes (k := k) v.flatten i = v[i] := by
  apply Vector.ext
  intro j hj
  have hdiv : (i.val * BYTES_PER_FIELD_ELEMENT + j) / 32 = i.val := by
    simp only [BYTES_PER_FIELD_ELEMENT]
    omega
  have hmod : (i.val * BYTES_PER_FIELD_ELEMENT + j) % 32 = j := by
    simp only [BYTES_PER_FIELD_ELEMENT]
    omega
  simp only [fieldElementBytes, Vector.getElem_ofFn]
  exact (Vector.getElem_flatten _).trans (by simp only [hdiv, hmod, Fin.getElem_fin])

/-- Relabelling the error fails exactly when the original fails. -/
private theorem mapError_eq_error {ε ε' α : Type} {g : ε → ε'} {x : Except ε α} {e' : ε'} :
    x.mapError g = .error e' ↔ ∃ e, x = .error e ∧ g e = e' := by
  cases x <;> simp [Except.mapError]

/-- The decoding loop, as a map over a list. -/
private theorem bytesToBlsFields_eq {k : Nat} (bytes : Vector UInt8 (k * BYTES_PER_FIELD_ELEMENT)) :
    bytesToBlsFields bytes = List.toArray <$> (Array.finRange k).toList.mapM
      (fun i => (bytesToBlsField (fieldElementBytes bytes i)).mapError
        fun _ => KzgError.invalidFieldElement (some i)) := by
  rw [bytesToBlsFields, Array.mapM_eq_mapM_toList]

/-- A successful decoding of `k` field elements returns `k` field elements. -/
theorem size_bytesToBlsFields {k : Nat} {bytes : Vector UInt8 (k * BYTES_PER_FIELD_ELEMENT)}
    {ys : Array Fr} (h : bytesToBlsFields bytes = .ok ys) : ys.size = k := by
  rw [bytesToBlsFields_eq] at h
  cases hl : (Array.finRange k).toList.mapM
      (fun i => (bytesToBlsField (fieldElementBytes bytes i)).mapError
        fun _ => KzgError.invalidFieldElement (some i)) with
  | error e => rw [hl] at h; cases h
  | ok l =>
    rw [hl] at h
    cases h
    simpa using Base.mapM_ok_length hl

/-- Element `i` of a successful decoding is the decoding of chunk `i`. -/
theorem getElem_bytesToBlsFields {k : Nat} {bytes : Vector UInt8 (k * BYTES_PER_FIELD_ELEMENT)}
    {ys : Array Fr} (h : bytesToBlsFields bytes = .ok ys) (i : Fin k) :
    bytesToBlsField (fieldElementBytes bytes i) =
      .ok (ys[i.val]'(by rw [size_bytesToBlsFields h]; exact i.isLt)) := by
  have hsize := size_bytesToBlsFields h
  rw [bytesToBlsFields_eq] at h
  cases hl : (Array.finRange k).toList.mapM
      (fun i => (bytesToBlsField (fieldElementBytes bytes i)).mapError
        fun _ => KzgError.invalidFieldElement (some i)) with
  | error e => rw [hl] at h; cases h
  | ok l =>
    rw [hl] at h
    cases h
    have hil : i.val < (Array.finRange k).toList.length := by simp
    have hstep := Base.mapM_ok_getElem hl i.val hil
    simp only [Array.getElem_toList, Array.getElem_finRange, Base.mapError_ok_iff] at hstep
    simpa using hstep

/-- A failed decoding names its first invalid chunk.

That chunk does not decode, and every chunk before it does. -/
theorem bytesToBlsFields_error {k : Nat} {bytes : Vector UInt8 (k * BYTES_PER_FIELD_ELEMENT)}
    {e : KzgError} (h : bytesToBlsFields bytes = .error e) :
    ∃ j : Fin k, e = .invalidFieldElement (some j.val) ∧
      (∀ f, bytesToBlsField (fieldElementBytes bytes j) ≠ .ok f) ∧
      ∀ i : Fin k, i < j → ∃ f, bytesToBlsField (fieldElementBytes bytes i) = .ok f := by
  rw [bytesToBlsFields_eq] at h
  cases hl : (Array.finRange k).toList.mapM
      (fun i => (bytesToBlsField (fieldElementBytes bytes i)).mapError
        fun _ => KzgError.invalidFieldElement (some i)) with
  | ok l => rw [hl] at h; cases h
  | error e' =>
    rw [hl] at h
    cases h
    obtain ⟨j, hj, hfail, hbefore⟩ := Base.mapM_error hl
    have hjk : j < k := by simpa using hj
    simp only [Array.getElem_toList, Array.getElem_finRange, mapError_eq_error] at hfail
    obtain ⟨e₀, he₀, rfl⟩ := hfail
    refine ⟨⟨j, hjk⟩, rfl, fun f hf => ?_, fun i hij => ?_⟩
    · have : bytesToBlsField (fieldElementBytes bytes ⟨j, hjk⟩) = .error e₀ := by
        simpa using he₀
      rw [this] at hf
      cases hf
    · obtain ⟨y, hy⟩ := hbefore i.val hij
      simp only [Array.getElem_toList, Array.getElem_finRange, Base.mapError_ok_iff] at hy
      exact ⟨y, by simpa using hy⟩

/-- The decoding succeeds when every chunk decodes.

It then returns the decoded values. -/
theorem bytesToBlsFields_eq_ok {k : Nat} {bytes : Vector UInt8 (k * BYTES_PER_FIELD_ELEMENT)}
    (g : Fin k → Fr) (h : ∀ i, bytesToBlsField (fieldElementBytes bytes i) = .ok (g i)) :
    bytesToBlsFields bytes = .ok (Array.ofFn g) := by
  rw [bytesToBlsFields_eq, Base.mapM_eq_ok_map (g := g) fun i _ => Base.mapError_ok_iff.mpr (h i)]
  show Except.ok _ = _
  congr 1
  apply Array.ext
  · simp
  · intro i _ _
    simp

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

private theorem dite_lt_size_getElem! (p : PolynomialCoeff) (i : Nat) :
    (if h : i < p.size then p[i] else Fr.zero) = p[i]! := by
  by_cases h : i < p.size
  · rw [dite_eq_left h, getElem!_pos p i h]
  · rw [dite_eq_right h, getElem!_of_ge_size p h]

/-- Coefficient `i` of `addPolynomialcoeff a b` is `a[i]! + b[i]!` for all `i`
(since out-of-bounds accesses default to `Fr.zero`). -/
@[simp] theorem addPolynomialcoeff_getElem! (a b : PolynomialCoeff) (i : Nat) :
    (addPolynomialcoeff a b)[i]! = a[i]! + b[i]! := by
  rw [addPolynomialcoeff]
  by_cases hab : a.size ≥ b.size
  · rw [ite_eq_left hab]
    dsimp only []
    by_cases hi : i < a.size
    · rw [getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn]
      simp only [Fin.getElem_fin]
      rw [getElem!_pos a i hi, dite_lt_size_getElem!]
    · have hib : ¬ i < b.size := by omega
      rw [getElem!_of_ge_size _ (by simp [hi]),
          getElem!_of_ge_size a hi, getElem!_of_ge_size b hib]
      exact (Fr.add_zero _).symm
  · rw [ite_eq_right hab]
    dsimp only []
    by_cases hi : i < b.size
    · rw [getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn]
      simp only [Fin.getElem_fin]
      rw [getElem!_pos b i hi, Fr.add_comm, dite_lt_size_getElem!]
    · have hia : ¬ i < a.size := by omega
      rw [getElem!_of_ge_size _ (by simp [hi]),
          getElem!_of_ge_size a hia, getElem!_of_ge_size b hi]
      exact (Fr.add_zero _).symm


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
  | zero => exact (Fr.add_zero _).symm
  | succ n ih =>
    simp only [evalCoeffPolyAux, ih, addPolynomialcoeff_getElem!, Fr.add_mul]
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
          Fr.zero_mul, Fr.add_zero]

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

private def mulFoldStep (a b : PolynomialCoeff) (r : PolynomialCoeff)
    (power : Nat) : PolynomialCoeff :=
  let coef := a[power]!
  let summand : PolynomialCoeff :=
    Array.replicate power Fr.zero ++ b.map (· * coef)
  addPolynomialcoeff r summand

/-- The product's fold, with the coefficient read under its bound, is the fold of `mulFoldStep`. -/
private theorem multiplyFold_eq (a b : PolynomialCoeff) :
    (Array.finRange a.size).foldl (init := #[Fr.zero]) (fun r power =>
      addPolynomialcoeff r (Array.replicate power.val Fr.zero ++ b.map (· * a[power]))) =
    (List.range a.size).foldl (mulFoldStep a b) #[Fr.zero] :=
  foldl_finRange_eq_foldl_range _ _ (fun r i => by
    simp only [mulFoldStep, Fin.getElem_fin, getElem!_pos a i.val i.isLt]) _

/-- A product within the size bound is the fold of `mulFoldStep`. -/
private theorem multiplyPolynomialcoeff_eq_fold {a b : PolynomialCoeff}
    (h : ¬ a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB) :
    multiplyPolynomialcoeff a b = .ok ((List.range a.size).foldl (mulFoldStep a b) #[Fr.zero]) := by
  rw [multiplyPolynomialcoeff, ite_eq_right h, ← multiplyFold_eq]
  rfl

/-- Multiplying an empty left polynomial by a bounded right polynomial returns `#[Fr.zero]`. -/
@[simp] theorem multiplyPolynomialcoeff_empty_left {b : PolynomialCoeff}
    (hb : b.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB) :
    multiplyPolynomialcoeff #[] b = .ok #[Fr.zero] := by
  have hnot : ¬ ((#[] : PolynomialCoeff).size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB) := by
    simp
    omega
  rw [multiplyPolynomialcoeff_eq_fold hnot]
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
    rw [hm, hn, hmn, Fr.add_zero]

/-- `multiplyPolynomialcoeff` rejects polynomials whose combined length
exceeds `FIELD_ELEMENTS_PER_EXT_BLOB`. -/
theorem multiplyPolynomialcoeff_too_large {a b : PolynomialCoeff}
    (h : a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB) :
    multiplyPolynomialcoeff a b =
      .error (.polynomialProductTooLong a.size b.size) := by
  unfold multiplyPolynomialcoeff
  rw [ite_eq_left h]
  rfl

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
  rw [multiplyPolynomialcoeff_eq_fold hnot, foldl_mulFoldStep_empty_right]

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
  by_cases hgt : a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB
  · rw [multiplyPolynomialcoeff, ite_eq_left hgt] at h
    cases h
  · rw [multiplyPolynomialcoeff_eq_fold hgt] at h
    injection h with hp
    subst hp
    rw [size_foldl_mulFoldStep a b a.size]
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
  by_cases hgt : a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB
  · rw [multiplyPolynomialcoeff, ite_eq_left hgt] at h
    cases h
  · rw [multiplyPolynomialcoeff_eq_fold hgt] at h
    injection h with hp
    subst hp
    obtain ⟨k, hk⟩ : ∃ k, a.size = k + 1 := ⟨a.size - 1, by omega⟩
    rw [hk, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hidx : k + 1 + b.size - 2 = k + b.size - 1 := by omega
    have hsub : k + 1 - 1 = k := by omega
    rw [hidx, hsub, mulFoldStep, addPolynomialcoeff_getElem!,
        getElem!_foldl_mulFoldStep_before_top a b hb0 k, Fr.zero_add]
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
        exact Fr.one_mul _
      obtain ⟨hsz, hld⟩ := ih q (by omega) hq_lead h
      refine ⟨?_, hld⟩
      simp only [hsz, hq_sz, List.length_cons]
      omega

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

private theorem fr_powNat_add (x : Fr) (a b : Nat) :
    Fr.powNat x (a + b) = Fr.powNat x a * Fr.powNat x b := by
  induction b with
  | zero =>
    rw [Nat.add_zero, Fr.powNat_zero, Fr.mul_one]
  | succ b ih =>
    rw [Nat.add_succ, Fr.powNat_succ, Fr.powNat_succ, ih,
        ← Fr.mul_assoc, Fr.mul_comm x (Fr.powNat x a), Fr.mul_assoc]

private theorem map_mul_getElem! (b : PolynomialCoeff) (c : Fr) (n : Nat) :
    (b.map (· * c))[n]! = b[n]! * c := by
  by_cases hn : n < b.size
  · rw [getElem!_pos _ n (by simp [hn]), getElem!_pos b n hn, Array.getElem_map]
  · rw [getElem!_of_ge_size _ (by simp [hn]), getElem!_of_ge_size b hn, Fr.zero_mul]

private theorem evalCoeffPolyAux_scale_right (b : PolynomialCoeff) (c x : Fr) (n : Nat) :
    evalCoeffPolyAux (b.map (· * c)) x n = evalCoeffPolyAux b x n * c := by
  induction n with
  | zero =>
    simp [evalCoeffPolyAux, Fr.zero_mul]
  | succ n ih =>
    simp only [evalCoeffPolyAux, ih, map_mul_getElem!]
    rw [Fr.add_mul, Fr.mul_assoc, Fr.mul_comm c (Fr.powNat x n), ← Fr.mul_assoc]

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
        Fr.zero_mul, Fr.add_zero]

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
        evalCoeffPolyAux, Fr.zero_mul]
  | succ m ih =>
    rw [Nat.add_succ, evalCoeffPolyAux, ih, evalCoeffPolyAux,
        replicate_zero_append_getElem!_add, Fr.add_mul,
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
  rw [h0, Fr.zero_mul, Fr.add_zero]

private theorem evalCoeffPoly_foldl_mulFoldStep (a b : PolynomialCoeff) (x : Fr) (k : Nat) :
    evalCoeffPoly ((List.range k).foldl (mulFoldStep a b) #[Fr.zero]) x =
      evalCoeffPolyAux a x k * evalCoeffPoly b x := by
  induction k with
  | zero =>
    simp [evalCoeffPoly_zero_singleton, evalCoeffPolyAux, Fr.zero_mul]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        mulFoldStep, evalCoeffPoly_addPolynomialcoeff, ih,
        evalCoeffPoly_replicate_zero_append, evalCoeffPoly_scale_right,
        evalCoeffPolyAux, Fr.add_mul]
    congr 1
    rw [Fr.mul_assoc, Fr.mul_comm (evalCoeffPoly b x)]

/-- Evaluating the product of two coefficient-form polynomials at `x` equals the
product of their evaluations at `x`. -/
theorem evalPolyAt_mulPoly {a b p : PolynomialCoeff} (x : Fr)
    (h : multiplyPolynomialcoeff a b = .ok p) :
    evalPolyAt p x = evalPolyAt a x * evalPolyAt b x := by
  by_cases hgt : a.size + b.size > FIELD_ELEMENTS_PER_EXT_BLOB
  · rw [multiplyPolynomialcoeff, ite_eq_left hgt] at h
    cases h
  · rw [multiplyPolynomialcoeff_eq_fold hgt] at h
    injection h with hp
    subst hp
    change evalCoeffPoly _ x = _
    rw [evalCoeffPoly_foldl_mulFoldStep]
    rfl

private theorem evalPolyAt_linear_factor_self (z : Fr) :
    evalPolyAt #[-z, Fr.one] z = Fr.zero := by
  show (Fr.zero + (#[-z, Fr.one] : PolynomialCoeff)[0]! * Fr.powNat z 0) +
       (#[-z, Fr.one] : PolynomialCoeff)[1]! * Fr.powNat z 1 = Fr.zero
  have h0 : (#[-z, Fr.one] : PolynomialCoeff)[0]! = -z := rfl
  have h1 : (#[-z, Fr.one] : PolynomialCoeff)[1]! = Fr.one := rfl
  have hp1 : Fr.powNat z 1 = z := by
    rw [Fr.powNat_succ, Fr.powNat_zero, Fr.mul_one]
  rw [h0, h1, Fr.powNat_zero, hp1, Fr.zero_add, Fr.mul_one, Fr.one_mul, Fr.neg_add_cancel]

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
        rw [evalPolyAt_mulPoly z hq, hz, Fr.zero_mul]
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
          rw [evalPolyAt_mulPoly z hq, evalPolyAt_linear_factor_self, Fr.mul_zero]
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
  · simp [dividePolynomialcoeff, h, throw, throwThe, MonadExceptOf.throw]
  · have hnotlt : ¬ a.size < b.size := by omega
    by_cases hb0 : b.size = 0
    · simp [dividePolynomialcoeff, hb0, throw, throwThe, MonadExceptOf.throw]
    · have hz : (b[b.size - 1]'(by omega)).isZero = true := by
        rw [← getElem!_pos b _ (by omega)]
        exact hzero
      simp [dividePolynomialcoeff, hb0, hnotlt, hz, Bind.bind, Except.bind,
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
  rw [dite_eq_left h]
  rfl

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

/-- `computeRootsOfUnity` computes the powers of the domain root. -/
theorem computeRootsOfUnity_def (order : Nat) :
    computeRootsOfUnity order =
      computePowers
        ((Fr.ofNat PRIMITIVE_ROOT_OF_UNITY) ^
          (Fr.ofNat ((BLS_MODULUS - 1) / order))) order := by
  rfl

/-- A successful `blobToPolynomial` returns exactly
`FIELD_ELEMENTS_PER_BLOB` field elements. -/
theorem size_blobToPolynomial (blob : Blob) (poly : Polynomial)
    (h : blobToPolynomial blob = .ok poly) :
    poly.size = FIELD_ELEMENTS_PER_BLOB :=
  size_bytesToBlsFields (k := FIELD_ELEMENTS_PER_BLOB) h

/-- Element `i` of a decoded blob is the decoding of the `i`-th 32-byte chunk. -/
theorem getElem_blobToPolynomial (blob : Blob) (poly : Polynomial)
    (h : blobToPolynomial blob = .ok poly) (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    bytesToBlsField (fieldElementBytes (k := FIELD_ELEMENTS_PER_BLOB) blob i) =
      .ok (poly[i.val]'(by rw [size_blobToPolynomial blob poly h]; exact i.isLt)) :=
  getElem_bytesToBlsFields (k := FIELD_ELEMENTS_PER_BLOB) h i

/-- A failed decoding of a blob names its first invalid chunk `j`.

Chunk `j` does not decode, and all chunks before `j` do. -/
theorem blobToPolynomial_error (blob : Blob) {e : KzgError}
    (h : blobToPolynomial blob = .error e) :
    ∃ j : Fin FIELD_ELEMENTS_PER_BLOB, e = .invalidFieldElement (some j.val) ∧
      (∀ f, bytesToBlsField (fieldElementBytes (k := FIELD_ELEMENTS_PER_BLOB) blob j) ≠ .ok f) ∧
      ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, i < j →
        ∃ f, bytesToBlsField (fieldElementBytes (k := FIELD_ELEMENTS_PER_BLOB) blob i) = .ok f :=
  bytesToBlsFields_error (k := FIELD_ELEMENTS_PER_BLOB) h

/-! ## Evaluation in evaluation form -/

/-- The barycentric sum `Σ_j p[i+j] * D[i+j] / (z - D[i+j])` of `count` terms.

It adds the terms from left to right onto `acc`.

A zero denominator would add `0`, since division in `Fr` by `0` gives `0`. -/
def barycentricSumAux (polynomial domain : Array Fr) (z : Fr) :
    Fr → Nat → Nat → Fr
  | acc, _, 0 => acc
  | acc, i, count + 1 =>
    let a := polynomial[i]! * domain[i]!
    let b := z - domain[i]!
    barycentricSumAux polynomial domain z (acc + a / b) (i + 1) count

/-- The barycentric sum, with the inverses of `z - D[i]` given. -/
def barycentricSumInvAux (polynomial domain inverses : Array Fr) :
    Fr → Nat → Nat → Fr
  | acc, _, 0 => acc
  | acc, i, count + 1 =>
    barycentricSumInvAux polynomial domain inverses
      (acc + polynomial[i]! * domain[i]! * inverses[i]!) (i + 1) count

/-- A fold over an array is a fold over its indices, reading each entry with a default. -/
theorem foldl_eq_foldl_range_getElem! {α β : Type _} [Inhabited α] (f : β → α → β)
    (arr : Array α) (init : β) :
    arr.foldl f init = (List.range arr.size).foldl (fun acc k => f acc arr[k]!) init := by
  have hl : arr.toList = (List.range arr.size).map (arr[·]!) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [getElem!_pos arr i (by simpa using h1)]
  rw [← Array.foldl_toList, hl, List.foldl_map]

/-- The sum with inverses, from index `i`, is a fold over the indices `i` to `i + count - 1`. -/
theorem barycentricSumInvAux_eq_foldl (polynomial domain inverses : Array Fr) (count : Nat) :
    ∀ acc i, barycentricSumInvAux polynomial domain inverses acc i count =
      (List.range' i count).foldl
        (fun acc k => acc + polynomial[k]! * domain[k]! * inverses[k]!) acc := by
  induction count with
  | zero => intro acc i; rfl
  | succ n ih =>
    intro acc i
    rw [List.range'_succ, List.foldl_cons, ← ih]
    rfl

/-- The fold of the evaluation over its triples is the sum with inverses. -/
theorem foldl_zip_zip_eq_barycentricSumInvAux (polynomial domain inverses : Array Fr)
    (hpd : polynomial.size = domain.size) (hinv : inverses.size = polynomial.size) (acc : Fr) :
    ((polynomial.zip domain).zip inverses).foldl (init := acc) (fun acc ((y, d), inv) =>
      acc + y * d * inv) =
      barycentricSumInvAux polynomial domain inverses acc 0 polynomial.size := by
  rw [foldl_eq_foldl_range_getElem!, barycentricSumInvAux_eq_foldl, ← List.range_eq_range']
  simp only [Array.size_zip, hpd, hinv, Nat.min_self]
  apply List.foldl_ext
  intro r k hk
  have hk' : k < domain.size := List.mem_range.mp hk
  rw [getElem!_pos _ k (by simp [hpd, hinv]; omega)]
  simp only [Array.getElem_zip]
  rw [getElem!_pos polynomial k (by omega), getElem!_pos domain k hk',
    getElem!_pos inverses k (by omega)]

/-- When `z` is the `i`-th element of `domain`, evaluation is a table
lookup. -/
theorem evaluatePolynomialInEvaluationFormAux_fastPath
    (polynomial domain : Array Fr) (z : Fr) (i : Nat)
    (hsize : polynomial.size = domain.size)
    (h : domain.idxOf? z = some i) :
    evaluatePolynomialInEvaluationFormAux polynomial domain z
      = polynomial[i]! := by
  rw [Array.idxOf?_eq_map_finIdxOf?_val, Option.map_eq_some_iff] at h
  obtain ⟨fi, hfi, rfl⟩ := h
  obtain ⟨hdi, hbefore⟩ := Array.finIdxOf?_eq_some_iff.mp hfi
  have hi : fi.val < polynomial.size := by have := fi.isLt; omega
  have hfind : (polynomial.zip domain).find? (·.2 == z) =
      some (polynomial[fi.val], domain[fi]) := by
    rw [Array.find?_eq_some_iff_getElem]
    refine ⟨by simp [hdi], fi.val, by simp [hi], by simp [Array.getElem_zip], fun j hj => ?_⟩
    simpa [Array.getElem_zip] using hbefore ⟨j, Nat.lt_trans hj fi.isLt⟩ hj
  rw [evaluatePolynomialInEvaluationFormAux]
  simp only [hfind]
  rw [getElem!_pos polynomial _ hi]

/-- When `z` is the `i`-th element of the evaluation domain, evaluating
the polynomial at `z` is a table lookup. -/
theorem evaluatePolynomialInEvaluationForm_fastPath
    (polynomial : Polynomial) (z : Fr) (i : Nat)
    (hsize : polynomial.size = FIELD_ELEMENTS_PER_BLOB)
    (h : (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).idxOf? z = some i) :
    evaluatePolynomialInEvaluationForm polynomial z = .ok polynomial[i]! := by
  rw [evaluatePolynomialInEvaluationForm, ite_eq_right (by simp [hsize])]
  exact congrArg Except.ok
    (evaluatePolynomialInEvaluationFormAux_fastPath polynomial _ z i
      (by rw [hsize, size_rootsOfUnityBrp]) h)

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
