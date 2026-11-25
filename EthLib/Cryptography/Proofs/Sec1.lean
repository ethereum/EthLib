module

public import EthLib.Cryptography.Sec1
public import EthLib.Cryptography.Proofs.Jacobian
public import EthLib.Base.Proofs.ByteOrder
public import EthLib.Base.Proofs.Except
public import EthLib.Base.Proofs.Pow

/-!
# Proofs: SEC 1 point encoding

Decoding inverts encoding on the points of the curve, in both forms.

Octets decode to a point exactly when they are one of its encodings, so the encoding is canonical.

Decompression finds the point of the requested parity exactly when one exists.
-/

@[expose] public section

namespace EthLib.Cryptography.Sec1

open ShortWeierstrass (Point)
open ShortWeierstrass.Point (rhs)

variable {p : Nat}

/-- The law of a square root: it returns a root of each square, and `none` for each non-square. -/
structure IsSqrt (sqrt? : Fin p → Option (Fin p)) : Prop where
  /-- A returned value is a root. -/
  root : ∀ {α β : Fin p}, sqrt? α = some β → β * β = α
  /-- `none` comes only for an element with no root. -/
  complete : ∀ {α : Fin p}, sqrt? α = none → ∀ β : Fin p, β * β ≠ α

/-- The candidate `α^((p + 1) / 4)` squares to `α` when `α` is a square, for a prime `p`. -/
private theorem pow_mul_pow_of_mul_self [Fact p.Prime] (h3 : p % 4 = 3) (γ : ZMod p) :
    (γ * γ) ^ ((p + 1) / 4) * (γ * γ) ^ ((p + 1) / 4) = γ * γ := by
  have h4 : 4 * ((p + 1) / 4) = p + 1 := by omega
  rw [← pow_add, ← pow_two, ← pow_mul, ← two_mul, ← mul_assoc, show 2 * 2 = 4 from rfl, h4,
    pow_succ, ZMod.pow_card, pow_two]

/-- The square root for `p = 3 mod 4` obeys the law, for a prime `p`. -/
theorem isSqrt_sqrt3Mod4 [NeZero p] [Fact p.Prime] (h3 : p % 4 = 3) :
    IsSqrt (sqrt3Mod4 (p := p)) := by
  refine ⟨fun {α β} h => ?_, fun {α} h γ hγ => ?_⟩
  · unfold sqrt3Mod4 at h
    dsimp only at h
    split_ifs at h with hβ
    cases h
    exact hβ
  · unfold sqrt3Mod4 at h
    dsimp only at h
    split_ifs at h with hβ
    apply hβ
    have he : (p + 1) / 4 < 2 ^ (p.log2 + 1) := by
      have := Nat.lt_log2_self (n := p)
      omega
    rw [Base.powBits_eq_pow _ _ _ he, ← hγ]
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := NeZero.ne p; omega⟩
    exact pow_mul_pow_of_mul_self h3 (γ : ZMod (n + 1))

/-! ## Field elements -/

section Field

variable (params : Params p)

/-- A field element takes `mlen` octets. -/
theorem size_fieldToBytes (a : Fin p) : (fieldToBytes params a).size = params.mlen := by
  simp [fieldToBytes, ByteArray.size]

/-- The octets of a field element hold its integer. -/
theorem ofBE_fieldToBytes (a : Fin p) :
    Base.ByteOrder.ofBE (fieldToBytes params a).data.toList = a.val := by
  simp only [fieldToBytes]
  exact Base.ByteOrder.ofBE_toBE_of_lt (Nat.lt_of_lt_of_le a.isLt params.fits)

/-- Octets read as a field element exactly when they are its encoding. -/
theorem fieldOfBytes?_eq_some_iff {M : ByteArray} {a : Fin p} :
    fieldOfBytes? params M = some a ↔ M = fieldToBytes params a := by
  constructor
  · intro h
    unfold fieldOfBytes? at h
    split_ifs at h with hs hlt
    cases h
    obtain ⟨d⟩ := M
    simp only [fieldToBytes, ByteArray.mk.injEq]
    apply Array.toList_inj.mp
    exact (Base.ByteOrder.toList_toBE_ofBE_of_length hs).symm
  · rintro rfl
    simp only [fieldOfBytes?, size_fieldToBytes, ofBE_fieldToBytes, a.isLt, ↓reduceIte, dite_true]

/-- The octets of a field element read back as that element. -/
theorem fieldOfBytes?_fieldToBytes (a : Fin p) :
    fieldOfBytes? params (fieldToBytes params a) = some a :=
  (fieldOfBytes?_eq_some_iff params).mpr rfl

/-- A field element takes at least one octet, since `p > 1`. -/
private theorem one_le_mlen : 1 ≤ params.mlen := by
  have hfits := params.fits
  have hmin := params.minimal
  rcases h : params.mlen with _ | m
  · rw [h] at hfits hmin
    simp at hfits hmin
    omega
  · omega

/-- The octets of a field element read back as that element. -/
private theorem readField_fieldToBytes (a : Fin p) :
    readField params (fieldToBytes params a) = .ok a := by
  simp only [readField, fieldOfBytes?_fieldToBytes]

/-- Octets read as a field element are its encoding. -/
private theorem eq_fieldToBytes_of_readField {X : ByteArray} {a : Fin p}
    (h : readField params X = .ok a) : X = fieldToBytes params a := by
  unfold readField at h
  cases hf : fieldOfBytes? params X with
  | none => rw [hf] at h; cases h
  | some b =>
    rw [hf] at h
    cases h
    exact (fieldOfBytes?_eq_some_iff params).mp hf

end Field

/-! ## Points -/

section Points

variable [NeZero p] [ShortWeierstrass.Params (Fin p)] (params : Params p)

omit [NeZero p] [ShortWeierstrass.Params (Fin p)] in
/-- The compressed form of a point other than `O` takes `mlen + 1` octets. -/
theorem size_encode_true (x y : Fin p) :
    (encode params true (.affine x y)).size = params.mlen + 1 := by
  simp only [encode, ↓reduceIte, ByteArray.size_append, size_fieldToBytes]
  change 1 + _ = _
  omega

omit [NeZero p] [ShortWeierstrass.Params (Fin p)] in
/-- The uncompressed form of a point other than `O` takes `2 mlen + 1` octets. -/
theorem size_encode_false (x y : Fin p) :
    (encode params false (.affine x y)).size = 2 * params.mlen + 1 := by
  simp only [encode, Bool.false_eq_true, ↓reduceIte, ByteArray.size_append, size_fieldToBytes]
  change 1 + _ + _ = _
  omega

variable {params}

/-- A root of the right-hand side gives a point of the curve. -/
private theorem isOnCurve_of_mul_self {x β : Fin p} (h : β * β = rhs x) :
    (Point.affine x β).isOnCurve = true := by
  simp [Point.isOnCurve, h]

omit [ShortWeierstrass.Params (Fin p)] in
/-- For an odd `p`, `β` and `-β` have opposite parities, unless `β = 0`. -/
private theorem val_neg_mod_two_ne (hp : p % 2 = 1) {β : Fin p} (hβ : β ≠ 0) :
    (-β).val % 2 ≠ β.val % 2 := by
  have h0 : β.val ≠ 0 := fun h => hβ (Fin.ext h)
  have := β.isLt
  rw [Fin.val_neg', Nat.mod_eq_of_lt (a := p - β.val) (b := p) (by omega)]
  omega

/-- Over a prime field, two roots of one square are equal or opposite. -/
private theorem eq_or_eq_neg_of_mul_self [Fact p.Prime] {y β : Fin p} (h : y * y = β * β) :
    y = β ∨ y = -β := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := NeZero.ne p; omega⟩
  have h' : ∀ a b : ZMod (n + 1), a * a = b * b → a = b ∨ a = -b :=
    fun _ _ => mul_self_eq_mul_self_iff.mp
  exact h' y β h

/-- Decompression returns a point of the curve with the given `x` and parity of `y`. -/
theorem exists_of_decompress_eq_ok (law : IsSqrt params.sqrt?) {x : Fin p} {ybit : Bool}
    {Q : Point (Fin p)} (h : decompress params x ybit = .ok Q) :
    ∃ y, Q = .affine x y ∧ (Point.affine x y).isOnCurve = true ∧ decide (y.val % 2 = 1) = ybit := by
  unfold decompress at h
  cases hs : params.sqrt? (rhs x) with
  | none => rw [hs] at h; cases h
  | some β =>
    rw [hs] at h
    have hon := law.root hs
    dsimp only at h
    split_ifs at h with hpar hβ
    · cases h
      exact ⟨β, rfl, isOnCurve_of_mul_self hon, hpar⟩
    · cases h
      refine ⟨-β, rfl, isOnCurve_of_mul_self (by rw [neg_mul_neg, hon]), ?_⟩
      have := val_neg_mod_two_ne params.odd hβ
      cases ybit <;> simp_all

/-- Decompression finds the point of the curve with the given `x` and parity of `y`, if any.

Over a prime field, it fails only when no such point exists. -/
theorem decompress_eq_ok_iff [Fact p.Prime] (law : IsSqrt params.sqrt?) {x : Fin p} {ybit : Bool}
    {Q : Point (Fin p)} :
    decompress params x ybit = .ok Q ↔
      ∃ y, Q = .affine x y ∧ (Point.affine x y).isOnCurve = true ∧
        decide (y.val % 2 = 1) = ybit := by
  refine ⟨exists_of_decompress_eq_ok law, ?_⟩
  rintro ⟨y, rfl, hc, hpar⟩
  have hy : y * y = rhs x := by simpa [Point.isOnCurve] using hc
  unfold decompress
  cases hs : params.sqrt? (rhs x) with
  | none => exact absurd hy (law.complete hs y)
  | some β =>
    dsimp only
    have hβy := eq_or_eq_neg_of_mul_self (hy.trans (law.root hs).symm)
    split_ifs with hb hβ
    · rcases hβy with rfl | rfl
      · rfl
      · by_cases hβ : β = 0
        · subst hβ
          rw [neg_zero]
        · have := val_neg_mod_two_ne params.odd hβ
          cases ybit <;> simp_all
    · subst hβ
      rcases hβy with rfl | rfl <;> simp_all
    · rcases hβy with rfl | rfl
      · exact absurd hpar hb
      · rfl

/-- An octet string is its first octet followed by the rest. -/
private theorem eq_append_extract {M : ByteArray} (h : 0 < M.size) :
    M = ⟨#[M[0]]⟩ ++ M.extract 1 M.size := by
  conv_lhs => rw [← ByteArray.extract_zero_size (b := M),
    ByteArray.extract_eq_extract_append_extract 1 (by omega) (by omega),
    ByteArray.extract_add_one (i := 0) (by omega)]
  rfl

/-- A single octet makes an array of size one. -/
private theorem size_singleton (b : UInt8) : (ByteArray.mk #[b]).size = 1 := rfl

/-- Each form of a point of the curve decodes back to that point. -/
theorem decode_encode [Fact p.Prime] (law : IsSqrt params.sqrt?) (compressed : Bool)
    {Q : Point (Fin p)} (hQ : Q.isOnCurve = true) :
    decode params (encode params compressed Q) = .ok Q := by
  have hm := one_le_mlen params
  cases Q with
  | infinity => cases compressed <;> rfl
  | affine x y =>
    cases compressed
    · have hsize := size_encode_false params x y
      unfold decode
      rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left hsize]
      have h0 : (encode params false (.affine x y))[0]'(by omega) = 4 := by
        simp only [encode, Bool.false_eq_true, ↓reduceIte]
        rw [ByteArray.getElem_append_left (by simp [size_singleton]),
          ByteArray.getElem_append_left (by simp [size_singleton])]
        rfl
      have hx : (encode params false (.affine x y)).extract 1 (params.mlen + 1) =
          fieldToBytes params x := by
        have hsx := size_fieldToBytes params x
        simp only [encode, Bool.false_eq_true, ↓reduceIte]
        ext1
        simp [hsx]
      have hy : (encode params false (.affine x y)).extract (params.mlen + 1)
          (encode params false (.affine x y)).size = fieldToBytes params y := by
        have hsx := size_fieldToBytes params x
        simp only [encode, Bool.false_eq_true, ↓reduceIte]
        exact ByteArray.extract_append_eq_right
          (by rw [ByteArray.size_append, size_singleton, hsx]; omega) ByteArray.size_append
      simp only [h0, hx, hy, readField_fieldToBytes, Base.ok_bind, hQ, ne_eq, not_true_eq_false,
        ↓reduceIte]
    · have hsize := size_encode_true params x y
      unfold decode
      rw [dite_eq_right (by omega), dite_eq_left hsize]
      have h0 : (encode params true (.affine x y))[0]'(by omega) =
          if y.val % 2 = 0 then 2 else 3 := by
        simp only [encode, ↓reduceIte]
        rw [ByteArray.getElem_append_left (by simp [size_singleton])]
        rfl
      have hx : (encode params true (.affine x y)).extract 1
          (encode params true (.affine x y)).size = fieldToBytes params x := by
        simp only [encode, ↓reduceIte]
        exact ByteArray.extract_append_eq_right rfl ByteArray.size_append
      have hd := decompress_eq_ok_iff law (x := x) (ybit := decide (y.val % 2 = 1))
        (Q := .affine x y) |>.mpr ⟨y, rfl, hQ, rfl⟩
      simp only [h0, hx, readField_fieldToBytes, Base.ok_bind]
      rcases Nat.mod_two_eq_zero_or_one y.val with h | h <;> simp_all

/-- The uncompressed form of a pair off the curve is rejected, by step 3.5. -/
theorem decode_encode_false_of_isOnCurve_eq_false {x y : Fin p}
    (h : (Point.affine x y).isOnCurve = false) :
    decode params (encode params false (.affine x y)) = .error .notOnCurve := by
  have hm := one_le_mlen params
  have hsize := size_encode_false params x y
  have hsx := size_fieldToBytes params x
  unfold decode
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left hsize]
  have h0 : (encode params false (.affine x y))[0]'(by omega) = 4 := by
    simp only [encode, Bool.false_eq_true, ↓reduceIte]
    rw [ByteArray.getElem_append_left (by simp [size_singleton]),
      ByteArray.getElem_append_left (by simp [size_singleton])]
    rfl
  have hx : (encode params false (.affine x y)).extract 1 (params.mlen + 1) =
      fieldToBytes params x := by
    simp only [encode, Bool.false_eq_true, ↓reduceIte]
    ext1
    simp [hsx]
  have hy : (encode params false (.affine x y)).extract (params.mlen + 1)
      (encode params false (.affine x y)).size = fieldToBytes params y := by
    simp only [encode, Bool.false_eq_true, ↓reduceIte]
    exact ByteArray.extract_append_eq_right
      (by rw [ByteArray.size_append, size_singleton, hsx]; omega) ByteArray.size_append
  simp only [h0, hx, hy, readField_fieldToBytes, Base.ok_bind, h, ne_eq, not_true_eq_false,
    ↓reduceIte, Bool.false_eq_true]

/-- Octets that decode to a point are one of its encodings, and the point is on the curve. -/
theorem exists_encode_of_decode_eq_ok (law : IsSqrt params.sqrt?) {M : ByteArray}
    {Q : Point (Fin p)} (h : decode params M = .ok Q) :
    Q.isOnCurve = true ∧ ∃ compressed, M = encode params compressed Q := by
  unfold decode at h
  split_ifs at h with h1 h0 h2 h3
  · cases h
    refine ⟨rfl, true, (eq_append_extract (by omega)).trans ?_⟩
    simp only [h0, h1, ByteArray.extract_same, ByteArray.append_empty]
    rfl
  · cases hr : readField params (M.extract 1 M.size) with
    | error e => rw [hr] at h; cases h
    | ok x =>
      rw [hr, Base.ok_bind] at h
      have hM := (eq_append_extract (M := M) (by omega)).trans
        (congrArg _ (eq_fieldToBytes_of_readField params hr))
      dsimp only at h
      split_ifs at h with hY2 hY3
      · obtain ⟨y, rfl, hc, hpar⟩ := exists_of_decompress_eq_ok law h
        refine ⟨hc, true, hM.trans ?_⟩
        have hy : y.val % 2 = 0 := by simp only [decide_eq_false_iff_not] at hpar; omega
        simp only [encode, ↓reduceIte, hY2, hy]
      · obtain ⟨y, rfl, hc, hpar⟩ := exists_of_decompress_eq_ok law h
        refine ⟨hc, true, hM.trans ?_⟩
        have hy : y.val % 2 = 1 := by simpa using hpar
        simp only [encode, ↓reduceIte, hY3, hy, Nat.one_ne_zero]
  · dsimp only at h
    split_ifs at h with hW
    cases hx : readField params (M.extract 1 (params.mlen + 1)) with
    | error e => rw [hx] at h; cases h
    | ok x =>
      cases hy : readField params (M.extract (params.mlen + 1) M.size) with
      | error e => rw [hx, Base.ok_bind, hy] at h; cases h
      | ok y =>
        rw [hx, Base.ok_bind, hy, Base.ok_bind] at h
        split_ifs at h with hc
        cases h
        refine ⟨hc, false, (eq_append_extract (by omega)).trans ?_⟩
        rw [ByteArray.extract_eq_extract_append_extract (params.mlen + 1) (by omega) (by omega),
          eq_fieldToBytes_of_readField params hx, eq_fieldToBytes_of_readField params hy,
          not_not.mp hW]
        simp only [encode, Bool.false_eq_true, ↓reduceIte, ByteArray.append_assoc]

/-- Octets decode to a point exactly when they are one of its encodings.

So decoding is canonical: no other octets decode to a point. -/
theorem decode_eq_ok_iff [Fact p.Prime] (law : IsSqrt params.sqrt?) {M : ByteArray}
    {Q : Point (Fin p)} :
    decode params M = .ok Q ↔ Q.isOnCurve = true ∧ ∃ compressed, M = encode params compressed Q :=
  ⟨exists_encode_of_decode_eq_ok law, fun ⟨hQ, _, hM⟩ => hM ▸ decode_encode law _ hQ⟩

/-- Two octet strings of one length that decode to one point are equal. -/
theorem eq_of_decode_eq_ok (law : IsSqrt params.sqrt?) {M1 M2 : ByteArray} {Q : Point (Fin p)}
    (h1 : decode params M1 = .ok Q) (h2 : decode params M2 = .ok Q) (size : M1.size = M2.size) :
    M1 = M2 := by
  obtain ⟨-, c1, rfl⟩ := exists_encode_of_decode_eq_ok law h1
  obtain ⟨-, c2, rfl⟩ := exists_encode_of_decode_eq_ok law h2
  have hm := one_le_mlen params
  cases Q with
  | infinity => cases c1 <;> cases c2 <;> rfl
  | affine x y =>
    cases c1 <;> cases c2
    · rfl
    · rw [size_encode_false, size_encode_true] at size
      omega
    · rw [size_encode_false, size_encode_true] at size
      omega
    · rfl

/-- Validation accepts a key exactly when it is not `O`, is on the curve, and has `n Q = O`.

The last check is skipped when the cofactor `h` is 1. -/
theorem validatePublicKey_eq_ok_iff {n h : Nat} {Q R : Point (Fin p)} :
    validatePublicKey n h Q = .ok R ↔
      R = Q ∧ Q ≠ .infinity ∧ Q.isOnCurve = true ∧
        (h = 1 ∨ Q.mulBits id ShortWeierstrass.Params.inv id ShortWeierstrass.Params.a
          (n.log2 + 1) n = .infinity) := by
  unfold validatePublicKey
  split_ifs with hinf hon hsub
  · simp [hinf]
  · simp_all
  · exact ⟨False.elim, fun ⟨_, _, _, hor⟩ => hor.elim hsub.1 hsub.2⟩
  · refine ⟨fun e => ⟨(Except.ok.inj e).symm, hinf, by simpa using hon, ?_⟩,
      fun ⟨e, _⟩ => e ▸ rfl⟩
    exact (not_and_or.mp hsub).imp not_not.mp not_not.mp

/-- Through a map of the field into a field, validation is §3.2.2.1 on the group of the curve.

It accepts exactly the points of the curve other than `O` with `n Q = O`.

The map is onto, so the group is that of the curve over `F_p`.

It assumes that the curve over `F_p` has `n` points when the cofactor is 1, as SEC 1 does. -/
theorem validatePublicKey_eq_ok_iff_nsmul {K : Type} [Field K] [DecidableEq K] {A B : K}
    [(ShortWeierstrass.curve A B).IsElliptic] {f : Fin p → K}
    (hf : ShortWeierstrass.Embedding f A B) (hs : Function.Surjective f) (hone : f 1 = 1)
    (h2 : (2 : K) ≠ 0) {n h : Nat}
    (hcard : h = 1 → Nat.card {Q : Point (Fin p) // Q.isOnCurve = true} = n)
    {Q R : Point (Fin p)} :
    validatePublicKey n h Q = .ok R ↔
      R = Q ∧ Q ≠ .infinity ∧ Q.isOnCurve = true ∧ n • Point.toPoint A B f Q = 0 := by
  -- On the curve, `n Q = O` by double and add exactly when `n Q = 0` in the group.
  have key : Q.isOnCurve = true →
      (Q.mulBits id ShortWeierstrass.Params.inv id ShortWeierstrass.Params.a (n.log2 + 1) n =
        .infinity ↔ n • Point.toPoint A B f Q = 0) := fun hQ => by
    rw [← Point.toPoint_mulBits_field hf hone Jacobian.Coords.Embedding.id
        (fun x => hf.map_inv x) (fun _ => rfl) hf.map_a h2 _ n hQ Nat.lt_log2_self,
      Point.toPoint_eq_zero hf (Point.isOnCurve_mulBits_field hf hone Jacobian.Coords.Embedding.id
        (fun x => hf.map_inv x) (fun _ => rfl) hf.map_a h2 _ n hQ)]
    exact Iff.rfl
  -- The points of the curve over `F_p` map one to one onto the group.
  have hgroup : Nat.card {Q : Point (Fin p) // Q.isOnCurve = true} =
      Nat.card (ShortWeierstrass.curve A B).Point :=
    Nat.card_congr (Equiv.ofBijective (fun q => Point.toPoint A B f q.1)
      ⟨fun q1 q2 he => Subtype.ext ((Point.toPoint_inj hf q1.2 q2.2).mp he), fun P =>
        let ⟨q, hq, he⟩ := Point.toPoint_surjective hf hs P
        ⟨⟨q, hq⟩, he⟩⟩)
  rw [validatePublicKey_eq_ok_iff]
  constructor
  · rintro ⟨rfl, hi, hQ, h1 | hm⟩
    · exact ⟨rfl, hi, hQ, hcard h1 ▸ hgroup ▸ card_nsmul_eq_zero'⟩
    · exact ⟨rfl, hi, hQ, (key hQ).mp hm⟩
  · rintro ⟨rfl, hi, hQ, hn⟩
    exact ⟨rfl, hi, hQ, Or.inr ((key hQ).mpr hn)⟩

end Points

end EthLib.Cryptography.Sec1
