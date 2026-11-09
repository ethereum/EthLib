module

public import EthLib.Cryptography.Proofs.Bls.HashToCurve

/-!
# Square-root choices in G2 decoding and hashing

RFC 9380 §4 permits either square root because callers select its sign.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open scoped EthLib.Cryptography.Bls.Fp

namespace HashToCurve

private theorem parity_sub_odd (p n : Nat) (hp : p % 2 = 1) (hn : n ≤ p) :
    ((p - n) % 2 == 1) = !(n % 2 == 1) := by
  rw [Bool.eq_iff_iff, Bool.not_eq_true_eq_eq_false, beq_iff_eq, beq_eq_false_iff_ne]
  omega

private theorem sgn0Fp_eq_val (a : Fp) : sgn0Fp a = (a.val % 2 == 1) := by
  rw [sgn0Fp]
  exact Fp.baseField_sgn0 a

/-- Negation flips the RFC 9380 §4.1 sign of a nonzero base-field element. -/
theorem sgn0Fp_neg {y : Fp} (hy : y ≠ 0) : sgn0Fp (-y) = !sgn0Fp y := by
  have hy0 : 0 < y.val := Nat.pos_of_ne_zero (fun h => hy (Fp.ext (h.trans Fp.val_zero.symm)))
  have hylt : y.val < Fp.modulus := Fp.val_lt y
  have hv : (-y).val = Fp.modulus - y.val := by
    rw [Fp.val_neg, Nat.mod_eq_of_lt (by omega)]
  have hp : Fp.modulus % 2 = 1 := by decide
  rw [sgn0Fp_eq_val, sgn0Fp_eq_val, hv]
  exact parity_sub_odd _ _ hp (Nat.le_of_lt hylt)

private theorem sgn0Fp_zero : sgn0Fp (0 : Fp) = false := by
  rw [sgn0Fp_eq_val, Fp.val_zero]
  rfl

/-- Negation flips the RFC 9380 §4.1 sign of a nonzero quadratic-extension element. -/
theorem sgn0Fp2_neg {y : Fp2} (hy : y ≠ 0) : sgn0Fp2 (-y) = !sgn0Fp2 y := by
  have hz : BaseField.isZero (-y).c0 = BaseField.isZero y.c0 := by
    rw [Bool.eq_iff_iff, Fp.baseField_isZero, Fp.baseField_isZero,
      Fp.isZero_iff, Fp.isZero_iff, Fp2.neg_c0, neg_eq_zero]
  rw [sgn0Fp2, sgn0Fp2, hz]
  by_cases h0 : y.c0 = 0
  · have h1 : y.c1 ≠ 0 := fun h1 => hy (Fp2.ext h0 h1)
    have hs0 : sgn0Fp y.c0 = false := h0 ▸ sgn0Fp_zero
    have hn0 : sgn0Fp (-y).c0 = false := by
      rw [Fp2.neg_c0, sgn0Fp_eq_val, Fp.val_neg, h0, Fp.val_zero]
      decide
    have hz0 : BaseField.isZero y.c0 = true := by
      rw [Fp.baseField_isZero, Fp.isZero_iff]
      exact h0
    rw [hs0, hn0, hz0]
    simp only [Bool.false_or, Bool.true_and, Fp2.neg_c1]
    exact sgn0Fp_neg h1
  · have hzero : BaseField.isZero y.c0 = false := by
      rw [Fp.baseField_isZero, Bool.eq_false_iff]
      exact fun hz => h0 (Fp.isZero_iff.mp hz)
    rw [hzero]
    simp only [Bool.false_and, Bool.or_false, Fp2.neg_c0]
    exact sgn0Fp_neg h0

/-- Selecting a sign gives the same result for a root and its negation, including zero. -/
theorem select_sign_neg {A : Type} [AddGroup A] (sign : A → Bool)
    (hflip : ∀ y : A, y ≠ 0 → sign (-y) = !sign y) (s : Bool) (y : A) :
    (if sign (-y) = s then -y else -(-y)) =
      (if sign y = s then y else -y) := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [hflip y hy, neg_neg]
    cases sign y <;> cases s <;> rfl

private theorem select_sign_neg_prop {A : Type} [AddGroup A] (sign : A → Bool)
    (hflip : ∀ y : A, y ≠ 0 → sign (-y) = !sign y) (s : Prop) [Decidable s] (y : A) :
    (if (sign (-y) = true) = s then -y else -(-y)) =
      (if (sign y = true) = s then y else -y) := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [hflip y hy, neg_neg]
    cases sign y <;> by_cases hs : s <;> simp [hs]

end HashToCurve

/-- Choosing a sign makes the optimized and reference square roots identical. -/
theorem Fp2.sqrt_map_sign (sign : Fp2 → Bool)
    (hflip : ∀ y : Fp2, y ≠ 0 → sign (-y) = !sign y) (s : Bool) (a : Fp2) :
    (Fp2.sqrt a).map (fun y => if sign y = s then y else -y) =
      (Fp2.sqrtReference a).map (fun y => if sign y = s then y else -y) := by
  rcases Fp2.sqrt_error_cases a with herror | ⟨y, hy⟩
  · rw [herror, (Fp2.sqrt_error_iff_reference a).mp herror]
  · obtain ⟨r, hr, hsign⟩ := Fp2.sqrt_ok_reference hy
    rw [hy, hr]
    simp only [Except.map]
    congr 1
    rcases hsign with rfl | rfl
    · rfl
    · exact HashToCurve.select_sign_neg sign hflip s r

set_option linter.auxLemma false in
/-- G2 decompression is unchanged when the reference square root chooses the other sign. -/
theorem G2.uncompress_eq_reference (bytes : ByteArray) :
    G2.uncompress bytes = G2.uncompress bytes Fp2.sqrtReference := by
  have errors := Fp2.sqrt_error_cases
  have failures := Fp2.sqrt_error_iff_reference
  have roots := @Fp2.sqrt_ok_reference
  generalize (Fp2.sqrt : Fp2 → Except BlsError Fp2) = newFn at errors failures roots ⊢
  generalize (Fp2.sqrtReference : Fp2 → Except BlsError Fp2) = refFn at failures roots ⊢
  unfold G2.uncompress
  split
  · rfl
  · extract_lets head isC isI yS cleared c1Bytes c0Bytes
    split
    · rfl
    · split
      · rfl
      · cases h1 : Fp.fromBytesBE c1Bytes with
        | error e => rfl
        | ok c1 =>
          cases h0 : Fp.fromBytesBE c0Bytes with
          | error e => rfl
          | ok c0 =>
            simp (config := { zeta := false, iota := false, beta := false }) only
              [G2.uncompress.match_3.eq_1]
            extract_lets x rhs
            rcases errors rhs with he | ⟨y, hy⟩
            · rw [he, (failures rhs).mp he]
            · obtain ⟨r, hr, hsign⟩ := roots hy
              rw [hy, hr]
              dsimp only
              congr 2
              rcases hsign with rfl | rfl
              · rfl
              · exact HashToCurve.select_sign_neg_prop Fp2.signBit
                  (fun _ hy => Fp2.signBit_neg hy) yS r

namespace HashToCurve

private theorem simpleSwu_congr_sqrt {F : Type} [BaseField F]
    (newFn refFn : Fp2 F → Except BlsError (Fp2 F)) (u : Fp2 F)
    (signed : ∀ a,
      (newFn a).map (fun y => if sgn0Fp2 u = sgn0Fp2 y then y else -y) =
        (refFn a).map (fun y => if sgn0Fp2 u = sgn0Fp2 y then y else -y)) :
    simpleSwu u newFn = simpleSwu u refFn := by
  unfold simpleSwu
  dsimp only
  generalize Z * (u * u) = t
  generalize (if (t * t + t).isZero = true then Bprime / (Z * Aprime)
    else -Bprime / Aprime * (Fp2.one + (t * t + t).inverse)) = x
  have h1 := signed (x * x * x + Aprime * x + Bprime)
  cases hn : newFn (x * x * x + Aprime * x + Bprime) with
  | error en =>
    cases hr : refFn (x * x * x + Aprime * x + Bprime) with
    | ok r => simp only [hn, hr, Except.map, reduceCtorEq] at h1
    | error er =>
      have h2 := signed (t * x * (t * x) * (t * x) + Aprime * (t * x) + Bprime)
      cases hn2 : newFn (t * x * (t * x) * (t * x) + Aprime * (t * x) + Bprime) <;>
        cases hr2 : refFn (t * x * (t * x) * (t * x) + Aprime * (t * x) + Bprime) <;>
        simp only [hn2, hr2, Except.map, bind, Except.bind, pure, Except.pure] at h2 ⊢
      · exact congrArg Except.error (Except.error.inj h2)
      · cases h2
      · cases h2
      · exact congrArg (fun z : Fp2 F =>
          (Except.ok (t * x, z) : Except BlsError (Fp2 F × Fp2 F))) (Except.ok.inj h2)
  | ok y =>
    cases hr : refFn (x * x * x + Aprime * x + Bprime) with
    | error er => simp only [hn, hr, Except.map, reduceCtorEq] at h1
    | ok r =>
      simp only [hn, hr, Except.map, Except.ok.injEq] at h1
      simpa only [pure, Except.pure] using
        congrArg (fun z : Fp2 F => (Except.ok (x, z) : Except BlsError (Fp2 F × Fp2 F))) h1

/-- The SSWU map is unchanged because RFC 9380 §6.6.2 selects the sign of its root. -/
theorem simpleSwu_eq_reference (u : Fp2) :
    simpleSwu u = simpleSwu u Fp2.sqrtReference := by
  apply simpleSwu_congr_sqrt
  have signed := Fp2.sqrt_map_sign sgn0Fp2 (fun _ hy => sgn0Fp2_neg hy) (sgn0Fp2 u)
  have choose : (fun y : Fp2 => if sgn0Fp2 y = sgn0Fp2 u then y else -y) =
      (fun y => if sgn0Fp2 u = sgn0Fp2 y then y else -y) := by
    funext y
    by_cases h : sgn0Fp2 y = sgn0Fp2 u
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  rw [choose] at signed
  exact signed

/-- Hashing to G2 is unchanged when both SSWU maps use the reference square root. -/
theorem hashToG2_eq_reference (msg dst : ByteArray) :
    hashToG2 (F := Fp) msg dst =
      hashToG2 msg dst (fun u => simpleSwu u Fp2.sqrtReference) := by
  have h : (fun u : Fp2 => simpleSwu u) = (fun u => simpleSwu u Fp2.sqrtReference) :=
    funext simpleSwu_eq_reference
  exact congrArg (fun swu => hashToG2 msg dst swu) h

end HashToCurve

end EthLib.Cryptography.Bls
