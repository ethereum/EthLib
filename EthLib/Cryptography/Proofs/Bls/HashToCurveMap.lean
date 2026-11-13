module

public import EthLib.Cryptography.Bls.MapToCurve
public import EthLib.Cryptography.Proofs.Bls.CurveMap

/-!
# Proofs: hashing to the BLS12-381 curves under a map of base fields

A map of base fields that respects their operations commutes with each step of hashing to a curve.

So the square roots, the SSWU maps, the isogenies and the cofactor clearing agree, once mapped.

The hash of a message to `G2` gives the same point, or the same error, on both base fields.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open EthLib.Cryptography.BaseField (Hom)

variable {F G : Type} [BaseField F] [BaseField G]

theorem map_sqrtOrError (f : Hom F G) (a : F) :
    sqrtOrError (f a) = (sqrtOrError a).map f := by
  unfold sqrtOrError
  rw [f.map_sqrt]
  cases BaseField.sqrt a <;> rfl

namespace Fp2

theorem map_sqrt (f : Hom F G) (a : Fp2 F) :
    Fp2.sqrt (a.map f) = (Fp2.sqrt a).map (Fp2.map f) := by
  obtain ⟨a0, a1⟩ := a
  unfold Fp2.sqrt
  simp only [Fp2.map, f.map_isZero, ← f.map_mul, ← f.map_add, ← f.map_ofNat,
    ← f.map_inverse, map_sqrtOrError]
  cases BaseField.isZero a1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases sqrtOrError (a0 * a0 + a1 * a1) with
    | error e => rfl
    | ok s =>
      simp only [Except.map, ← f.map_add, ← f.map_mul, ← f.map_inverse, f.map_sqrtCandidate,
        f.map_beq]
      split <;> simp only [Fp2.map, f.map_mul, f.map_inverse, f.map_ofNat]
  · simp only [↓reduceIte, f.map_sqrtCandidate, ← f.map_mul, f.map_beq]
    split <;> simp only [Except.map, Fp2.map, f.map_zero]

end Fp2

namespace HashToCurve

theorem map_fpFromBytesL (f : Hom F G) (b : ByteArray) :
    f (fpFromBytesL b : F) = fpFromBytesL b :=
  f.map_ofNat _

theorem map_hashToFieldFp2 (f : Hom F G) (msg dst : ByteArray) (count : Nat) :
    (hashToFieldFp2 msg dst count : Except BlsError (Vector (Fp2 F) count)).map
      (Vector.map (Fp2.map f)) = hashToFieldFp2 msg dst count := by
  unfold hashToFieldFp2
  dsimp only
  cases expandMessageXmd msg dst (count * 2 * 64) with
  | error e => rfl
  | ok uniform =>
    simp only [Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]
    congr 1
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Fp2.map, map_fpFromBytesL]

theorem map_sgn0Fp (f : Hom F G) (x : F) : sgn0Fp (f x) = sgn0Fp x :=
  f.map_sgn0 x

theorem map_sgn0Fp2 (f : Hom F G) (x : Fp2 F) : sgn0Fp2 (x.map f) = sgn0Fp2 x := by
  simp only [sgn0Fp2, Fp2.map, map_sgn0Fp, f.map_isZero]

theorem map_Z (f : Hom F G) : (Z : Fp2 F).map f = Z := by
  simp only [Z, Fp2.map, f.map_neg, f.map_ofNat, f.map_one]

theorem map_Aprime (f : Hom F G) : (Aprime : Fp2 F).map f = Aprime := by
  simp only [Aprime, Fp2.map, f.map_zero, f.map_ofNat]

theorem map_Bprime (f : Hom F G) : (Bprime : Fp2 F).map f = Bprime := by
  simp only [Bprime, Fp2.map, f.map_ofNat]

theorem map_simpleSwu (f : Hom F G) (u : Fp2 F) :
    simpleSwu (u.map f) = (simpleSwu u).map (Prod.map (Fp2.map f) (Fp2.map f)) := by
  unfold simpleSwu
  simp only [← map_Z f, ← map_Aprime f, ← map_Bprime f, ← Fp2.map_mul, ← Fp2.map_add,
    Fp2.map_isZero, ← Fp2.map_div, ← Fp2.map_neg, ← Fp2.map_one f, ← Fp2.map_inverse,
    ← apply_ite (Fp2.map f), Fp2.map_sqrt]
  generalize Z * (u * u) = zu2
  generalize (if (zu2 * zu2 + zu2).isZero = true then (Bprime / (Z * Aprime) : Fp2 F)
    else -Bprime / Aprime * (Fp2.one + (zu2 * zu2 + zu2).inverse)) = x1
  cases Fp2.sqrt (x1 * x1 * x1 + Aprime * x1 + Bprime) with
  | ok y =>
    simp only [Except.map, pure, Except.pure, Prod.map, map_sgn0Fp2, apply_ite (Fp2.map f),
      Fp2.map_neg]
  | error e =>
    cases Fp2.sqrt (zu2 * x1 * (zu2 * x1) * (zu2 * x1) + Aprime * (zu2 * x1) + Bprime) with
    | ok y =>
      simp only [Except.map, pure, Except.pure, bind, Except.bind, Prod.map, map_sgn0Fp2,
        apply_ite (Fp2.map f), Fp2.map_neg]
    | error e => rfl

theorem map_fp2 (f : Hom F G) (c0 c1 : Nat) : (fp2 c0 c1 : Fp2 F).map f = fp2 c0 c1 := by
  simp only [fp2, Fp2.map, f.map_ofNat]

theorem map_k10 (f : Hom F G) : (k10 : Fp2 F).map f = k10 := map_fp2 f _ _
theorem map_k11 (f : Hom F G) : (k11 : Fp2 F).map f = k11 := map_fp2 f _ _
theorem map_k12 (f : Hom F G) : (k12 : Fp2 F).map f = k12 := map_fp2 f _ _
theorem map_k13 (f : Hom F G) : (k13 : Fp2 F).map f = k13 := map_fp2 f _ _
theorem map_k20 (f : Hom F G) : (k20 : Fp2 F).map f = k20 := map_fp2 f _ _
theorem map_k21 (f : Hom F G) : (k21 : Fp2 F).map f = k21 := map_fp2 f _ _
theorem map_k30 (f : Hom F G) : (k30 : Fp2 F).map f = k30 := map_fp2 f _ _
theorem map_k31 (f : Hom F G) : (k31 : Fp2 F).map f = k31 := map_fp2 f _ _
theorem map_k32 (f : Hom F G) : (k32 : Fp2 F).map f = k32 := map_fp2 f _ _
theorem map_k33 (f : Hom F G) : (k33 : Fp2 F).map f = k33 := map_fp2 f _ _
theorem map_k40 (f : Hom F G) : (k40 : Fp2 F).map f = k40 := map_fp2 f _ _
theorem map_k41 (f : Hom F G) : (k41 : Fp2 F).map f = k41 := map_fp2 f _ _
theorem map_k42 (f : Hom F G) : (k42 : Fp2 F).map f = k42 := map_fp2 f _ _

theorem map_isoMapG2 (f : Hom F G) (xp yp : Fp2 F) :
    (isoMapG2 xp yp).map f = isoMapG2 (xp.map f) (yp.map f) := by
  unfold isoMapG2
  simp only [← map_k10 f, ← map_k11 f, ← map_k12 f, ← map_k13 f, ← map_k20 f, ← map_k21 f,
    ← map_k30 f, ← map_k31 f, ← map_k32 f, ← map_k33 f, ← map_k40 f, ← map_k41 f, ← map_k42 f,
    ← Fp2.map_mul, ← Fp2.map_add, Fp2.map_isZero,
    ← Fp2.map_div, apply_ite (G2.map f), G2.map_zero]
  simp only [G2.map, Fp2.map_one]

theorem map_frobeniusFp2 (f : Hom F G) (x : Fp2 F) :
    (frobeniusFp2 x).map f = frobeniusFp2 (x.map f) := by
  simp only [frobeniusFp2, Fp2.map, f.map_neg]

theorem map_c1Psi (f : Hom F G) : (c1Psi : Fp2 F).map f = c1Psi := by
  unfold c1Psi
  rw [Fp2.map_inverse, Fp2.map_powNat]
  simp only [Fp2.map, f.map_one]

theorem map_c2Psi (f : Hom F G) : (c2Psi : Fp2 F).map f = c2Psi := by
  unfold c2Psi
  rw [Fp2.map_inverse, Fp2.map_powNat]
  simp only [Fp2.map, f.map_one]

theorem map_c1Psi2 (f : Hom F G) : (c1Psi2 : Fp2 F).map f = c1Psi2 := by
  simp only [c1Psi2, Fp2.map, f.map_inverse, f.map_powNat, f.map_ofNat, f.map_zero]

theorem map_psi (f : Hom F G) (P : G2 F) : (psi P).map f = psi (P.map f) := by
  unfold psi
  have hz : (G2.map f P).z.isZero = P.z.isZero := Fp2.map_isZero f P.z
  rw [hz, ← G2.map_toAffine]
  cases P.z.isZero
  · obtain ⟨x, y⟩ := P.toAffine
    simp only [Bool.false_eq_true, ↓reduceIte, Prod.map, G2.map, ← map_c1Psi f, ← map_c2Psi f,
      ← map_frobeniusFp2, ← Fp2.map_mul, Fp2.map_one]
  · rfl

theorem map_psi2 (f : Hom F G) (P : G2 F) : (psi2 P).map f = psi2 (P.map f) := by
  unfold psi2
  have hz : (G2.map f P).z.isZero = P.z.isZero := Fp2.map_isZero f P.z
  rw [hz, ← G2.map_toAffine]
  cases P.z.isZero
  · obtain ⟨x, y⟩ := P.toAffine
    simp only [Bool.false_eq_true, ↓reduceIte, Prod.map, G2.map, ← map_c1Psi2 f,
      ← Fp2.map_mul, ← Fp2.map_neg, Fp2.map_one]
  · rfl

theorem map_mulNegX (f : Hom F G) (P : G2 F) : (mulNegX P).map f = mulNegX (P.map f) := by
  simp only [mulNegX, ← G2.map_mulNat]
  exact G2.map_neg f _

theorem map_clearCofactor (f : Hom F G) (P : G2 F) :
    (clearCofactor P).map f = clearCofactor (P.map f) := by
  have hadd : ∀ p q : G2 F, (G2.add p q).map f = G2.add (p.map f) (q.map f) :=
    G2.map_add f
  have hneg : ∀ p : G2 F, (G2.neg p).map f = G2.neg (p.map f) := G2.map_neg f
  simp only [clearCofactor, hadd, hneg, map_mulNegX, map_psi, map_psi2, G2.map_double]

theorem map_hashToG2 (f : Hom F G) (msg dst : ByteArray) :
    (hashToG2 msg dst : Except BlsError (G2 F)).map (G2.map f) = hashToG2 msg dst := by
  unfold hashToG2
  rw [← map_hashToFieldFp2 f]
  cases (hashToFieldFp2 msg dst 2 : Except BlsError (Vector (Fp2 F) 2)) with
  | error e => rfl
  | ok us =>
    simp only [Except.map, bind, Except.bind, Vector.getElem_map, map_simpleSwu]
    cases simpleSwu us[0] with
    | error e => rfl
    | ok p0 =>
      cases simpleSwu us[1] with
      | error e => rfl
      | ok p1 =>
        obtain ⟨x0, y0⟩ := p0
        obtain ⟨x1, y1⟩ := p1
        simp only [Prod.map, pure, Except.pure, map_clearCofactor, ← map_isoMapG2]
        congr 2
        exact G2.map_add f _ _

end HashToCurve

namespace MapToCurve

theorem map_Z (f : Hom F G) : f (Z : F) = Z := f.map_ofNat _

theorem map_Aprime (f : Hom F G) : f (Aprime : F) = Aprime := f.map_ofNat _

theorem map_Bprime (f : Hom F G) : f (Bprime : F) = Bprime := f.map_ofNat _

theorem map_simpleSwuG1 (f : Hom F G) (u : F) :
    simpleSwuG1 (f u) = (simpleSwuG1 u).map (Prod.map f f) := by
  unfold simpleSwuG1
  simp only [← map_Z f, ← map_Aprime f, ← map_Bprime f, ← f.map_mul, ← f.map_add,
    f.map_isZero, ← f.map_inverse, ← f.map_neg, ← f.map_one, ← apply_ite f, map_sqrtOrError]
  generalize Z * (u * u) = zu2
  generalize (if BaseField.isZero (zu2 * zu2 + zu2) = true then
      Bprime * BaseField.inverse (Z * Aprime)
    else -Bprime * BaseField.inverse Aprime * (BaseField.one + BaseField.inverse (zu2 * zu2 + zu2)))
    = x1
  cases sqrtOrError (x1 * x1 * x1 + Aprime * x1 + Bprime) with
  | ok _ =>
    simp only [Except.map, Except.isOk, Except.toBool, ↓reduceIte, bind, Except.bind]
    cases sqrtOrError (x1 * x1 * x1 + Aprime * x1 + Bprime) with
    | ok y =>
      simp only [pure, Except.pure, Prod.map, apply_ite f.toFun, f.map_neg,
        HashToCurve.map_sgn0Fp]
    | error e => rfl
  | error _ =>
    simp only [Except.map, Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte, bind,
      Except.bind]
    cases sqrtOrError (zu2 * x1 * (zu2 * x1) * (zu2 * x1) + Aprime * (zu2 * x1) + Bprime) with
    | ok y =>
      simp only [pure, Except.pure, Prod.map, apply_ite f.toFun, f.map_neg,
        HashToCurve.map_sgn0Fp]
    | error e => rfl

theorem map_k1_0 (f : Hom F G) : f (k1_0 : F) = k1_0 := f.map_ofNat _
theorem map_k1_1 (f : Hom F G) : f (k1_1 : F) = k1_1 := f.map_ofNat _
theorem map_k1_2 (f : Hom F G) : f (k1_2 : F) = k1_2 := f.map_ofNat _
theorem map_k1_3 (f : Hom F G) : f (k1_3 : F) = k1_3 := f.map_ofNat _
theorem map_k1_4 (f : Hom F G) : f (k1_4 : F) = k1_4 := f.map_ofNat _
theorem map_k1_5 (f : Hom F G) : f (k1_5 : F) = k1_5 := f.map_ofNat _
theorem map_k1_6 (f : Hom F G) : f (k1_6 : F) = k1_6 := f.map_ofNat _
theorem map_k1_7 (f : Hom F G) : f (k1_7 : F) = k1_7 := f.map_ofNat _
theorem map_k1_8 (f : Hom F G) : f (k1_8 : F) = k1_8 := f.map_ofNat _
theorem map_k1_9 (f : Hom F G) : f (k1_9 : F) = k1_9 := f.map_ofNat _
theorem map_k1_10 (f : Hom F G) : f (k1_10 : F) = k1_10 := f.map_ofNat _
theorem map_k1_11 (f : Hom F G) : f (k1_11 : F) = k1_11 := f.map_ofNat _
theorem map_k2_0 (f : Hom F G) : f (k2_0 : F) = k2_0 := f.map_ofNat _
theorem map_k2_1 (f : Hom F G) : f (k2_1 : F) = k2_1 := f.map_ofNat _
theorem map_k2_2 (f : Hom F G) : f (k2_2 : F) = k2_2 := f.map_ofNat _
theorem map_k2_3 (f : Hom F G) : f (k2_3 : F) = k2_3 := f.map_ofNat _
theorem map_k2_4 (f : Hom F G) : f (k2_4 : F) = k2_4 := f.map_ofNat _
theorem map_k2_5 (f : Hom F G) : f (k2_5 : F) = k2_5 := f.map_ofNat _
theorem map_k2_6 (f : Hom F G) : f (k2_6 : F) = k2_6 := f.map_ofNat _
theorem map_k2_7 (f : Hom F G) : f (k2_7 : F) = k2_7 := f.map_ofNat _
theorem map_k2_8 (f : Hom F G) : f (k2_8 : F) = k2_8 := f.map_ofNat _
theorem map_k2_9 (f : Hom F G) : f (k2_9 : F) = k2_9 := f.map_ofNat _
theorem map_k3_0 (f : Hom F G) : f (k3_0 : F) = k3_0 := f.map_ofNat _
theorem map_k3_1 (f : Hom F G) : f (k3_1 : F) = k3_1 := f.map_ofNat _
theorem map_k3_2 (f : Hom F G) : f (k3_2 : F) = k3_2 := f.map_ofNat _
theorem map_k3_3 (f : Hom F G) : f (k3_3 : F) = k3_3 := f.map_ofNat _
theorem map_k3_4 (f : Hom F G) : f (k3_4 : F) = k3_4 := f.map_ofNat _
theorem map_k3_5 (f : Hom F G) : f (k3_5 : F) = k3_5 := f.map_ofNat _
theorem map_k3_6 (f : Hom F G) : f (k3_6 : F) = k3_6 := f.map_ofNat _
theorem map_k3_7 (f : Hom F G) : f (k3_7 : F) = k3_7 := f.map_ofNat _
theorem map_k3_8 (f : Hom F G) : f (k3_8 : F) = k3_8 := f.map_ofNat _
theorem map_k3_9 (f : Hom F G) : f (k3_9 : F) = k3_9 := f.map_ofNat _
theorem map_k3_10 (f : Hom F G) : f (k3_10 : F) = k3_10 := f.map_ofNat _
theorem map_k3_11 (f : Hom F G) : f (k3_11 : F) = k3_11 := f.map_ofNat _
theorem map_k3_12 (f : Hom F G) : f (k3_12 : F) = k3_12 := f.map_ofNat _
theorem map_k3_13 (f : Hom F G) : f (k3_13 : F) = k3_13 := f.map_ofNat _
theorem map_k3_14 (f : Hom F G) : f (k3_14 : F) = k3_14 := f.map_ofNat _
theorem map_k3_15 (f : Hom F G) : f (k3_15 : F) = k3_15 := f.map_ofNat _
theorem map_k4_0 (f : Hom F G) : f (k4_0 : F) = k4_0 := f.map_ofNat _
theorem map_k4_1 (f : Hom F G) : f (k4_1 : F) = k4_1 := f.map_ofNat _
theorem map_k4_2 (f : Hom F G) : f (k4_2 : F) = k4_2 := f.map_ofNat _
theorem map_k4_3 (f : Hom F G) : f (k4_3 : F) = k4_3 := f.map_ofNat _
theorem map_k4_4 (f : Hom F G) : f (k4_4 : F) = k4_4 := f.map_ofNat _
theorem map_k4_5 (f : Hom F G) : f (k4_5 : F) = k4_5 := f.map_ofNat _
theorem map_k4_6 (f : Hom F G) : f (k4_6 : F) = k4_6 := f.map_ofNat _
theorem map_k4_7 (f : Hom F G) : f (k4_7 : F) = k4_7 := f.map_ofNat _
theorem map_k4_8 (f : Hom F G) : f (k4_8 : F) = k4_8 := f.map_ofNat _
theorem map_k4_9 (f : Hom F G) : f (k4_9 : F) = k4_9 := f.map_ofNat _
theorem map_k4_10 (f : Hom F G) : f (k4_10 : F) = k4_10 := f.map_ofNat _
theorem map_k4_11 (f : Hom F G) : f (k4_11 : F) = k4_11 := f.map_ofNat _
theorem map_k4_12 (f : Hom F G) : f (k4_12 : F) = k4_12 := f.map_ofNat _
theorem map_k4_13 (f : Hom F G) : f (k4_13 : F) = k4_13 := f.map_ofNat _
theorem map_k4_14 (f : Hom F G) : f (k4_14 : F) = k4_14 := f.map_ofNat _

theorem map_K1 (f : Hom F G) : (K1 : List F).map f = K1 := by
  simp only [K1, List.map_cons, List.map_nil, map_k1_0, map_k1_1, map_k1_2, map_k1_3, map_k1_4,
    map_k1_5, map_k1_6, map_k1_7, map_k1_8, map_k1_9, map_k1_10, map_k1_11]

theorem map_K2 (f : Hom F G) : (K2 : List F).map f = K2 := by
  simp only [K2, List.map_cons, List.map_nil, map_k2_0, map_k2_1, map_k2_2, map_k2_3, map_k2_4,
    map_k2_5, map_k2_6, map_k2_7, map_k2_8, map_k2_9]

theorem map_K3 (f : Hom F G) : (K3 : List F).map f = K3 := by
  simp only [K3, List.map_cons, List.map_nil, map_k3_0, map_k3_1, map_k3_2, map_k3_3, map_k3_4,
    map_k3_5, map_k3_6, map_k3_7, map_k3_8, map_k3_9, map_k3_10, map_k3_11, map_k3_12, map_k3_13,
    map_k3_14, map_k3_15]

theorem map_K4 (f : Hom F G) : (K4 : List F).map f = K4 := by
  simp only [K4, List.map_cons, List.map_nil, map_k4_0, map_k4_1, map_k4_2, map_k4_3, map_k4_4,
    map_k4_5, map_k4_6, map_k4_7, map_k4_8, map_k4_9, map_k4_10, map_k4_11, map_k4_12, map_k4_13,
    map_k4_14]

theorem map_evaluate (f : Hom F G) (coefficients : List F) (x : F) :
    f (evaluate coefficients x) = evaluate (coefficients.map f) (f x) := by
  induction coefficients with
  | nil => exact f.map_zero
  | cons c cs ih =>
    simp only [evaluate, List.foldr_cons, List.map_cons, f.map_add, f.map_mul] at ih ⊢
    rw [ih]

theorem map_isoMapG1 (f : Hom F G) (xp yp : F) :
    (isoMapG1 xp yp).map f = isoMapG1 (f xp) (f yp) := by
  unfold isoMapG1
  simp only [← map_K1 f, ← map_K2 f, ← map_K3 f, ← map_K4 f, ← map_evaluate, ← f.map_powNat,
    ← f.map_add, f.map_isZero, ← f.map_mul, ← f.map_inverse, ← f.map_one,
    apply_ite (G1.map f), G1.map_zero]
  simp only [G1.map]

theorem map_clearCofactorG1 (f : Hom F G) (point : G1 F) :
    (clearCofactorG1 point).map f = clearCofactorG1 (point.map f) :=
  G1.map_mulNat f point H_EFF_G1

theorem map_mapToG1 (f : Hom F G) (u : F) :
    mapToG1 (f u) = (mapToG1 u).map (G1.map f) := by
  unfold mapToG1
  rw [map_simpleSwuG1]
  cases simpleSwuG1 u with
  | error e => rfl
  | ok p =>
    obtain ⟨x, y⟩ := p
    simp only [Except.map, bind, Except.bind, pure, Except.pure, Prod.map, map_clearCofactorG1,
      map_isoMapG1]

theorem map_mapToG2 (f : Hom F G) (u : Fp2 F) :
    mapToG2 (u.map f) = (mapToG2 u).map (G2.map f) := by
  unfold mapToG2
  rw [HashToCurve.map_simpleSwu]
  cases HashToCurve.simpleSwu u with
  | error e => rfl
  | ok p =>
    obtain ⟨x, y⟩ := p
    simp only [Except.map, bind, Except.bind, pure, Except.pure, Prod.map,
      HashToCurve.map_clearCofactor, HashToCurve.map_isoMapG2]

end MapToCurve

end EthLib.Cryptography.Bls
