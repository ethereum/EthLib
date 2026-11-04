module

public import EthLib.Cryptography.Proofs.AltBn128.Order
public import EthLib.Cryptography.Proofs.AltBn128.G2Order

/-!
# Proofs: the pairing law of alt_bn128 as one hypothesis

[EIP-197](https://eips.ethereum.org/EIPS/eip-197) §"Specification" defines the check of ECPAIRING.

It returns one exactly when `sum_i log_P1(a_i) log_P2(b_i) = 0`.

EthLib does not prove that its pairing check computes this, so it states the law as one hypothesis.

The law reads points as multiples of the generators `P1` and `P2`.

Points are affine, so each group element has one representative.

A pair with a point at infinity does not change the check, with or without the law.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

/-- `P` is `a P1`. -/
def Point.Represents (P : Point) (a : ZMod Fr.modulus) : Prop :=
  P = Point.mulBits 256 a.val Point.generator

/-- `Q` is `b P2`. -/
def Point2.Represents (Q : Point2) (b : ZMod Fr.modulus) : Prop :=
  Q = Point2.mulBits 256 b.val Point2.generator

/-- The law of the pairing check.

Let `P_i = a_i P1` and `Q_i = b_i P2`.

The check of the pairs `(P_i, Q_i)` passes exactly when `sum_i a_i b_i = 0`. -/
structure PairingLaws : Prop where
  pairingCheck_iff :
    ∀ (pairs : List (Point × Point2)) (a b : List (ZMod Fr.modulus)),
      a.length = pairs.length → b.length = pairs.length →
      (∀ i (h : i < pairs.length),
        (pairs[i]).1.Represents a[i]! ∧ (pairs[i]).2.Represents b[i]!) →
      (pairingCheck pairs = true ↔ (List.zipWith (· * ·) a b).sum = 0)

/-! ## Pairs with a point at infinity -/

/-- A pair with a point at infinity does not change the check, wherever it sits. -/
theorem pairingCheck_append_cons {x : Point × Point2}
    (hx : x.1 = .infinity ∨ x.2 = .infinity) (ps qs : List (Point × Point2)) :
    pairingCheck (ps ++ x :: qs) = pairingCheck (ps ++ qs) := by
  obtain ⟨P, Q⟩ := x
  -- The fold skips the pair, so it reaches the rest with the same accumulator.
  rcases hx with h | h <;> simp only at h <;> subst h
  · simp only [pairingCheck, List.foldl_append, List.foldl_cons]
  · cases P <;> simp only [pairingCheck, List.foldl_append, List.foldl_cons]

/-- A first pair with a point at infinity does not change the check. -/
theorem pairingCheck_cons_of_infinity {x : Point × Point2}
    (hx : x.1 = .infinity ∨ x.2 = .infinity) (ps : List (Point × Point2)) :
    pairingCheck (x :: ps) = pairingCheck ps :=
  pairingCheck_append_cons hx [] ps

namespace Point

/-- Every point on the curve over `Fp` is `a P1` for some `a`. -/
theorem exists_represents {P : Point} (hP : P.isOnCurve = true) : ∃ a, P.Represents a := by
  obtain ⟨k, hk, rfl⟩ := exists_eq_mulBits_generator hP
  refine ⟨k, ?_⟩
  rw [Represents, ZMod.val_cast_of_lt hk]

/-- `P1` is `1 P1`. -/
theorem represents_generator : generator.Represents 1 := by
  have h := isOnCurve_generator
  rw [Represents, ZMod.val_one, ← toPoint_inj h (isOnCurve_mulBits _ _ h),
    toPoint_mulBits _ _ h (by decide), one_smul]

end Point

/-- `P2` is `1 P2`. -/
theorem Point2.represents_generator : Point2.generator.Represents 1 := by
  have h := Point2.isOnCurve_generator
  rw [Point2.Represents, ZMod.val_one, ← Point2.toPoint_inj h (Point2.isOnCurve_mulBits _ _ h),
    Point2.toPoint_mulBits _ _ h (by decide), one_smul]

namespace PairingLaws

/-- The law for two pairs, the shape of a check `e(A, B) e(C, D) = 1`. -/
theorem two_pairs (laws : PairingLaws) {P P' : Point} {Q Q' : Point2}
    {a b c d : ZMod Fr.modulus}
    (hP : P.Represents a) (hQ : Q.Represents b)
    (hP' : P'.Represents c) (hQ' : Q'.Represents d) :
    pairingCheck [(P, Q), (P', Q')] = true ↔ a * b + c * d = 0 := by
  have h := laws.pairingCheck_iff [(P, Q), (P', Q')] [a, c] [b, d] rfl rfl (by
    intro i hi
    match i, hi with
    | 0, _ => exact ⟨hP, hQ⟩
    | 1, _ => exact ⟨hP', hQ'⟩)
  simpa using h

/-- The check of no pairs passes. -/
theorem pairingCheck_nil (laws : PairingLaws) : pairingCheck [] = true :=
  (laws.pairingCheck_iff [] [] [] rfl rfl (fun _ h => absurd h (Nat.not_lt_zero _))).mpr rfl

/-- The law is non-degenerate: `P1` and `P2` do not pair to 1. -/
theorem nondegenerate (laws : PairingLaws) :
    pairingCheck [(Point.generator, Point2.generator)] = false := by
  have h := laws.pairingCheck_iff [(Point.generator, Point2.generator)] [1] [1] rfl rfl (by
    intro i hi
    match i, hi with
    | 0, _ => exact ⟨Point.represents_generator, Point2.represents_generator⟩)
  simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil] at h
  exact Bool.eq_false_iff.mpr fun ht => absurd (h.mp ht) (by decide)

end PairingLaws

end EthLib.Cryptography.AltBn128
