module

public import EthLib.Cryptography.Bls.Pairing
public import EthLib.Cryptography.Proofs.Bls.FrZMod
public import EthLib.Cryptography.Proofs.Bls.G1Order
public import EthLib.Cryptography.Proofs.Bls.G2Order
public import EthLib.Cryptography.Proofs.Bls.G2Validity

/-!
# Proofs: the pairing law as one hypothesis

[draft-irtf-cfrg-bls-signature-04](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04) §1.3 asks for a non-degenerate bilinear map `e : G1 × G2 → GT`.

[EIP-2537](https://eips.ethereum.org/EIPS/eip-2537) "ABI for pairing check" defines the pairing check: it accepts exactly when the product of the `e(P_i, Q_i)` is 1.

`pairingCheck` implements that check, but EthLib does not prove that its Miller loop and final exponentiation compute such a map.

`PairingLaws` states, as one hypothesis, the consequence that the theorems need.

Let `P_i` represent `a_i * g_1` and `Q_i` represent `b_i * g_2`.

Bilinearity gives `prod_i e(P_i, Q_i) = e(g_1, g_2)^(sum_i a_i * b_i)`.

Non-degeneracy gives `e(g_1, g_2) != 1`, and `GT` has prime order `r`.

So the product is 1 exactly when `sum_i a_i * b_i = 0` in `Fr`, whichever such map `e` is.

A representative of `0 * g_1` or `0 * g_2` is a point at infinity, so the law also covers the pairs that the check skips.

`PairingLaws` is a `Prop`, never an axiom.

Each theorem that relies on it takes it as an explicit argument.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open scoped EthLib.Cryptography.Bls.Fr

/-- `P` is a valid representative of the group element `a • g1`. -/
def G1.Represents (P : G1) (a : Fr) : Prop :=
  G1.Valid P ∧ G1.toPoint P = G1.toPoint (G1.mul G1.generator a)

/-- `Q` is a valid representative of the group element `b • g2`. -/
def G2.Represents (Q : G2) (b : Fr) : Prop :=
  G2.Valid Q ∧ G2.toPoint Q = G2.toPoint (G2.mul G2.generator b)

/-- The law of the concrete pairing check, on points of the prime-order subgroups.

The check of the pairs `(P_i, Q_i)` passes exactly when `sum_i a_i * b_i = 0`.

Here `P_i` represents `a_i • g1` and `Q_i` represents `b_i • g2`. -/
structure PairingLaws : Prop where
  pairingCheck_iff :
    ∀ (pairs : List (G1 × G2)) (a b : List Fr),
      a.length = pairs.length → b.length = pairs.length →
      (∀ i (h : i < pairs.length), G1.Represents (pairs[i]).1 a[i]! ∧ G2.Represents (pairs[i]).2 b[i]!) →
      (pairingCheck pairs.toArray = true ↔ (List.zipWith (· * ·) a b).sum = 0)

namespace G1

/-- `a • g1`, as the spec computes it, represents `a • g1`. -/
theorem represents_mul_generator (a : Fr) : Represents (mul generator a) a :=
  ⟨valid_mul valid_generator a, rfl⟩

/-- The generator represents `1 • g1`. -/
theorem represents_generator : Represents generator 1 := by
  refine ⟨valid_generator, ?_⟩
  rw [toPoint_mul_generator, ofFr_one]

/-- Negation of a representative of `a • g1` represents `(-a) • g1`. -/
theorem Represents.neg {P : G1} {a : Fr} (h : Represents P a) : Represents (neg P) (-a) := by
  refine ⟨valid_neg h.1, ?_⟩
  -- `exact` closes the step up to the two definitionally equal `Fr` instances.
  have h0 : ofFr (-a) + ofFr a = 0 := by
    rw [← ofFr_add]
    exact (congrArg ofFr (neg_add_cancel a)).trans ofFr_zero
  rw [toPoint_neg h.1, h.2, toPoint_mul_generator, toPoint_mul_generator]
  exact (eq_neg_of_add_eq_zero_left h0).symm

end G1

namespace G2

/-- `b • g2`, as the spec computes it, represents `b • g2`. -/
theorem represents_mul_generator (b : Fr) : Represents (mul generator b) b :=
  ⟨valid_mul valid_generator b, rfl⟩

/-- The generator represents `1 • g2`. -/
theorem represents_generator : Represents generator 1 := by
  refine ⟨valid_generator, ?_⟩
  rw [toPoint_mul_generator, ofFr_one]

/-- Negation of a representative of `b • g2` represents `(-b) • g2`. -/
theorem Represents.neg {Q : G2} {b : Fr} (h : Represents Q b) : Represents (neg Q) (-b) := by
  refine ⟨valid_neg h.1, ?_⟩
  have h0 : ofFr (-b) + ofFr b = 0 := by
    rw [← ofFr_add]
    exact (congrArg ofFr (neg_add_cancel b)).trans ofFr_zero
  rw [toPoint_neg h.1, h.2, toPoint_mul_generator, toPoint_mul_generator]
  exact (eq_neg_of_add_eq_zero_left h0).symm

end G2

namespace PairingLaws

/-- The law for two pairs, the shape of a signature or an opening check. -/
theorem two_pairs (laws : PairingLaws) {P P' : G1} {Q Q' : G2} {a b c d : Fr}
    (hP : G1.Represents P a) (hQ : G2.Represents Q b)
    (hP' : G1.Represents P' c) (hQ' : G2.Represents Q' d) :
    pairingCheck #[(P, Q), (P', Q')] = true ↔ a * b + c * d = 0 := by
  have h := laws.pairingCheck_iff [(P, Q), (P', Q')] [a, c] [b, d] rfl rfl (by
    intro i hi
    match i, hi with
    | 0, _ => exact ⟨hP, hQ⟩
    | 1, _ => exact ⟨hP', hQ'⟩)
  simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil] at h
  -- The trailing `+ 0` of the sum uses the spec's `Fin` addition, so `Fin.add_zero` removes it.
  exact h.trans (iff_of_eq (congrArg (a * b + · = 0) (Fin.add_zero (c * d))))

/-- A sanity consequence: the generators do not pair to 1. -/
theorem nondegenerate (laws : PairingLaws) :
    pairingCheck #[(G1.generator, G2.generator)] = false := by
  have h := laws.pairingCheck_iff [(G1.generator, G2.generator)] [1] [1] rfl rfl (by
    intro i hi
    match i, hi with
    | 0, _ => exact ⟨G1.represents_generator, G2.represents_generator⟩)
  simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil] at h
  exact Bool.eq_false_iff.mpr fun ht => absurd (h.mp ht) (by decide)

end PairingLaws

end EthLib.Cryptography.Bls
