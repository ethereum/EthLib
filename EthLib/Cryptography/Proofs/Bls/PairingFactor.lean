module

public import EthLib.Cryptography.Bls.Pairing

/-!
# Proofs: the pairing through the factor of its pair

A pair with a point at infinity has no factor, and its pairing is 1.

Any other pair has its conjugated Miller loop as its factor.

Its pairing is the final exponentiation of that factor.

Proofs rewrite with these facts instead of unfolding the pairing.

Unfolding it on concrete points, such as a multiple of a generator, lets Lean evaluate them.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

variable {F : Type} [BaseField F]

/-- A pair with a point at infinity has no factor. -/
theorem pairFactor_eq_none {P : G1 F} {Q : G2 F} (h : (P.isInfinity || Q.isInfinity) = true) :
    pairFactor (P, Q) = none := by
  simp [pairFactor, h]

/-- A pair without a point at infinity has its conjugated Miller loop as its factor. -/
theorem pairFactor_eq_some {P : G1 F} {Q : G2 F} (h : (P.isInfinity || Q.isInfinity) = false) :
    pairFactor (P, Q) = some (millerLoop blsX Q.toAffine P.toAffine).conjugate := by
  simp [pairFactor, h]

/-- The pairing of a pair without a factor is 1. -/
theorem pairing_eq_one_of_pairFactor {P : G1 F} {Q : G2 F} (h : pairFactor (P, Q) = none) :
    pairing P Q = Fp12.one := by
  rw [pairing, h]

/-- The pairing of a pair with a factor is the final exponentiation of that factor. -/
theorem pairing_eq_of_pairFactor {P : G1 F} {Q : G2 F} {f : Fp12 F}
    (h : pairFactor (P, Q) = some f) : pairing P Q = finalExponentiation f := by
  rw [pairing, h]

end EthLib.Cryptography.Bls
