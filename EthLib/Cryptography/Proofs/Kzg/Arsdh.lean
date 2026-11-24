module

public import EthLib.Cryptography.Proofs.Kzg.CellBinding
public import EthLib.Cryptography.Proofs.Bls.Represents
import EthLib.Cryptography.Proofs.Bls.PairingAte

/-!
# Proofs: the winning conditions of the PeerDAS assumptions

Wagner and Zapico prove the security of PeerDAS under two assumptions, in ePrint 2025/1683, §2.1.

<https://eprint.iacr.org/2025/1683>

Both give the adversary the powers `τ^i` of a secret `τ`, for `i ≤ d` in `G1` and `i ≤ D` in `G2`.

This file states only the winning condition of each problem, for a fixed secret `τ`.

It models neither the input of the adversary, nor `D`, nor `d ≥ D`, nor the advantage.

For a known `τ`, both conditions are easy to meet, so a solution alone proves nothing.

A reduction must compute its solution from the input of the adversary.

That the problems are hard stays an informal hypothesis.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr TargetGroup G2.neg)
open scoped EthLib.Cryptography.Bls.Fr

/-! ## Bilinear strong Diffie–Hellman

The first assumption, Definition 1 of ePrint 2025/1683.
-/

/-- The winning condition of bilinear strong Diffie–Hellman, in the sign of ePrint 2025/1683.

The adversary outputs `c ≠ τ` and an element `x` of the target group that represents `1 / (τ - c)`.
-/
def IsBsdhSolutionSub {GT : Type} [CommMonoid GT] (M : TargetGroup GT) (τ : Fr)
    (sol : Fr × GT) : Prop :=
  sol.1 ≠ τ ∧ M.Represents sol.2 (τ - sol.1)⁻¹

/-- The two signs of `c`. -/
private theorem sign_fr (τ c : Fr) :
    τ - -c = τ + c ∧ (-c ≠ τ ↔ τ + c ≠ 0) := by
  refine ⟨sub_neg_eq_add τ c, not_congr ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← h]
    exact neg_add_cancel c
  · linear_combination -h

/-- The two signs of the problem: `(c, x)` solves one form exactly when `(-c, x)` solves the other.

The extended KZG paper, CACR 2010-10, Definition 2.4, writes `1 / (τ + c)` instead.

<https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf>

The two problems are the same, up to the sign of `c`.
-/
theorem isBsdhSolution_iff_sub {GT : Type} [CommMonoid GT] (M : TargetGroup GT) (τ c : Fr)
    (x : GT) : IsBsdhSolution M τ (c, x) ↔ IsBsdhSolutionSub M τ (-c, x) := by
  obtain ⟨h, hne⟩ := sign_fr τ c
  simp only [IsBsdhSolution, IsBsdhSolutionSub]
  rw [show (τ - -c : Fr) = τ + c from h]
  exact and_congr_left' hne.symm

/-! ## Adaptive rational strong Diffie–Hellman

The second assumption, Definition 2 of ePrint 2025/1683.

Lipmaa, Parisella and Siim introduced it at EUROCRYPT 2024, with only `g2` and `τ g2` in `G2`.

Footnote 3 of ePrint 2025/1683 gives the adversary `τ^i g2` for `i ≤ D`.
-/

/-- The vanishing polynomial of a set `S` of scalars, at `τ`: the product of `τ - s` over `S`. -/
def vanishingAt (S : Finset Fr) (τ : Fr) : Fr := ∏ s ∈ S, (τ - s)

/-- The winning condition of `(d, D)`-ARSDH for the secret `τ`, Definition 2 of ePrint 2025/1683.

The adversary outputs a set `S` of `d + 1` scalars and two points `g` and `φ` of `G1`.

Let `g` and `φ` represent the scalars `a` and `b`.

The scalar `a` is not zero, so the point `g` is not zero.

The scalars satisfy `a = b V_S(τ)`, where `V_S` vanishes on `S`.

PeerDAS uses `d = 4095` and `D = 64`, so `S` has 4096 scalars. -/
def IsArsdhSolution (d : Nat) (τ : Fr) (sol : Finset Fr × G1 × G1) : Prop :=
  sol.1.card = d + 1 ∧ ∃ a b, G1.Represents sol.2.1 a ∧ G1.Represents sol.2.2 b ∧ a ≠ 0 ∧
    a = b * vanishingAt sol.1 τ

/-- Take points that represent `a` and `b`.

A solution is then a set of `d + 1` scalars with `a = b V_S(τ)` and `a ≠ 0`. -/
theorem isArsdhSolution_iff {d : Nat} {τ : Fr} {S : Finset Fr} {g φ : G1} {a b : Fr}
    (hg : G1.Represents g a) (hφ : G1.Represents φ b) :
    IsArsdhSolution d τ (S, g, φ) ↔ S.card = d + 1 ∧ a ≠ 0 ∧ a = b * vanishingAt S τ := by
  refine and_congr_right' ⟨fun ⟨a', b', hg', hφ', h0, h⟩ => ?_,
    fun ⟨h0, h⟩ => ⟨a, b, hg, hφ, h0, h⟩⟩
  rw [hg.unique hg', hφ.unique hφ']
  exact ⟨h0, h⟩

/-- The scalar form of the pairing equation. -/
private theorem pairing_form_fr (a b v : Fr) :
    a = b * v ↔ a * -1 + b * v = 0 :=
  ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩

/-- The pairing form of the condition, as Definition 2 states it.

Let `Q` represent `V_S(τ)` in `G2`.

`a = b V_S(τ)` holds exactly when `e(g, g2) = e(φ, V_S(τ) g2) = e(φ, Q)`.

The check of the pairs `(g, -g2)` and `(φ, Q)` tests that equation. -/
theorem isArsdhSolution_iff_pairingCheck {d : Nat} {τ : Fr}
    {S : Finset Fr} {g φ : G1} {Q : G2} {a b : Fr} (hg : G1.Represents g a)
    (hφ : G1.Represents φ b) (hQ : G2.Represents Q (vanishingAt S τ)) :
    IsArsdhSolution d τ (S, g, φ) ↔ S.card = d + 1 ∧ a ≠ 0 ∧
      Bls.pairingCheck #[(g, G2.neg G2.generator), (φ, Q)] = true := by
  rw [isArsdhSolution_iff hg hφ, Bls.pairingLaws.two_pairs hg G2.represents_generator.neg hφ hQ]
  exact and_congr_right' (and_congr_right' (pairing_form_fr a b _))

end EthLib.Cryptography.Kzg
