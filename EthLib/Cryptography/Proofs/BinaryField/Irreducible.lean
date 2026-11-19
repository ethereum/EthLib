module

public import Mathlib.FieldTheory.Finite.Extension

/-!
# Proofs: a test of irreducibility over GF(2)

Let `f` be monic over GF(2), of degree `2^(k+1)`.

Then `f` is irreducible when two conditions hold.

- `f` divides `u^(2^(2^(k+1))) - u`.
- `f` is coprime to `u^(2^(2^k)) - u`.

If `f` is reducible, it has an irreducible factor of degree `d` at most `2^k`.

That factor divides `u^(2^d) - u`.

The first condition makes `d` divide `2^(k+1)`, so `d` divides `2^k`.

The factor then divides `u^(2^(2^k)) - u`, against the second condition.

A degree with one prime factor, here 2, needs only these two conditions.

The test is due to M. O. Rabin, in "Probabilistic algorithms in finite fields" (1980).

The factor divides `u^(2^d) - u` by Theorem 3.20 of Lidl and Niederreiter, "Finite Fields".
-/

@[expose] public section

namespace EthLib.Cryptography.BinaryField

open Polynomial

/-- A monic polynomial of degree `2^(k+1)` over GF(2) is irreducible under two conditions.

It divides `u^(2^(2^(k+1))) - u`, and it is coprime to `u^(2^(2^k)) - u`. -/
theorem irreducible_of_dvd_of_isCoprime {f : (ZMod 2)[X]} {k : ℕ} (hmonic : f.Monic)
    (hdeg : f.natDegree = 2 ^ (k + 1)) (hdvd : f ∣ X ^ 2 ^ 2 ^ (k + 1) - X)
    (hcop : IsCoprime f (X ^ 2 ^ 2 ^ k - X)) : Irreducible f := by
  have hcard : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  rw [hmonic.irreducible_iff_natDegree']
  refine ⟨fun h1 => ?_, fun a g _ hg hag hmem => ?_⟩
  · rw [h1, natDegree_one] at hdeg
    exact absurd hdeg.symm (by positivity)
  · rw [Finset.mem_Ioc, hdeg, pow_succ, Nat.mul_div_cancel _ two_pos] at hmem
    -- A factor `g` of degree at most `2^k` has an irreducible factor `q`.
    have hg0 : g ≠ 0 := hg.ne_zero
    have hgu : ¬ IsUnit g := fun hu => by
      rw [natDegree_eq_zero_of_isUnit hu] at hmem
      omega
    obtain ⟨q, hq, hqg⟩ := WfDvdMonoid.exists_irreducible_factor hgu hg0
    have hqf : q ∣ f := hqg.trans (Dvd.intro_left a hag)
    -- The first condition makes the degree of `q` divide `2^(k+1)`.
    have hqd : q.natDegree ∣ 2 ^ (k + 1) :=
      hq.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (by rw [hcard]; exact hqf.trans hdvd)
    have hqle : q.natDegree ≤ 2 ^ k := (natDegree_le_of_dvd hqg hg0).trans hmem.2
    -- A power of two at most `2^k` divides `2^k`.
    have hqk : q.natDegree ∣ 2 ^ k := by
      obtain ⟨i, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hqd
      rw [he] at hqle ⊢
      exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp hqle)
    -- So `q` divides `u^(2^(2^k)) - u` and `f`, against the second condition.
    have hqx := hq.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hqk
    rw [hcard] at hqx
    exact hq.not_isUnit (hcop.isUnit_of_dvd' hqf hqx)

end EthLib.Cryptography.BinaryField
