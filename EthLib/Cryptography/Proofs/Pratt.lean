import EthLib.Cryptography.Proofs.PowMod
import Mathlib.NumberTheory.LucasPrimality

/-!
# Proofs: primality from a factored `m - 1`

Lucas' test proves `m` prime from a witness `g` whose order is `m - 1`.

- `g^(m - 1) = 1` mod `m`.
- `g^((m - 1) / q) != 1` mod `m`, for each prime `q` that divides `m - 1`.

`prime_of_lucas` takes `m - 1` as a list of prime powers `q^e`.

The kernel checks the product and the powers by `decide`, through `PowMod.powModAux`.

Each factor `q` needs its own proof of primality, by `norm_num` when small, or by this lemma again.

That nesting is a Pratt certificate.
-/

namespace EthLib.Cryptography.Pratt

open PowMod

/-- A prime that divides a product of prime powers is one of the primes. -/
private theorem mem_of_dvd_prod {q : Nat} (hq : q.Prime) :
    ∀ fs : List (Nat × Nat), (∀ f ∈ fs, f.1.Prime) →
      q ∣ (fs.map fun f => f.1 ^ f.2).prod → ∃ f ∈ fs, q = f.1
  | [], _, h => absurd (Nat.le_of_dvd Nat.one_pos (by simpa using h)) (by have := hq.two_le; omega)
  | f :: fs, hp, h => by
    rw [List.map_cons, List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · -- `q` divides `f.1^f.2`, so it divides the prime `f.1`, and equals it.
      exact ⟨f, List.mem_cons_self .., (Nat.prime_dvd_prime_iff_eq hq (hp f (List.mem_cons_self ..))).mp
        (hq.dvd_of_dvd_pow h)⟩
    · obtain ⟨g, hg, rfl⟩ := mem_of_dvd_prod hq fs (fun g hg => hp g (List.mem_cons_of_mem _ hg)) h
      exact ⟨g, List.mem_cons_of_mem _ hg, rfl⟩

/-- Lucas' test, with `m - 1` given as the product of `q^e` over `fs`.

`fuel` bounds the exponents: `m - 1 < 2^fuel`. -/
theorem prime_of_lucas (m g fuel : Nat) (fs : List (Nat × Nat))
    (hfuel : m - 1 < 2 ^ fuel)
    (hprod : (fs.map fun f => f.1 ^ f.2).prod = m - 1)
    (hprime : ∀ f ∈ fs, f.1.Prime)
    (hpow : powModAux fuel m g (m - 1) = 1 % m)
    (hdiv : fs.all (fun f => powModAux fuel m g ((m - 1) / f.1) != 1 % m) = true) :
    m.Prime := by
  refine lucas_primality m (g : ZMod m) ((natCast_pow_eq_one_iff m fuel g _ hfuel).mpr hpow) ?_
  intro q hq hdvd
  -- `q` is one of the listed primes, whose power check the kernel ran.
  obtain ⟨f, hf, rfl⟩ := mem_of_dvd_prod hq fs hprime (hprod ▸ hdvd)
  have hne := List.all_eq_true.mp hdiv f hf
  exact natCast_pow_div_ne_one m fuel g f.1 hfuel (by simpa using hne)

end EthLib.Cryptography.Pratt
