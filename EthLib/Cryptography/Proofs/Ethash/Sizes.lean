module

public import EthLib.Cryptography.Ethash.Sizes
public import Mathlib.NumberTheory.Bertrand

/-!
# Proofs: the sizes of the Ethash cache and dataset

The trial division decides primality.

The search for a size returns the first candidate whose count of items is prime.

Every candidate it passed over has a count that is not prime.

Bertrand's postulate puts a prime among the candidates, so the search never runs out of fuel.

So at every epoch the cache and the dataset hold a prime number of items.
-/

@[expose] public section

namespace EthLib.Cryptography.Ethash

/-! ## Trial division -/

/-- With fuel, trial division from `d` tries every divisor below `d + fuel` up to the root. -/
theorem noDivisorFrom_iff (n : Nat) :
    ∀ fuel d, noDivisorFrom n fuel d = true ↔
      ∀ m, d ≤ m → m < d + fuel → m * m ≤ n → n % m ≠ 0 := by
  intro fuel
  induction fuel with
  | zero => intro d; simp only [noDivisorFrom, true_iff]; intro m h1 h2; omega
  | succ fuel ih =>
    intro d
    simp only [noDivisorFrom, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      bne_iff_ne, ne_eq, ih]
    constructor
    · rintro (h | ⟨hd, h⟩) m hm1 hm2 hm3
      · -- Past the root, no divisor is left to try.
        have : d * d ≤ m * m := Nat.mul_le_mul hm1 hm1
        omega
      · rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
        · exact hd
        · exact h m hlt (by omega) hm3
    · intro h
      by_cases hlt : n < d * d
      · exact Or.inl hlt
      · refine Or.inr ⟨h d le_rfl (by omega) (by omega), fun m hm1 hm2 hm3 => ?_⟩
        exact h m (by omega) (by omega) hm3

/-- The trial division decides primality. -/
theorem isPrime_iff (n : Nat) : isPrime n = true ↔ Nat.Prime n := by
  rw [Nat.prime_def_le_sqrt]
  simp only [isPrime, Bool.and_eq_true, decide_eq_true_eq, noDivisorFrom_iff]
  refine and_congr_right fun h2 => ⟨fun h m hm hroot hdvd => ?_, fun h m hm1 _ hm3 hmod => ?_⟩
  · have hsq : m * m ≤ n := Nat.le_sqrt.mp hroot
    have : m ≤ n := le_trans (Nat.le_mul_self m) hsq
    exact h m hm (by omega) hsq (Nat.mod_eq_zero_of_dvd hdvd)
  · exact h m hm1 (Nat.le_sqrt.mpr hm3) (Nat.dvd_of_mod_eq_zero hmod)

/-! ## The search -/

/-- The search returns the first candidate with a prime count, if one is within its fuel.

The candidates are `x`, `x - 2 · unit`, `x - 4 · unit`, and so on. -/
theorem primeSize_go_spec (unit : Nat) :
    ∀ fuel x, (∃ k < fuel, Nat.Prime ((x - 2 * unit * k) / unit)) →
      ∃ k < fuel, primeSize.go unit fuel x = x - 2 * unit * k ∧
        Nat.Prime ((x - 2 * unit * k) / unit) ∧
        ∀ j < k, ¬Nat.Prime ((x - 2 * unit * j) / unit) := by
  intro fuel
  induction fuel with
  | zero => intro x ⟨k, hk, _⟩; omega
  | succ fuel ih =>
    intro x ⟨k, hk, hp⟩
    by_cases h0 : Nat.Prime (x / unit)
    · refine ⟨0, by omega, ?_, by simpa using h0, fun j hj => absurd hj (by omega)⟩
      simp [primeSize.go, (isPrime_iff _).mpr h0]
    · -- The first candidate fails, so the search goes on from the next one.
      have hk0 : k ≠ 0 := by rintro rfl; simp at hp; exact h0 hp
      have hnext : ∃ k < fuel, Nat.Prime ((x - 2 * unit - 2 * unit * k) / unit) :=
        ⟨k - 1, by omega, by
          rwa [Nat.sub_sub, show 2 * unit + 2 * unit * (k - 1) = 2 * unit * k by
            obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
            simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]; ring]⟩
      obtain ⟨k', hk', hgo, hp', hbefore⟩ := ih (x - 2 * unit) hnext
      have hshift : ∀ i, x - 2 * unit - 2 * unit * i = x - 2 * unit * (i + 1) := fun i => by
        rw [Nat.sub_sub, Nat.mul_add_one, Nat.add_comm]
      refine ⟨k' + 1, by omega, ?_, by rwa [← hshift], fun j hj => ?_⟩
      · have : isPrime (x / unit) = false := by
          cases h : isPrime (x / unit)
          · rfl
          · exact absurd ((isPrime_iff _).mp h) h0
        simp only [primeSize.go, this, Bool.false_eq_true, ite_false, hgo, hshift]
      · cases j with
        | zero => simpa using h0
        | succ j => rw [← hshift]; exact hbefore j (by omega)

/-- A search from `unit · q`, with `q` odd and at least 5, finds a prime count. -/
theorem primeSize_spec {unit q : Nat} (hu : 0 < unit) (hodd : q % 2 = 1) (hq : 5 ≤ q) :
    ∃ k < q, primeSize (unit * q) unit = unit * q - 2 * unit * k ∧
      Nat.Prime ((unit * q - 2 * unit * k) / unit) ∧
      ∀ j < k, ¬Nat.Prime ((unit * q - 2 * unit * j) / unit) := by
  -- Bertrand: a prime `p` with `q / 2 < p ≤ q - 1`, odd since it exceeds 2.
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (q / 2) (by omega)
  have hpodd : p % 2 = 1 := by
    by_contra hne
    have h2 : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega
  -- The candidate `k = (q - p) / 2` has count `q - 2k = p`.
  have hcount : ∀ k, 2 * k ≤ q → (unit * q - 2 * unit * k) / unit = q - 2 * k := fun k hk => by
    rw [show 2 * unit * k = unit * (2 * k) by ring, ← Nat.mul_sub, Nat.mul_div_cancel_left _ hu]
  have hfound : ∃ k < q, Nat.Prime ((unit * q - 2 * unit * k) / unit) :=
    ⟨(q - p) / 2, by omega, by rw [hcount _ (by omega)]; convert hp using 1; omega⟩
  unfold primeSize
  rw [Nat.mul_div_cancel_left _ hu]
  exact primeSize_go_spec unit q (unit * q) (by simpa [Nat.mul_div_cancel_left _ hu] using hfound)

/-! ## The sizes -/

/-- The count of items that the cache search starts from, at an epoch. -/
theorem cacheTop_eq (e : Nat) :
    CACHE_BYTES_INIT + CACHE_BYTES_GROWTH * e - HASH_BYTES =
      HASH_BYTES * (2 ^ 18 + 2 ^ 11 * e - 1) := by
  simp only [CACHE_BYTES_INIT, CACHE_BYTES_GROWTH, HASH_BYTES]
  omega

/-- The count of items that the dataset search starts from, at an epoch. -/
theorem datasetTop_eq (e : Nat) :
    DATASET_BYTES_INIT + DATASET_BYTES_GROWTH * e - MIX_BYTES =
      MIX_BYTES * (2 ^ 23 + 2 ^ 16 * e - 1) := by
  simp only [DATASET_BYTES_INIT, DATASET_BYTES_GROWTH, MIX_BYTES]
  omega

/-- The cache size is the first candidate below the linear size with a prime count of items.

Every candidate above it has a count that is not prime. -/
theorem cacheSize_spec (number : Nat) :
    ∃ k, cacheSize number =
        CACHE_BYTES_INIT + CACHE_BYTES_GROWTH * epoch number - HASH_BYTES - 2 * HASH_BYTES * k ∧
      Nat.Prime (cacheSize number / HASH_BYTES) ∧
      ∀ j < k, ¬Nat.Prime ((CACHE_BYTES_INIT + CACHE_BYTES_GROWTH * epoch number - HASH_BYTES -
        2 * HASH_BYTES * j) / HASH_BYTES) := by
  unfold cacheSize
  rw [cacheTop_eq]
  obtain ⟨k, -, h, hp, hb⟩ := primeSize_spec (unit := HASH_BYTES) (by decide)
    (q := 2 ^ 18 + 2 ^ 11 * epoch number - 1) (by omega) (by omega)
  exact ⟨k, h, h ▸ hp, hb⟩

/-- The dataset size is the first candidate below the linear size with a prime count of mixes.

Every candidate above it has a count that is not prime. -/
theorem datasetSize_spec (number : Nat) :
    ∃ k, datasetSize number =
        DATASET_BYTES_INIT + DATASET_BYTES_GROWTH * epoch number - MIX_BYTES - 2 * MIX_BYTES * k ∧
      Nat.Prime (datasetSize number / MIX_BYTES) ∧
      ∀ j < k, ¬Nat.Prime ((DATASET_BYTES_INIT + DATASET_BYTES_GROWTH * epoch number -
        MIX_BYTES - 2 * MIX_BYTES * j) / MIX_BYTES) := by
  unfold datasetSize
  rw [datasetTop_eq]
  obtain ⟨k, -, h, hp, hb⟩ := primeSize_spec (unit := MIX_BYTES) (by decide)
    (q := 2 ^ 23 + 2 ^ 16 * epoch number - 1) (by omega) (by omega)
  exact ⟨k, h, h ▸ hp, hb⟩

/-- The cache holds a prime number of items, so at least two. -/
theorem prime_cacheSize_div (number : Nat) : Nat.Prime (cacheSize number / HASH_BYTES) :=
  (cacheSize_spec number).choose_spec.2.1

/-- The dataset holds a prime number of mixes, so at least two. -/
theorem prime_datasetSize_div (number : Nat) : Nat.Prime (datasetSize number / MIX_BYTES) :=
  (datasetSize_spec number).choose_spec.2.1

end EthLib.Cryptography.Ethash
