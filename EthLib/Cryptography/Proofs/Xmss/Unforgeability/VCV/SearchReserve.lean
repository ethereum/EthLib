module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchSnapshots

/-!
# Bounding the total pre-search reserve by physical trial counts

Each signing key uses its entry at the first attempted search, or the live state if no search has begun.
The reserve sums over keys, while its final bound uses only the two totals for all keys.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest

open Constants HashSig OracleComp OracleSpec CachedCodeword PostSigning
open scoped ENNReal

/-- Number of physical message inputs at this key's live or saved entry. -/
noncomputable def inputCount (pp : PublicParam) (k : Key) (s : Entry) : Nat :=
  (inputsAtKey pp k.1 k.2 s.2).card

/-- Number of accepted physical inputs at this key's live or saved entry. -/
noncomputable def validCount (pp : PublicParam) (k : Key) (s : Entry) : Nat :=
  (validInputs pp k.1 k.2 s.1 s.2).card

/-- All adaptive first-attempt reserves are bounded by the same two physical counts. -/
theorem reserve_le_product (pp : PublicParam) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32)
    (keys : Finset Key) (state : Key → Entry)
    (covers : ∀ k ∈ keys, ∀ b w, (state k).1 b = some w → b ∈ (state k).2) :
    let p : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
    let ε : ℝ≥0∞ := 1 / 2 ^ 128
    let n : ℝ≥0∞ := ∑ k ∈ keys, (inputCount pp k (state k) : ℝ≥0∞)
    let v : ℝ≥0∞ := ∑ k ∈ keys, (validCount pp k (state k) : ℝ≥0∞)
    p * (∑ k ∈ keys, searchReserve pp c fuel k (state k)) ≤ ε * (v * (p * n + (1 - p) * v)) := by
  classical
  intro p ε n v
  let vk (k : Key) : ℝ≥0∞ := validCount pp k (state k)
  let nk (k : Key) : ℝ≥0∞ := inputCount pp k (state k)
  let h (k : Key) := occupiedSelections pp k.1 k.2
    (activeMessages pp k.1 k.2 (state k).2 ×ˢ Finset.univ) c fuel (state k).1
  have cap (k : Key) (hk : k ∈ keys) : p * h k ≤ p * nk k + (1 - p) * vk k :=
    occupied_finders_le pp k.1 k.2 _ c fuel within (state k).1 (state k).2 (covers k hk)
  have total (k : Key) (hk : k ∈ keys) : vk k ≤ v := Finset.single_le_sum (fun _ _ => bot_le) hk
  calc
    _ = ε * (∑ k ∈ keys, vk k * (p * h k)) := by
      simp only [searchReserve, vk, h, validCount, ε, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ac_rfl
    _ ≤ ε * (∑ k ∈ keys, v * (p * nk k + (1 - p) * vk k)) := by
      exact mul_le_mul_right (Finset.sum_le_sum fun k hk => mul_le_mul' (total k hk) (cap k hk)) _
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_add_distrib, n, v, vk, nk, mul_add]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest
