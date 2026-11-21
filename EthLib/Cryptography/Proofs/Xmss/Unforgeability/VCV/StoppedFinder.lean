module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PriorRetirement
public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.StoppedPartner

/-!
# An earlier digest match at the end of the real finder

The leanXMSS draft in "WOTS+C", paragraph "Signing", stops when the low digest decodes.
Only the last physical query can add a valid word.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest

open Constants HashSig OracleComp OracleSpec CachedCodeword PostSigning randomOracle.Partners
open scoped ENNReal

/-- Probability that the native finder selects an input with a partner in its resulting cache. -/
noncomputable def stoppedSelection (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (r : Randomizer) (c fuel : Nat) (cache : HashSpec.QueryCache) : ℝ≥0∞ :=
  Pr{let z ← (simulateQ randomOracle (selected pp l e m r c fuel)).run cache}[
    ∃ t, z.1 = some t ∧ EarlierDigest.Partner pp z.2 (trialInput pp l e m t)]

/-- An already partnered row and a fresh first accepted match are the two ways to finish.
The inequality is valid for a fixed, adversarially chosen starting randomizer. -/
theorem stopped_finder_le (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (r : Randomizer) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32) (cache : HashSpec.QueryCache)
    (seen : Finset HashInput) (covers : ∀ b w, cache b = some w → b ∈ seen) :
    let p : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
    let ε : ℝ≥0∞ := 1 / 2 ^ 128
    let Φ := partneredSelections pp l e {(m, r)} c fuel cache
    p * stoppedSelection pp l e m r c fuel cache ≤ p * Φ + ε * (validInputs pp l e cache seen).card := by
  classical
  intro p ε Φ
  have valid (w : HashOutput) (d : Digest) (hw : validDigest w = some d) : w ∈ accepted := by
    unfold validDigest at hw
    split at hw
    · exact (mem_accepted _).2 ‹_›
    · contradiction
  have rate := storedDigest_rate_le (messageKey pp) validDigest cache (some (l, e)) (validInputs pp l e cache seen)
    ε (fun b hk w hw d hd => Finset.mem_filter.mpr ⟨covers b w hw, hk, w, valid w d hd, hw⟩) prEvent_validDigest
  let enc := trialInput pp l e m
  let trials := (List.range' c fuel).map (trialRandomizer r)
  let run := (simulateQ randomOracle (AcceptedScan.scanWithAnswer accepted enc trials)).run cache
  have finish : stoppedSelection pp l e m r c fuel cache = Pr{let z ← run}[
      ∃ x w, z.1 = some (x, w) ∧ EarlierDigest.Partner pp z.2 (enc x)] := by
    simp only [stoppedSelection, selected, findCodeword_position, AcceptedScan.scan, simulateQ_map,
      StateT.run_map, prEvent_norm]
    apply prEvent_congr
    rintro ⟨_ | ⟨x, w⟩, state⟩ <;> simp [enc]
  have old : Φ = partneredMass (messageKey pp) validDigest accepted enc trials cache := by
    simp only [Φ, partneredSelections, selected, findCodeword_position, Finset.sum_singleton, partneredMass, trials, enc]
  rw [finish, old, show p = Pr{let w ← $ᵗ HashOutput}[w ∈ accepted] from prEvent_accepted.symm]
  refine (stopped_partner_le (messageKey pp) validDigest accepted enc trials (trials_nodup pp l e m r c fuel within) cache
    (some (l, e)) (messageKey_trial pp l e m) valid).trans ?_
  · apply add_le_add_right
    exact (prEvent_mono _ _ _ (fun _ h => h.2)).trans rate

/-- Summing over all possible randomizer starts pays one terminal fresh-match penalty per key,
with the old-partner term still weighted by its actual finder selection probabilities. -/
theorem sum_stopped_finder_le (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32) (cache : HashSpec.QueryCache)
    (seen : Finset HashInput) (covers : ∀ b w, cache b = some w → b ∈ seen) :
    let p : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
    p * (∑ r : Randomizer, stoppedSelection pp l e m r c fuel cache) ≤
      p * partneredSelections pp l e ({m} ×ˢ Finset.univ) c fuel cache + (validInputs pp l e cache seen).card := by
  classical
  intro p
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum fun r _ => stopped_finder_le pp l e m r c fuel within cache seen covers).trans_eq ?_
  simp only [Finset.sum_add_distrib, partneredSelections, Finset.sum_singleton, Finset.sum_product,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change _ + (1 / 2 ^ 128) * (((Fintype.card Digest : Nat) : ℝ≥0∞) * _) = _
  rw [card_digest, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, one_div]
  norm_num [p, ENNReal.inv_mul_cancel]

/-- A selected row which was partnered at entry can only belong to a physically active message. -/
private theorem earlier_le_active (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (c fuel : Nat) (cache : HashSpec.QueryCache) (seen : Finset HashInput)
    (covers : ∀ b w, cache b = some w → b ∈ seen) :
    partneredSelections pp l e ({m} ×ˢ Finset.univ) c fuel cache ≤
      partneredSelections pp l e (activeMessages pp l e seen ×ˢ Finset.univ) c fuel cache := by
  classical
  let base := trialInput pp l e m (Vector.replicate 16 0)
  let more := insert base seen
  have mem : m ∈ activeMessages pp l e more := by
    apply Finset.mem_biUnion.mpr
    have has : ∃ n r, trialInput pp l e n r = base := ⟨m, _, rfl⟩
    obtain ⟨s, eq⟩ := has.choose_spec
    exact ⟨base, Finset.mem_insert_self .., by simp [messageOfInput, has, (trial_message_randomizer eq).1]⟩
  rw [(selections_active pp l e c fuel cache seen more (Finset.subset_insert ..) covers).2]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.product_subset_product (Finset.singleton_subset_iff.mpr mem) (Finset.Subset.refl _)
  · exact fun _ _ _ => zero_le

/-- The low private 128-bit draw used for a fresh signing base. -/
noncomputable def freshStopped (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (c fuel : Nat) (cache : HashSpec.QueryCache) : ℝ≥0∞ :=
  Pr{let z ← (do
    let low ← $ᵗ BitVec digestBits
    (simulateQ randomOracle (selected pp l e m (ofBV 16 low) c fuel)).run cache)}[
       ∃ t, z.1 = some t ∧ EarlierDigest.Partner pp z.2 (trialInput pp l e m t)]

/-- The average over the real low-word draw uses all 2^128 little-endian randomizers exactly once. -/
private theorem freshStopped_eq (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (c fuel : Nat) (cache : HashSpec.QueryCache) :
    freshStopped pp l e m c fuel cache =
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑ r, stoppedSelection pp l e m r c fuel cache := by
  classical
  let bytes : BitVec digestBits ≃ Randomizer := Equiv.ofBijective (ofBV 16) ⟨fun _ _ => ofBV_inj (by decide),
    fun r => ⟨BitVec.ofNat digestBits (bytesToUint r), ofBV_ofNat_bytesToUint r (by decide)⟩⟩
  unfold freshStopped
  rw [prEvent_bind_eq_sum_fintype]
  let cost := fun r => stoppedSelection pp l e m r c fuel cache
  have weight (x : BitVec digestBits) : Pr{let t ← $ᵗ BitVec digestBits}[t = x] = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
    rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bitVec]
    norm_num [digestBits]
  calc
    _ = ∑ x : BitVec digestBits, (2 ^ 128 : ℝ≥0∞)⁻¹ * cost (bytes x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [weight]
      rfl
    _ = _ := by rw [← Finset.mul_sum, Equiv.sum_comp bytes cost]

/-- Price an independently sampled bottom or top base on the warm cache left by the caller.
The prior mass includes every active message at this physical key. -/
theorem fresh_stopped_le (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32) (cache : HashSpec.QueryCache)
    (seen : Finset HashInput) (covers : ∀ b w, cache b = some w → b ∈ seen) :
    let p : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
    let eps : ℝ≥0∞ := (2 ^ 128)⁻¹
    p * freshStopped pp l e m c fuel cache ≤ eps *
      (p * partneredSelections pp l e (activeMessages pp l e seen ×ˢ Finset.univ) c fuel cache +
        (validInputs pp l e cache seen).card) := by
  intro p eps
  rw [freshStopped_eq, mul_left_comm]
  apply mul_le_mul_right
  refine (sum_stopped_finder_le pp l e m c fuel within cache seen covers).trans ?_
  exact add_le_add_left (mul_le_mul_right (earlier_le_active pp l e m c fuel cache seen covers) _) _

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest
