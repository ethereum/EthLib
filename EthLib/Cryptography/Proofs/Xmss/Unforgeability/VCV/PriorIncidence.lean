module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CyclicDigest
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PriorCompensation

/-!
# Counting physical rows across the message finders

The leanXMSS draft in "Hashing and parameters" places the fixed-width randomizer after the message.

The full hash input therefore identifies both the arbitrary-length message and its randomizer.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest

open Constants HashSig OracleComp OracleSpec AcceptedScan CachedCodeword PostSigning
open randomOracle.Partners
open scoped ENNReal

/-- At a fixed signing key the physical hash bytes identify both the message and randomizer. -/
theorem trial_message_randomizer {pp : PublicParam} {l : Layer} {e : UInt32}
    {m n : ByteArray} {r s : Randomizer} (same : trialInput pp l e m r = trialInput pp l e n s) :
    m = n ∧ r = s := by
  have payload := (thInput_inj (ByteArray.ext (Array.toList_inj.mp same))).2.2
  have size := congrArg ByteArray.size payload
  simp only [ByteArray.size_append, EthLib.Base.size_packBytes, Nat.add_left_inj] at size
  obtain ⟨messages, randomizers⟩ := byteArray_append_inj payload size
  exact ⟨messages, packBytes_injective randomizers⟩

private theorem count_rows (pp : PublicParam) (l : Layer) (e : UInt32) (msgs : Finset ByteArray)
    (positions : ByteArray → Finset Randomizer) (physical : Finset HashInput)
    (covered : ∀ m ∈ msgs, ∀ r ∈ positions m, trialInput pp l e m r ∈ physical) :
    (∑ m ∈ msgs, (positions m).card) ≤ physical.card := by
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn
    (fun v : Σ _ : ByteArray, Randomizer => trialInput pp l e v.1 v.2)
  · rintro ⟨m, r⟩ h
    obtain ⟨hm, hr⟩ := Finset.mem_sigma.mp h
    exact covered m hm r hr
  · rintro ⟨m, r⟩ _ ⟨n, s⟩ _ same
    obtain ⟨rfl, rfl⟩ := trial_message_randomizer same
    rfl

/-- Occupied full inputs at one physical layer and OTS key, including rejected words. -/
noncomputable def inputsAtKey (pp : PublicParam) (l : Layer) (e : UInt32)
    (seen : Finset HashInput) :=
  seen.filter fun b => messageKey pp b = some (l, e)

set_option maxRecDepth 4096 in
/-- The randomizer rotation counts each stored row once across all chosen messages.

This holds for every finite set of messages, without a message length restriction. -/
theorem occupied_finders_le (pp : PublicParam) (l : Layer) (e : UInt32) (msgs : Finset ByteArray)
    (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32) (cache : HashSpec.QueryCache)
    (seen : Finset HashInput) (covers : ∀ b w, cache b = some w → b ∈ seen) :
    let p : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
    p * occupiedSelections pp l e (msgs ×ˢ Finset.univ) c fuel cache ≤
      p * (inputsAtKey pp l e seen).card + (1 - p) * (validInputs pp l e cache seen).card := by
  classical
  intro p
  let enc := trialInput pp l e
  let occup (m : ByteArray) := occupied (enc m) cache
  let good (m : ByteArray) := validRows accepted (enc m) cache
  have full : ∀ m, good m ⊆ occup m := by
    intro m r hr
    simp only [good, validRows, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    simp only [occup, occupied, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Option.isSome_iff_exists.mpr ⟨hr.choose, hr.choose_spec.2⟩
  have count := count_rows pp l e msgs occup (inputsAtKey pp l e seen) (by
    intro m hm r hr
    simp only [occup, occupied, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hr
    exact Finset.mem_filter.mpr ⟨covers _ _ hw, messageKey_trial ..⟩)
  have validCount := count_rows pp l e msgs good (validInputs pp l e cache seen) (by
    intro m hm r hr
    simp only [good, validRows, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨w, ok, hw⟩ := hr
    exact Finset.mem_filter.mpr ⟨covers _ _ hw, messageKey_trial .., w, ok, hw⟩)
  have perMessage (m : ByteArray) :=
    CyclicDigest.selection_mass_le pp l e m c fuel within cache (good m) (full m)
  unfold occupiedSelections
  rw [Finset.sum_product, Finset.mul_sum]
  calc
    _ ≤ ∑ m ∈ msgs, (p * (occup m).card + (1 - p) * (good m).card) :=
      Finset.sum_le_sum fun m _ => perMessage m
    _ = p * ((∑ m ∈ msgs, (occup m).card : Nat) : ℝ≥0∞) +
        (1 - p) * ((∑ m ∈ msgs, (good m).card : Nat) : ℝ≥0∞) := by
      simp only [Finset.sum_add_distrib, Nat.cast_sum, Finset.mul_sum]
    _ ≤ _ := by gcongr

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest
