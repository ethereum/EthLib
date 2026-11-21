module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.EarlierDigest
public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.Compensation

/-!
# The cost of partners formed before signing

The leanXMSS draft in "WOTS+C", paragraph "Signing", scans candidate randomizers until one gives a valid digest.

Partners share their layer and OTS key.
Their physical hash inputs can contain different messages.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest

open Constants HashSig OracleSpec OracleComp CachedCodeword PostSigning randomOracle.Partners
open scoped ENNReal

private theorem valid_of_digest (w : HashOutput) (d : Digest) (h : validDigest w = some d) :
    w ∈ accepted := by
  unfold validDigest at h
  split at h
  · exact (mem_accepted w).2 ‹_›
  · contradiction

private theorem trial_injective (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    Function.Injective (trialInput pp l e msg) := by
  intro r s same
  have inputs := (thInput_inj (ByteArray.ext (Array.toList_inj.mp same))).2.2
  exact packBytes_injective (HashSig.byteArray_append_inj inputs rfl).2

open Classical in
/-- The occupied, valid physical inputs at this key, across messages of every length. -/
noncomputable def validInputs (pp : PublicParam) (l : Layer) (e : UInt32)
    (cache : HashSpec.QueryCache) (seen : Finset HashInput) : Finset HashInput :=
  seen.filter fun b => messageKey pp b = some (l, e) ∧ ∃ w ∈ accepted, cache b = some w

/-- Inserting a fresh message trial increments the valid count exactly when its word decodes. -/
theorem validInputs_after (pp : PublicParam) (l : Layer) (e : UInt32) (cache : HashSpec.QueryCache)
    (seen : Finset HashInput) (a : HashInput) (addr : messageKey pp a = some (l, e))
    (cold : cache a = none) (w : HashOutput) :
    (validInputs pp l e (cache.cacheQuery a w) (insert a seen)).card =
      if w ∈ accepted then (validInputs pp l e cache seen).card + 1 else (validInputs pp l e cache seen).card := by
  classical
  let before := validInputs pp l e cache seen
  have outside : a ∉ before := by simp [before, validInputs, cold]
  have shape : validInputs pp l e (cache.cacheQuery a w) (insert a seen) =
      if w ∈ accepted then insert a before else before := by
    ext b
    by_cases same : b = a
    · subst b
      by_cases ok : w ∈ accepted <;> simp [validInputs, before, addr, QueryCache.cacheQuery_self, cold, ok]
    · by_cases ok : w ∈ accepted <;>
        simp [validInputs, before, same, ok]
  rw [shape]
  split <;> simp_all [Finset.card_insert_of_notMem, before]

/-- Sum of the actual finder probabilities for a finite family of messages and starting randomizers.
Each selected position must already contain an accepted full hash word in the entry cache. -/
noncomputable def occupiedSelections (pp : PublicParam) (l : Layer) (e : UInt32)
    (family : Finset (ByteArray × Randomizer)) (c fuel : Nat) (cache : HashSpec.QueryCache) : ℝ≥0∞ :=
  ∑ i ∈ family, Pr{let z ← (simulateQ randomOracle (selected pp l e i.1 i.2 c fuel)).run cache}[
    ∃ r ∈ validRows accepted (trialInput pp l e i.1) cache, z.1 = some r]

/-- Sum of the probabilities that the actual finder selects a row with another valid,
same-key input bearing the same digest in the entry cache. -/
noncomputable def partneredSelections (pp : PublicParam) (l : Layer) (e : UInt32)
    (family : Finset (ByteArray × Randomizer)) (c fuel : Nat) (cache : HashSpec.QueryCache) : ℝ≥0∞ :=
  ∑ i ∈ family, Pr{let z ← (simulateQ randomOracle (selected pp l e i.1 i.2 c fuel)).run cache}[
    ∃ r, z.1 = some r ∧ EarlierDigest.Partner pp cache (trialInput pp l e i.1 r)]

/-- A fresh physical query at this signing key pays for every newly partnered selection.
The valid input count includes all messages at this key, regardless of the measured family. -/
theorem compensate_finders (pp : PublicParam) (l : Layer) (e : UInt32)
    (family : Finset (ByteArray × Randomizer)) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32)
    (cache : HashSpec.QueryCache) (seen : Finset HashInput) (covers : ∀ b w, cache b = some w → b ∈ seen)
    (a : HashInput) (addr : messageKey pp a = some (l, e)) (cold : cache a = none) :
    let p : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
    let ε : ℝ≥0∞ := 1 / 2 ^ 128
    let H := occupiedSelections pp l e family c fuel
    let Φ := partneredSelections pp l e family c fuel
    let V := (validInputs pp l e cache seen).card
    let upd := fun v => cache.cacheQuery a v
    p * freshMean (fun v => Φ (upd v)) + ε * (V * H cache) ≤
      p * Φ cache + ε * freshMean (fun v => ((validInputs pp l e (upd v) (insert a seen)).card : ℝ≥0∞) * H (upd v)) := by
  classical
  have nonempty : accepted.Nonempty := by
    by_contra! empty
    have p := prEvent_accepted
    rw [empty] at p
    have positive : (0 : ℝ≥0∞) < CODE_SIZE / 2 ^ 128 := ENNReal.div_pos (by norm_num [CODE_SIZE]) (by norm_num)
    simp [← p] at positive
  obtain ⟨ref, ok⟩ := nonempty
  have rate := priorPairRate_le (messageKey pp) validDigest cache a (validInputs pp l e cache seen)
    ((1 : ℝ≥0∞) / 2 ^ 128) (fun b hk w hw d hd => Finset.mem_filter.mpr
      ⟨covers b w hw, hk.trans addr, w, valid_of_digest w d hd, hw⟩) prEvent_validDigest
  have bound := compensate_sum family (messageKey pp) validDigest accepted
    (fun i => trialInput pp l e i.1) (fun i _ => trial_injective pp l e i.1)
    (fun i => (List.range' c fuel).map (trialRandomizer i.2))
    (fun i _ => trials_nodup pp l e i.1 i.2 c fuel within) cache a cold ref ok
    ((1 : ℝ≥0∞) / 2 ^ 128) (validInputs pp l e cache seen).card rate valid_of_digest prEvent_validDigest
  dsimp only
  simp only [occupiedSelections, partneredSelections, selected, findCodeword_position,
    validInputs_after pp l e cache seen a addr cold, apply_ite Nat.cast, Nat.cast_add, Nat.cast_one]
  simpa only [prEvent_accepted, cachedMass, partneredMass] using bound

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest
