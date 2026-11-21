module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PriorMessages
public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.ForeignKey

/-!
# Foreign probes and the first signing registration

The leanXMSS draft in "The scheme" associates each WOTS+C key with its layer and epoch.
Selection masses use the whole physical footprint but depend only on inputs at that signing key.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest

open Constants HashSig OracleSpec OracleComp CachedCodeword PostSigning randomOracle.Partners
open scoped ENNReal

/-- A fresh probe at another key leaves both selection masses and the count at this key unchanged. -/
theorem foreign_probe (pp : PublicParam) (l : Layer) (e : UInt32) (c fuel : Nat)
    (within : c + fuel ≤ 2 ^ 32) (cache : HashSpec.QueryCache) (seen : Finset HashInput)
    (a : HashInput) (foreign : messageKey pp a ≠ some (l, e)) (cold : cache a = none) (v : HashOutput) :
    let upd := cache.cacheQuery a v
    let after := insert a seen
    let family := fun hist => activeMessages pp l e hist ×ˢ (Finset.univ : Finset Randomizer)
    validInputs pp l e upd after = validInputs pp l e cache seen ∧
      occupiedSelections pp l e (family after) c fuel upd = occupiedSelections pp l e (family seen) c fuel cache ∧
      partneredSelections pp l e (family after) c fuel upd = partneredSelections pp l e (family seen) c fuel cache := by
  classical
  intro upd after family
  have noMsg : messageOfInput pp l e a = none := by
    unfold messageOfInput
    split
    next ex =>
      obtain ⟨m, r, rfl⟩ := ex
      exact (foreign (messageKey_trial ..)).elim
    next => rfl
  have fam : family after = family seen := by
    simp [family, after, activeMessages, noMsg]
  rw [fam]
  constructor
  · ext b
    by_cases same : b = a
    · subst b
      simp [validInputs, foreign]
    · simp [validInputs, after, upd, same]
  have per (i : ByteArray × Randomizer) := unchanged_at_other_key (messageKey pp) validDigest accepted
    (trialInput pp l e i.1) ((List.range' c fuel).map (trialRandomizer i.2))
    (trials_nodup pp l e i.1 i.2 c fuel within) cache a cold (fun r => by rwa [messageKey_trial]) v
  constructor
  · unfold occupiedSelections
    apply Finset.sum_congr rfl
    intro i _
    simpa only [cachedMass, selected, findCodeword_position] using (per i).1
  · unfold partneredSelections
    apply Finset.sum_congr rfl
    intro i _
    simpa only [partneredMass, selected, findCodeword_position] using (per i).2

/-- A registration may overwrite a digest but cannot reopen a previously registered key. -/
theorem record_stays_registered (pp : PublicParam) (a : HashInput) (cache : HashSpec.QueryCache)
    (old : (Layer × UInt32) → Option Digest) (k : Layer × UInt32) (registered : (old k).isSome) :
    ((record pp a cache old) k).isSome := by
  classical
  cases hk : messageKey pp a with
  | none => simpa [record, hk] using registered
  | some key =>
    cases hw : cache a with
    | none => simpa [record, hk, hw] using registered
    | some w =>
      by_cases valid : (digits w).isSome
      · by_cases eq : k = key
        · subst key
          simp [record, hk, hw, valid]
        · simpa [record, hk, hw, valid, Function.update_of_ne eq] using registered
      · simpa [record, hk, hw, valid] using registered

/-- The mass is exposed once at the first effective registration.
Subsequent notices at the same key have zero retirement charge. -/
theorem first_registration (pp : PublicParam) (a : HashInput) (cache : HashSpec.QueryCache)
    (old : (Layer × UInt32) → Option Digest) (k : Layer × UInt32) (mass : ℝ≥0∞) :
    let after := record pp a cache old
    (if old k = none then mass else 0) =
      (if after k = none then mass else 0) + (if old k = none ∧ (after k).isSome then mass else 0) := by
  intro after
  cases h : old k with
  | none => cases after k <;> simp
  | some d =>
    have stays := record_stays_registered pp a cache old k (by simp [h])
    change (after k).isSome = true at stays
    cases h' : after k <;> simp_all

/-- Only a successful message trial at this key can retire a positive pre-registration charge. -/
theorem first_registration_trial (pp : PublicParam) (a : HashInput) (cache : HashSpec.QueryCache)
    (old : (Layer × UInt32) → Option Digest) (k : Layer × UInt32) (before : old k = none)
    (after : ((record pp a cache old) k).isSome) :
    messageKey pp a = some k ∧ ∃ w ∈ accepted, cache a = some w := by
  classical
  cases hk : messageKey pp a with
  | none => simp [record, hk, before] at after
  | some key =>
    cases hw : cache a with
    | none => simp [record, hk, hw, before] at after
    | some w =>
      by_cases valid : (digits w).isSome
      · by_cases eq : k = key
        · subst key
          exact ⟨rfl, w, (mem_accepted w).2 valid, rfl⟩
        · simp [record, hk, hw, valid, Function.update_of_ne eq, before] at after
      · simp [record, hk, hw, valid, before] at after

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest
