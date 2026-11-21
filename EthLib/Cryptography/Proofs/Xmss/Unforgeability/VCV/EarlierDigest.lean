module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RegisteredDigest
public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.PartnerSet

/-!
# When a fresh query matches an older digest before signing

The leanXMSS draft in "WOTS+C", paragraph "Signing", takes the first valid digest in counter order.

A matching valid reply at another trial can stop the search before it reaches the older trial.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest

open Constants HashSig OracleComp OracleSpec CachedCodeword PostSigning
open scoped ENNReal

/-- A valid message digest is the low half of the full physical hash word. -/
@[expose] def validDigest (w : HashOutput) : Option Digest :=
  if (digits w).isSome then some (halfOf 0 (ofOutput w)) else none

/-- A cold word matches any one prescribed valid digest with probability at most one in 2^128. -/
theorem prEvent_validDigest (d : Digest) :
    Pr{let w ← $ᵗ HashOutput}[validDigest w = some d] ≤ (1 : ℝ≥0∞) / 2 ^ 128 := by
  refine (prEvent_mono _ _ (fun w => halfOf 0 (ofOutput w) = d) ?_).trans_eq ?_
  · intro w h
    unfold validDigest at h
    split at h
    · exact Option.some.inj h
    · contradiction
  · rw [prEvent_halfOf_ofOutput (fun v => v = d)]
    simp

/-- A partner is a different physical input at the same signing key with the same valid digest. -/
abbrev Partner (pp : PublicParam) (cache : HashSpec.QueryCache) (a : HashInput) : Prop :=
  randomOracle.Partners.Partner (messageKey pp) validDigest cache a

/-- Observe only the selected randomizer of the actual finder, retaining all its hash calls. -/
@[expose] def selected (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : Nat) : OracleComp HashSpec (Option Randomizer) :=
  Option.map Prod.fst <$> Internal.findCodeword CachedCodeword.hash pp l e msg base c fuel

local notation "rom" => HashSpec.randomOracle

/-- A fresh probe can match any older trial in the set and give it its first partner.

The gain is at most the original chance of selecting from the set, divided by 2^128.

Both sides use the same message and counter window. -/
theorem old_selection_gain_le (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32)
    (cache : HashSpec.QueryCache) (a : HashInput) (fresh : cache a = none) (s : Finset Randomizer)
    (earlier : ∀ r ∈ s, ¬Partner pp cache (trialInput pp l e msg r) ∧
      ∃ w, cache (trialInput pp l e msg r) = some w ∧ (digits w).isSome) :
    (∑' v, Pr{let u ← $ᵗ HashOutput}[u = v] *
      Pr{let z ← (simulateQ rom (selected pp l e msg base c fuel)).run (cache.cacheQuery a v)}[
        ∃ r ∈ s, z.1 = some r ∧ Partner pp (cache.cacheQuery a v) (trialInput pp l e msg r)]) ≤
      ((1 : ℝ≥0∞) / 2 ^ 128) *
        Pr{let z ← (simulateQ rom (selected pp l e msg base c fuel)).run cache}[
          ∃ r ∈ s, z.1 = some r] := by
  rw [selected, findCodeword_position]
  apply randomOracle.Partners.selection_gain_set_le accepted (trialInput pp l e msg)
    ((List.range' c fuel).map (trialRandomizer base)) (trials_nodup pp l e msg base c fuel within)
    cache a fresh (messageKey pp) validDigest s _ _ _ prEvent_validDigest
  · intro r hr
    obtain ⟨old, w, present, good⟩ := earlier r hr
    exact ⟨old, w, halfOf 0 (ofOutput w), present, by simp [validDigest, good]⟩
  · intro word d h
    apply (mem_accepted word).2
    by_contra reject
    simp [validDigest, reject] at h

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest
