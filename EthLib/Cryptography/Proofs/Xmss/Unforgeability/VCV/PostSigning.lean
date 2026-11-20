module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CachedCodeword
public import VCVio.OracleComp.QueryTracking.RandomOracle.MarkedReplies
import EthLib.Cryptography.Proofs.Xmss.Address
import EthLib.Cryptography.Proofs.Xmss.TweakableHash

/-!
# Later hash queries at keys with an observed digest

The leanXMSS draft in "WOTS+C", paragraph "Signing", selects one message digest for a signature.

Fix the observed digest at each key before the caller continues.

Only a new message hash at a key with a recorded digest can make a new match.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.PostSigning

open HashSig Constants OracleSpec OracleComp CachedCodeword
open scoped ENNReal

/-- The caller knows at most one target digest for each layer and OTS key. -/
abbrev Targets := Layer → UInt32 → Option Digest

/-- The bytes of a message trial determine its layer and OTS key. -/
theorem trial_key {pp : PublicParam} {l k : Layer} {e f : UInt32}
    {m n : ByteArray} {r s : Randomizer}
    (same : trialInput pp l e m r = trialInput pp k f n s) : l = k ∧ e = f :=
  addrMsg_inj.mp (thInput_inj (ByteArray.ext (Array.toList_inj.mp same))).2.1

/-- Previously cold message addresses at keys with a fixed target. -/
@[expose] def watched (pp : PublicParam) (targets : Targets) (initial : HashSpec.QueryCache) :
    Set HashInput :=
  {b | initial b = none ∧ ∃ l e m r d, trialInput pp l e m r = b ∧ targets l e = some d}

/-- A full hash reply has the observed low half at the key named by its input. -/
@[expose] def repeats (pp : PublicParam) (targets : Targets) (b : HashInput)
    (w : HashOutput) : Prop :=
  ∃ l e m r, trialInput pp l e m r = b ∧ targets l e = some (halfOf 0 (ofOutput w))

/-- One fresh input can target only one earlier digest, even if many keys have signatures. -/
theorem prEvent_repeats (pp : PublicParam) (targets : Targets) (initial : HashSpec.QueryCache)
    (b : HashInput) (selected : b ∈ watched pp targets initial) :
    Pr{let w ← $ᵗ HashOutput}[repeats pp targets b w] ≤ (1 : ℝ≥0∞) / 2 ^ 128 := by
  obtain ⟨_, l, e, m, r, d, rfl, known⟩ := selected
  have chance : Pr{let w ← $ᵗ HashOutput}[halfOf 0 (ofOutput w) = d] =
      (1 : ℝ≥0∞) / 2 ^ 128 := by
    rw [prEvent_halfOf_ofOutput (fun h => h = d)]
    simp
  apply (prEvent_mono _ _ (fun w => halfOf 0 (ofOutput w) = d) ?_).trans
  · exact chance.le
  · rintro w ⟨k, f, n, s, same, hit⟩
    obtain ⟨rfl, rfl⟩ := trial_key same
    exact Option.some.inj (hit.symm.trans known)

/-- Each new message hash at a watched key has at most one chance in 2^128 of a match.

The bound includes every adaptive caller and an arbitrary initial cache. -/
theorem prEvent_match_and_count {α : Type} (pp : PublicParam) (targets : Targets)
    (initial : HashSpec.QueryCache) (caller : OracleComp OracleWorld α) (q : Nat) :
    Pr{let z ← (simulateQ (unifFwdImpl HashSpec + HashSpec.randomOracle) caller).run initial}[
      (∃ l e m r d w, targets l e = some d ∧ initial (trialInput pp l e m r) = none ∧
        z.2 (trialInput pp l e m r) = some w ∧ halfOf 0 (ofOutput w) = d) ∧
        (randomOracle.occupiedAt (watched pp targets initial) z.2).encard ≤ q] ≤
      (q : ℝ≥0∞) / 2 ^ 128 := by
  have good : ¬ randomOracle.hasMatch
      (watched pp targets initial) (repeats pp targets) initial := by
    rintro ⟨b, watchedAt, w, cached, _⟩
    have cold := watchedAt.1
    rw [cold] at cached
    contradiction
  have bound := randomOracle.prEvent_hasMatch_and_count (watched pp targets initial)
    (repeats pp targets) ((1 : ℝ≥0∞) / 2 ^ 128) (by norm_num)
    (prEvent_repeats pp targets initial) caller initial good q
  apply (prEvent_mono _ _ _ ?_).trans
  · simpa [div_eq_mul_inv] using bound
  · rintro z ⟨⟨l, e, m, r, d, w, target, cold, cached, low⟩, cost⟩
    exact ⟨⟨_, ⟨cold, l, e, m, r, d, rfl, target⟩, w, cached,
      l, e, m, r, rfl, low ▸ target⟩, cost⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.PostSigning
