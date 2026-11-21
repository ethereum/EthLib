module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.EarlierDigest
public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.NewPartner

/-!
# Selecting a fresh trial that matches an older digest

The leanXMSS draft in "WOTS+C", paragraph "Signing", stops at the first valid trial.

Each distinct valid digest already at the key gives a fresh trial one chance in 2^128 to match.

Once that match occurs, every matching word gives the finder the same chance of reaching the trial.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest

open Constants HashSig OracleComp OracleSpec CachedCodeword PostSigning
open scoped ENNReal

/-- Some other message input at this signing key already contains the valid digest. -/
def CachedAtKey (pp : PublicParam) (cache : HashSpec.QueryCache) (a : HashInput) (d : Digest) :
    Prop :=
  ∃ b ≠ a, messageKey pp b = messageKey pp a ∧ ∃ w, cache b = some w ∧ validDigest w = some d

private theorem validDigest_iff (w : HashOutput) (d : Digest) :
    validDigest w = some d ↔ halfOf 0 (ofOutput w) = d ∧ (codeword? d).isSome := by
  unfold validDigest digits
  split <;> rename_i h
  · constructor
    · intro same
      exact ⟨Option.some.inj same, Option.some.inj same ▸ h⟩
    · exact fun same => congrArg some same.1
  · simp only [reduceCtorEq, false_iff]
    exact fun same => h (same.1 ▸ same.2)

private theorem matches_iff (pp : PublicParam) (cache : HashSpec.QueryCache) (a : HashInput)
    (v : HashOutput) :
    (∃ d, validDigest v = some d ∧ CachedAtKey pp cache a d) ↔
      CachedAtKey pp cache a (halfOf 0 (ofOutput v)) := by
  constructor
  · rintro ⟨d, hd, occurs⟩
    exact (validDigest_iff v d).mp hd |>.1.symm ▸ occurs
  · intro occurs
    refine ⟨_, (validDigest_iff _ _).2 ⟨rfl, ?_⟩, occurs⟩
    obtain ⟨_, _, _, w, _, hw⟩ := occurs
    exact ((validDigest_iff w _).1 hw).2

local notation "rom" => HashSpec.randomOracle

/-- The chance of selecting the probed trial factors through the number of distinct older digests.

The second factor is the chance the finder reaches this trial when it contains a valid word.
-/
theorem new_selection_gain (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32)
    (cache : HashSpec.QueryCache) (target : Randomizer) (ref : HashOutput)
    (ok : (digits ref).isSome) :
    let a := trialInput pp l e msg target
    (∑' v, Pr{let u ← $ᵗ HashOutput}[u = v] *
      Pr{let z ← (simulateQ rom (selected pp l e msg base c fuel)).run (cache.cacheQuery a v)}[
        z.1 = some target ∧ Partner pp (cache.cacheQuery a v) a]) =
      ((Nat.card {d : Digest // CachedAtKey pp cache a d} : ℝ≥0∞) / 2 ^ 128) *
        Pr{let z ← (simulateQ rom (selected pp l e msg base c fuel)).run (cache.cacheQuery a ref)}[
          z.1 = some target] := by
  intro a
  rw [selected, findCodeword_position]
  rw [randomOracle.Partners.new_selection_gain (messageKey pp) validDigest accepted
    (trialInput pp l e msg) _ (trials_nodup pp l e msg base c fuel within) cache target ref
    ((mem_accepted ref).2 ok) (fun w d hw => (mem_accepted w).2 (by
      obtain ⟨same, good⟩ := (validDigest_iff w d).1 hw
      simpa only [digits, same] using good))]
  congr 1
  change Pr{let u ← $ᵗ HashOutput}[∃ d, validDigest u = some d ∧ CachedAtKey pp cache a d] = _
  simp_rw [matches_iff]
  exact prEvent_halfOf_ofOutput (CachedAtKey pp cache a)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest
