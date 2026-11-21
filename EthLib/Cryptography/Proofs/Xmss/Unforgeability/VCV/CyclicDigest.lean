module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CachedCodeword
public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.CyclicMass

/-!
# Cached selections across the native randomizer counter

The leanXMSS draft, section "WOTS+C", paragraph "Signing", adds the trial number to the randomizer.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.CyclicDigest

open Constants HashSig OracleSpec OracleComp AcceptedScan CachedCodeword
open scoped ENNReal

private theorem trial_value (r : Randomizer) (n : Nat) :
    bytesToUint (trialRandomizer r n) = (bytesToUint r + n) % 2 ^ 128 := by
  rw [trialRandomizer_eq, EthLib.Base.bytesToUint_uintToBytes]
  change (bytesToUint r + n) % 2 ^ 128 % 2 ^ 128 = _
  rw [Nat.mod_mod]

/-- Two consecutive counter offsets add in the native 128-bit domain. -/
theorem trial_add (r : Randomizer) (n m : Nat) :
    trialRandomizer (trialRandomizer r n) m = trialRandomizer r (n + m) := by
  rw [trialRandomizer_eq, trial_value, trialRandomizer_eq, Nat.mod_add_mod, Nat.add_assoc]

private theorem trial_zero (r : Randomizer) : trialRandomizer r 0 = r := by
  have small : bytesToUint r < 2 ^ 128 := EthLib.Base.bytesToUint_lt r
  rw [trialRandomizer_eq, Nat.add_zero, Nat.mod_eq_of_lt small, EthLib.Base.uintToBytes_bytesToUint]

/-- A full period returns the original 16 bytes. -/
theorem trial_period (r : Randomizer) : trialRandomizer r (2 ^ 128) = r := by
  rw [← trial_zero r]
  conv_lhs => rw [trial_add, Nat.zero_add, trialRandomizer_eq, Nat.add_mod_right]
  rw [trialRandomizer_eq, Nat.add_zero]

/-- Add one to the native little-endian randomizer and wrap at the end of its 128-bit range. -/
def advance : Equiv.Perm Randomizer where
  toFun r := trialRandomizer r 1
  invFun r := trialRandomizer r (2 ^ 128 - 1)
  left_inv r := (trial_add r 1 (2 ^ 128 - 1)).trans (trial_period r)
  right_inv r := (trial_add r (2 ^ 128 - 1) 1).trans (trial_period r)

private theorem advance_pow (r : Randomizer) (c : Nat) : (advance ^ c) r = trialRandomizer r c := by
  induction c with
  | zero => exact (trial_zero r).symm
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    exact trial_add r n 1

private theorem trials (r : Randomizer) (c n : Nat) :
    (List.range' c n).map (trialRandomizer r) = orbit advance n ((advance ^ c) r) := by
  induction n generalizing c with
  | zero => simp [orbit]
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, orbit_succ, ih, advance_pow]
    congr 2
    rw [advance_pow]
    change trialRandomizer r (c + 1) = trialRandomizer ((advance ^ c) r) 1
    rw [advance_pow, trial_add]

/-- The full cached finder obeys the cyclic bound for any target set already present at entry. -/
theorem selection_mass_le (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32) (cache : HashSpec.QueryCache)
    (s : Finset Randomizer) (warm : s ⊆ occupied (trialInput pp l e msg) cache) :
    let p : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
    p * ∑ r : Randomizer,
      Pr{let z ← (simulateQ randomOracle (Option.map Prod.fst <$>
        Internal.findCodeword CachedCodeword.hash pp l e msg r c fuel)).run cache}[
          ∃ x ∈ s, z.1 = some x] ≤
      p * (occupied (trialInput pp l e msg) cache).card + (1 - p) * s.card := by
  classical
  let encode := trialInput pp l e msg
  have distinct (r : Randomizer) : ((orbit advance fuel r).map encode).Nodup := by
    obtain ⟨base, rfl⟩ := (advance ^ c).surjective r
    rw [← trials]
    exact trials_nodup pp l e msg base c fuel within
  have law := cyclic_selection_mass_le accepted encode cache s warm advance fuel distinct
  simp only [prEvent_accepted] at law
  simp only [findCodeword_position, trials]
  let weight := fun r => Pr{let z ←
    (simulateQ randomOracle (scan accepted encode (orbit advance fuel r))).run cache}[
      ∃ x ∈ s, z.1 = some x]
  change _ * (∑ r, weight ((advance ^ c) r)) ≤ _
  rw [Equiv.sum_comp (advance ^ c) weight]
  exact law

end EthLib.Cryptography.Xmss.Unforgeability.VCV.CyclicDigest
