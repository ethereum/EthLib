module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.StoppedFinder

/-!
# Reserving the pre-signing mass at its actual search boundary

A search reads its randomizer after the adversary has chosen the request.

The first attempt at a key fixes the entry cache and footprint used to price that search.

Later probes and unsuccessful signing replies do not change that snapshot.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest

open Constants HashSig OracleComp OracleSpec CachedCodeword PostSigning randomOracle.Partners
open scoped ENNReal

abbrev Key := Layer × UInt32
abbrev Entry := HashSpec.QueryCache × Finset HashInput
abbrev Snapshots := Key → Option Entry

/-- Read the live state until the first attempt saves this key's entry. -/
def entry (saved : Snapshots) (k : Key) (now : Entry) : Entry := (saved k).getD now

/-- Record the state at the first attempt only, including attempts that later exhaust the finder. -/
noncomputable def begin (saved : Snapshots) (k : Key) (now : Entry) : Snapshots :=
  Function.update saved k (some (entry saved k now))

/-- Taking a snapshot changes no current mass at any key. -/
theorem entry_begin (saved : Snapshots) (k j : Key) (now : Entry) :
    entry (begin saved k now) j now = entry saved j now := by
  by_cases same : j = k
  · subst j
    simp [begin, entry]
  · simp [entry, begin, Function.update_of_ne same]

/-- A later cache extension, failed signing reply or repeated search keeps the booked entry. -/
theorem entry_later (saved : Snapshots) (k : Key) (now later : Entry) :
    entry (begin saved k now) k later = entry saved k now := by simp [entry, begin]

/-- The old partnered-selection contribution at one signing key. -/
noncomputable def searchMass (pp : PublicParam) (c fuel : Nat) (k : Key) (s : Entry) : ℝ≥0∞ :=
  let p : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
  p * partneredSelections pp k.1 k.2 (activeMessages pp k.1 k.2 s.2 ×ˢ Finset.univ) c fuel s.1

/-- The reserve which pays for the paired mass before the first attempted search at this key. -/
noncomputable def searchReserve (pp : PublicParam) (c fuel : Nat) (k : Key) (s : Entry) : ℝ≥0∞ :=
  let ε : ℝ≥0∞ := 1 / 2 ^ 128
  ε * ((validInputs pp k.1 k.2 s.1 s.2).card *
    occupiedSelections pp k.1 k.2 (activeMessages pp k.1 k.2 s.2 ×ˢ Finset.univ) c fuel s.1)

private theorem mean_const (b : ℝ≥0∞) : freshMean (fun _ : HashOutput => b) = b :=
  tsum_prEvent_mul_of_const_on_support _ (fun _ _ => rfl)

private theorem mean_scale (b : ℝ≥0∞) (f : HashOutput → ℝ≥0∞) :
    freshMean (fun v => b * f v) = b * freshMean f := by
  simp only [freshMean, ← ENNReal.tsum_mul_left, mul_left_comm]

private theorem mean_sum (keys : Finset Key) (f : Key → HashOutput → ℝ≥0∞) :
    freshMean (fun v => ∑ k ∈ keys, f k v) = ∑ k ∈ keys, freshMean (f k) := by
  simp only [freshMean, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)

/-- Any fresh physical query pays the increase in total live and booked mass.

Only its own still-live signing key can contribute a nonconstant term. -/
theorem snapshot_probe (pp : PublicParam) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32)
    (keys : Finset Key) (saved : Snapshots) (cache : HashSpec.QueryCache) (seen : Finset HashInput)
    (covers : ∀ b w, cache b = some w → b ∈ seen) (a : HashInput) (cold : cache a = none) :
    let now : Entry := (cache, seen)
    let next (v : HashOutput) : Entry := (cache.cacheQuery a v, insert a seen)
    let F (s : Entry) := ∑ k ∈ keys, searchMass pp c fuel k (entry saved k s)
    let R (s : Entry) := ∑ k ∈ keys, searchReserve pp c fuel k (entry saved k s)
    freshMean (fun v => F (next v)) + R now ≤ F now + freshMean (fun v => R (next v)) := by
  classical
  intro now next F R
  have one (k : Key) :
      freshMean (fun v => searchMass pp c fuel k (entry saved k (next v))) +
        searchReserve pp c fuel k (entry saved k now) ≤
      searchMass pp c fuel k (entry saved k now) +
        freshMean (fun v => searchReserve pp c fuel k (entry saved k (next v))) := by
    rcases k with ⟨l, e⟩
    cases held : saved (l, e) with
    | some snapshot => simp [entry, held, mean_const]
    | none =>
      simp only [entry, held, Option.getD_none]
      by_cases belongs : messageKey pp a = some (l, e)
      · simpa only [searchMass, searchReserve, now, next, mean_scale] using
          compensate_active pp l e c fuel within cache seen covers a belongs cold
      · have invariant (v : HashOutput) :=
          foreign_probe pp l e c fuel within cache seen a belongs cold v
        have hF (v : HashOutput) : searchMass pp c fuel (l, e) (next v) =
            searchMass pp c fuel (l, e) now :=
          congrArg (_ * ·) (invariant v).2.2
        have hR (v : HashOutput) : searchReserve pp c fuel (l, e) (next v) =
            searchReserve pp c fuel (l, e) now := by
          simp only [searchReserve, next, now, (invariant v).1, (invariant v).2.1]
        simp only [hF, hR, mean_const, le_refl]
  simp only [F, R, mean_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => one k

/-- A later successful release can redeem the pre-search reserve even after intervening hash calls.

This is the claim available at the first independent private randomizer draw. -/
theorem fresh_search_booking (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32) (saved : Snapshots) (coldKey : saved (l, e) = none)
    (cache : HashSpec.QueryCache) (seen : Finset HashInput)
    (covers : ∀ b w, cache b = some w → b ∈ seen)
    (later : Entry) :
    let now : Entry := (cache, seen)
    let booked := entry (begin saved (l, e) now) (l, e) later
    (CODE_SIZE / 2 ^ 128 : ℝ≥0∞) * freshStopped pp l e m c fuel cache ≤
      (2 ^ 128)⁻¹ * (searchMass pp c fuel (l, e) booked +
        (validInputs pp l e booked.1 booked.2).card) := by
  dsimp only
  rw [entry_later]
  simp only [entry, coldKey, Option.getD_none]
  exact
    fresh_stopped_le pp l e m c fuel within cache seen covers

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest
