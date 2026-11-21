module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchLedgerCount
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchLedgerPrice
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialMoment

/-!
# The first-search price on the same physical run as the trial moment

The snapshot table and the valid-word counter observe one sequence of native full public replies.

The global physical cap keeps the two counts within the range used in the moment estimate.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger

open Constants HashSig OracleComp OracleSpec PostSigning CachedCodeword
open RealClient.GraphPrefix RealClient.GraphPrefix.TrialGraphWatch
open scoped ENNReal Classical

/-- The current graph pays for old partners from its realized pre-registration trials and successes.
-/
theorem watched_product {Note R α : Type} (pp : PublicParam) (keys : Finset Key) (cut : Note →
    Option Key)
    (notice : Note → R → R) (registered : R → HashInput → Bool)
    (tracks : TracksRegistration pp cut notice registered)
    (r : R) (empty : ∀ b, registered r b = false) (c fuel : Nat) (within : c + fuel ≤ 2 ^ 32)
    (q : Nat) (p : OracleComp (Spec Note) α) (left : Nat) (room : left ≤ q) :
    let rate : ℝ≥0∞ := CODE_SIZE / 2 ^ 128
    let ε : ℝ≥0∞ := 1 / 2 ^ 128
    let initial : Observed R × History := ((((((∅, ∅), []), r), 0), 0, 0), ((∅, ∅), fun _ => none))
    let run := (simulateQ (watched pp cut notice registered q)
      (WeightedCap.capCompOpt fee left p)).run initial
    rate * (∑' z, Pr{let u ← run}[u = z] * total keys (searchMass pp c fuel) z.2.2) ≤
      ε * (∑' z, Pr{let u ← run}[u = z] *
        ((z.2.1.2.2 : ℝ≥0∞) * (rate * z.2.1.2.1 + (1-rate) * z.2.1.2.2))) := by
  intro rate ε initial run
  let capped := WeightedCap.capCompOpt fee left p
  have view := project_watch pp cut notice registered q (fun w => (digits w).isSome) capped initial
  let proj := fun s : Observed R × History => (s.1.1.1.1, s.2)
  change Prod.map id proj <$> run = (simulateQ (handler pp cut) capped).run (proj initial) at view
  have price := empty_price pp cut c fuel within keys capped
  dsimp only at price
  rw [← view, tsum_prEvent_map_mul, tsum_prEvent_map_mul] at price
  refine price.trans (mul_le_mul_right (tsum_le_tsum fun z => ?_) ε)
  by_cases reached : z ∈ support run
  · have counted := counted_cap pp keys cut notice registered tracks q p left initial
      (counted_empty pp keys registered r empty) (by simpa [initial] using room) reached
    have hN : total keys (fun k h => (inputCount pp k h : ℝ≥0∞)) z.2.2 ≤ z.2.1.2.1 := by
      simpa [total, initialCount, Nat.cast_sum] using (Nat.cast_le (α := ℝ≥0∞)).mpr counted.inputs
    have hV : total keys (fun k h => (validCount pp k h : ℝ≥0∞)) z.2.2 ≤ z.2.1.2.2 := by
      simpa [total, initialCount, Nat.cast_sum] using (Nat.cast_le (α := ℝ≥0∞)).mpr counted.valid
    exact mul_le_mul_right (mul_le_mul' hV (add_le_add (mul_le_mul_right hN _)
      (mul_le_mul_right hV _))) _
  · simp only [prEvent_eq_zero_of_not_mem_support run reached, zero_mul, le_refl]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.EarlierDigest.Ledger
