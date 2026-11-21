module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TrialGraphExpectation
public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedGraph

/-!
# Pricing graph failures in the same physical experiment as the message trials

The low halves at chain, leaf, and node addresses pay for both graph hazards.

The price uses the public inputs the adaptive caller actually stored before the pending fill.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch

open HashSig OracleComp OracleSpec TwoLayerGraph CanonicalGraph.PairedQueries
open Constants
open ChainGraph (Word Public)
open scoped ENNReal

/-- Any low-subgraph conflict or keyed target collision can use the same expected address charge. -/
theorem raw_low_price {α : Type} (pp : PublicParam) (left : Nat) (p : OracleComp Raw α) :
    let body := guardedGraph left p
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) body}[(lowGraph pp).Conflict
      ((subgraph pp).project z.2.1) ∨
        (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project z.2.1)] ≤
      mean ((simulateQ (graph pp).deferredImpl body).run ((∅, ∅), []))
        (fun z => (addressedInputs pp z.2.1.1).encard) / 2 ^ 127 := by
  intro body
  let f := subgraph pp
  let nk := TwoLayerGraph.keys pp
  have empty : ¬((lowGraph pp).Conflict (f.project (∅, ∅)) ∨ nk.TCHazard (f.project (∅, ∅))) := by
    change ¬((lowGraph pp).Conflict (∅, ∅) ∨ nk.TCHazard (∅, ∅))
    exact not_or.mpr ⟨(lowGraph pp).not_conflict_empty, CanonicalGraph.NodeKeys.not_tcHazard_empty⟩
  have charged := (f.isCharged nk.isCharged).prEvent_deferredFillDraw_le_expected empty
    (fun cache => 2 * ((addressedInputs pp cache).encard : ℝ≥0∞) / Nat.card Word)
    (potential_le_addressed pp) body
  have card : (Nat.card Word : ℝ≥0∞) = 2 ^ 128 := by
    rw [Nat.card_eq_fintype_card]
    norm_num [Word, digestBits]
  apply charged.trans_eq
  rw [card, show (2 : ℝ≥0∞) ^ 128 = 2 * 2 ^ 127 by rw [pow_succ, mul_comm]]
  have cancel (x : ℝ≥0∞) : 2 * x / (2 * 2 ^ 127) = x / 2 ^ 127 :=
    ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)
  simp only [cancel, mean, div_eq_mul_inv, ← ENNReal.tsum_mul_right, mul_assoc]

/--
The union of graph conflicts and off-path collisions is priced by its own expected public inputs.
-/
theorem raw_graph_price {α : Type} (pp : PublicParam) (left : Nat) (p : OracleComp Raw α) :
    let body := guardedGraph left p
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) body}[(graph pp).Conflict z.2.1
      ∨ OffPath pp z.2.1] ≤
      mean ((simulateQ (graph pp).deferredImpl body).run ((∅, ∅), []))
        (fun z => (addressedInputs pp z.2.1.1).encard) / 2 ^ 127 := by
  intro body
  refine (prEvent_mono_of_support _ _ _ ?_).trans (raw_low_price pp left p)
  rintro z hz (hit | off)
  · have ⟨before, filled, _⟩ := (graph pp).mem_support_deferredFillDraw_iff.mp hz
    have present := (normalized_path pp left p before).2
    have stable := RelabelState.fst_eq_of_mem_support_endFill filled
    have after : PairedPresence z.2.1 := by simpa only [PairedPresence, stable] using present
    exact Or.inl (lowConflict pp _ after hit)
  · exact Or.inr (lowCollision pp _ off)

/--
Free registration notices and trial counters share the same graph distribution, including refusals.
-/
theorem graph_price {Note A α : Type} (pp : PublicParam) (notice : Note → A → A)
    (registered : A → HashInput → Bool) (quota : Nat) (test : HashOutput → Bool)
    (body : OracleComp (Spec Note) α) (left : Nat) (reg : A) :
    let m := (simulateQ (observe pp notice registered quota test)
      (WeightedCap.capCompOpt fee left body)).run (((((∅, ∅), []), reg), 0), 0, 0)
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) (guardedGraph left (simulateQ erase body))}[
      (graph pp).Conflict z.2.1 ∨ OffPath pp z.2.1] ≤
        mean m (fun z => (addressedInputs pp z.2.1.1.1.1.1).encard) / 2 ^ 127 := by
  intro m
  have proj := erase_run pp notice registered quota test (WeightedCap.capCompOpt fee left body)
    (((((∅, ∅), []), reg), 0), 0, 0)
  rw [erase_cap] at proj
  have price := raw_graph_price pp left (simulateQ erase body)
  dsimp only at price
  unfold guardedGraph mean at price
  rw [← proj, tsum_prEvent_map_mul] at price
  exact price

/-- Price the actual low-keyed target event on the same observed run as the trial counters. -/
theorem low_price {Note A α : Type} (pp : PublicParam) (notice : Note → A → A)
    (registered : A → HashInput → Bool) (quota : Nat) (test : HashOutput → Bool)
    (body : OracleComp (Spec Note) α) (left : Nat) (reg : A) :
    let m := (simulateQ (observe pp notice registered quota test)
      (WeightedCap.capCompOpt fee left body)).run (((((∅, ∅), []), reg), 0), 0, 0)
    Pr{let z ← (graph pp).deferredFillDraw (pure ()) (guardedGraph left (simulateQ erase body))}[
      (lowGraph pp).Conflict ((subgraph pp).project z.2.1) ∨
        (TwoLayerGraph.keys pp).TCHazard ((subgraph pp).project z.2.1)] ≤
        mean m (fun z => (addressedInputs pp z.2.1.1.1.1.1).encard) / 2 ^ 127 := by
  intro m
  have proj := erase_run pp notice registered quota test (WeightedCap.capCompOpt fee left body)
    (((((∅, ∅), []), reg), 0), 0, 0)
  rw [erase_cap] at proj
  have price := raw_low_price pp left (simulateQ erase body)
  dsimp only at price
  unfold guardedGraph mean at price
  rw [← proj, tsum_prEvent_map_mul] at price
  exact price

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.TrialGraphWatch
