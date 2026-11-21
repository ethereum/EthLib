module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SeedCapSquare
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.SignerReplay

/-!
# The production strong-forgery experiment after the two hidden-seed steps

The initial paid call cannot be an ordinary guess in either capped experiment.

Both losses use the number of remaining physical calls.

A normal signing error stays in the observation and outer exhaustion contributes no win.

Source: leanXMSS draft, sections "The scheme" and "Security".
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient

open OracleComp OracleSpec
open XmssSecurity (HashSpec HashOutput MasterSeed)
open scoped Classical ENNReal

/-- Test the strong-forgery observation only when the physical cap returned a candidate. -/
@[expose] def accepted : Option Outcome → Prop
  | none => False
  | some z => wins z = true

private theorem real_win (A : Adversary) (q : Nat) (bounded : HasHashQueryBound A q) :
    Pr{let s ← XmssSecurity.sampleMasterSeed
       let z ← (simulateQ (seedEncoding.realImpl s) (WeightedCap.capCompOpt masterFee q
         (masterSource A))).run ∅}[
      accepted z.1] = forgeAdvantage A := by
  have old := (master_cap_real A q bounded).prEvent_eq (fun z => accepted z.1)
  rw [simulateQ_bind, StateT.run_bind, roSim.run_liftM, bind_map_left] at old
  rw [forgeAdvantage_eq_statelessForgeAdvantage]
  have game : statelessForgeAdvantage A =
      Pr{let z ← (simulateQ HashSpec.romImpl (observe A)).run ∅}[wins z.1 = true] := by
    unfold statelessForgeAdvantage statelessExperiment
    refine (prEvent_forgetHashCost (statelessGameCore A) (fun b => b = true)).trans ?_
    rw [← stateless_core, simulateQ_map, StateT.run'_map', prEvent_map, StateT.run'_eq, prEvent_map]
  rw [game]
  change prEvent ((fun z : Option Outcome × Raw => accepted z.1) <$> (do
    let s ← XmssSecurity.sampleMasterSeed
    (simulateQ HashSpec.romImpl (simulateQ (seedEncoding.deriveImpl s)
      (WeightedCap.capCompOpt masterFee q (masterSource A)))).run ∅)) = _ at old
  simp only [map_bind] at old
  simpa only [SecretEncoding.realImpl, QueryImpl.simulateQ_compose, prEvent_map, accepted] using old

private def masterRaw : SeedSpec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False

private def paidRaw : Source.Domain → Prop
  | .inl (.inr (.inl _)) => True
  | _ => False

private theorem master_budget (A : Adversary) (q : Nat) :
    IsQueryBoundP (WeightedCap.capCompOpt masterFee q (masterSource A)) masterRaw (q-1) := by
  have head : ∃ k : HashOutput → OracleComp SeedSpec Outcome,
      masterSource A = liftM (SeedSpec.query (.inr ())) >>= k := by
    simp only [masterSource, sourceOf, bind_map_left]
    exact ⟨_, rfl⟩
  obtain ⟨k, eq⟩ := head
  rw [eq]
  apply WeightedCap.isQueryBoundP_capCompOpt_after_unprotected_unit_query
  · rintro ((n | t) | u) h <;> simp_all [masterRaw, masterFee, worldFee]
  · rfl
  · simp [masterRaw]

private theorem paid_budget (A : Adversary) (q : Nat) :
    IsQueryBoundP (WeightedCap.capCompOpt paidFee q (paidSource A)) paidRaw (q-1) := by
  have head : ∃ k : Unit → OracleComp Source Outcome,
      paidSource A = liftM (Source.query (.inl (.inr (.inr ())))) >>= k := ⟨_, rfl⟩
  obtain ⟨k, eq⟩ := head
  rw [eq]
  apply WeightedCap.isQueryBoundP_capCompOpt_after_unprotected_unit_query
  · rintro ((n | (t | u)) | x) h <;> simp_all [paidRaw, paidFee, ambientFee]
  · rfl
  · simp [paidRaw]

private theorem scheme_guess (t : Backend.Domain) :
    Pr{let s ← ($ᵗ HashOutput : ProbComp HashOutput)}[t ∈ Set.range (paidEncoding.enc s)] ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have unique : ∀ a b x y, paidEncoding.enc a x = paidEncoding.enc b y → a = b := by
    intro a b x y eq
    exact congrFun (prfEncoding_fix _ _ x y (Sum.inl.inj eq)) ()
  have h := prEvent_mem_range_enc_le paidEncoding unique t
  rw [Nat.card_eq_fintype_card, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- The capped private-source win and two seed-guess losses bound the keyed advantage.

The original stateless budget for all executions suffices.
-/
theorem forge_le_paid (A : Adversary) (q : Nat) (positive : 0 < q)
    (bounded : HasHashQueryBound A q) :
    forgeAdvantage A ≤
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl Backend PrfInput HashOutput)
        (WeightedCap.capCompOpt paidFee q (paidSource A))).run (∅, ∅)}[accepted z.1] +
        (q-1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ + (q-1 : Nat) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have first := seedEncoding.prEvent_realImpl_le_add_mul prEvent_mem_range_seedEncoding_le
    (p := masterRaw) (fun _ _ => trivial) (master_budget A q) (fun _ z => accepted z.1)
  rw [real_win A q bounded] at first
  simp only [OracleComp.prEvent_bind_const] at first
  have second := paidEncoding.prEvent_realImpl_le_add_mul scheme_guess
    (p := paidRaw) (fun _ _ => trivial) (paid_budget A q) (fun _ z => accepted z.1)
  simp only [OracleComp.prEvent_bind_const] at second
  have join := (capped_presample A q positive).prEvent_eq (fun z => accepted z.1)
  change prEvent ((fun z : Option Outcome × SecretEncoding.SplitCache HashSpec Unit HashOutput =>
      accepted z.1) <$> _) = prEvent ((fun z => accepted z.1) <$> (do
    let word ← ($ᵗ HashOutput : ProbComp HashOutput)
    let z ← (simulateQ (paidEncoding.realImpl word) (WeightedCap.capCompOpt paidFee q
      (paidSource A))).run ∅
    pure (z.1, SecretEncoding.paidUnitReadback HashSpec word z.2))) at join
  simp only [map_bind, bind_pure_comp, Functor.map_map] at join
  exact first.trans (add_le_add (join.le.trans second) le_rfl)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
