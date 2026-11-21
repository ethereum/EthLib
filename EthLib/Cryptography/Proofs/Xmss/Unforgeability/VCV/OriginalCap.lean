module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PaidSources
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealClient
import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial.Cost
public import VCVio.OracleComp.QueryTracking.WeightedCap
public import VCVio.OracleComp.QueryTracking.WriterCost.StateT

/-!
# The original query cap on the current strong-forgery client

The cap counts each physical hash before the two seed tables replace it.

The original all-execution budget makes the outer stop impossible in the real game.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient

open OracleComp OracleSpec
open XmssSecurity (HashSpec HashOutput MasterSeed)
open scoped Classical
abbrev Raw := HashSpec.QueryCache

/-- A coin is free and a hash costs one, including a warm hash. -/
@[expose] def worldFee : World.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

private theorem metered_run {α : Type} (p : OracleComp World α) (s : Raw) :
    (fun z : (α × Nat) × Raw => (z.1.1, z.2, z.1.2)) <$> (simulateQ countedOracle p).runAdd.run s =
      (simulateQ (HashSpec.romImpl.extendState (fun t _ _ _ n => n + worldFee t)) p).run (s,
        0) := by
  have real : simulateQ HashSpec.romImpl
      (simulateQ ((QueryImpl.id' World).withAddCost worldFee) p).runAdd =
        (simulateQ countedOracle p).runAdd := by
    rw [QueryImpl.simulateQ_withAddCost_runAdd_fusion]
    rfl
  simpa only [real, Nat.zero_add] using run_withAddCost_eq_extendState worldFee
    p HashSpec.romImpl s 0

/-- A cap on the current real observation retains the complete raw ROM table and never stops. -/
theorem observe_cap (A : Adversary) (q : Nat) (bounded : HasHashQueryBound A q) :
    (simulateQ HashSpec.romImpl (WeightedCap.capCompOpt worldFee q (observe A))).run ∅ =ᵈ
      (fun z : Outcome × Raw => (some z.1,
        z.2)) <$> (simulateQ HashSpec.romImpl (observe A)).run ∅ := by
  let aux := fun (t : World.Domain) (_ : Raw) (_ : World.Range t) (_ : Raw)
      (n : Nat) => n + worldFee t
  let impl := HashSpec.romImpl.extendState aux
  have charge : WeightedCap.ReportsCost impl worldFee Prod.snd := by
    intro t s w hw
    exact ((QueryImpl.mem_support_extendState_run_iff HashSpec.romImpl aux t s w).mp hw).2
  have limit : ∀ w ∈ support ((simulateQ impl (observe A)).run (∅, 0)), w.2.2 ≤ 0 + q := by
    intro w hw
    rw [← metered_run, support_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    apply (Nat.zero_add q).symm ▸ (hashQueryBound_iff A q).1 bounded v.1
    have joined : (simulateQ countedOracle (observe A)).runAdd =
        (simulateQ countedOracle (observe A)).run := id_map _
    have counted : countedObservation A =
        (fun x : (Outcome × Nat) × Raw => x.1) <$>
          (simulateQ countedOracle (observe A)).runAdd.run ∅ := by
      rw [joined, countedObservation, StateT.run'_eq]
      rfl
    rw [counted, support_map]
    exact ⟨v, hv, rfl⟩
  have h := (WeightedCap.evalDist_capCompOpt impl worldFee Prod.snd charge (observe A) q (∅,
      0) limit).map
    (Prod.map id Prod.fst)
  have left := extendState_run_proj_eq HashSpec.romImpl aux
    (WeightedCap.capCompOpt worldFee q (observe A)) ∅ 0
  have right := extendState_run_proj_eq HashSpec.romImpl aux (observe A) ∅ 0
  change (Prod.map id Prod.fst <$> _) =ᵈ (Prod.map id Prod.fst <$> _) at h
  rw [← left, ← right]
  refine h.trans (EvalDistEq.of_eq ?_)
  simp only [Functor.map_map]
  rfl

/-- Every explicit master derivation represents exactly one physical hash. -/
@[expose] def masterFee : SeedSpec.Domain → Nat
  | .inl t => worldFee t
  | .inr _ => 1

private def masterIndex (s : MasterSeed) : SeedSpec.Domain → World.Domain
  | .inl t => t
  | .inr _ => .inr (XmssSecurity.seedHashInput s)

private theorem master_range (s : MasterSeed) (t : SeedSpec.Domain) :
    World.Range (masterIndex s t) = SeedSpec.Range t := by cases t <;> rfl

private theorem master_cap {α : Type} (s : MasterSeed) (p : OracleComp SeedSpec α) (q : Nat) :
    simulateQ (seedEncoding.deriveImpl s) (WeightedCap.capCompOpt masterFee q p) =
      WeightedCap.capCompOpt worldFee q (simulateQ (seedEncoding.deriveImpl s) p) := by
  let forward := fun t => (cast (master_range s t)) <$>
    (liftM (World.query (masterIndex s t)) : OracleComp World _)
  have same : forward = seedEncoding.deriveImpl s := by
    funext t
    rcases t with (n | x) | u <;> rfl
  rw [← same]
  exact WeightedCap.simulateQ_capCompOpt_single_query masterFee worldFee (masterIndex s)
    (fun t => cast (master_range s t)) (fun t => by cases t <;> rfl) p q

private theorem free_prefix {α β : Type} (draw : ProbComp α) (k : α → OracleComp World β)
    (q : Nat) :
    WeightedCap.capCompOpt worldFee q ((liftM draw : OracleComp World α) >>= k) =
      (liftM draw : OracleComp World α) >>= fun x => WeightedCap.capCompOpt worldFee q (k x) := by
  induction draw using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n f ih =>
    simp only [liftM_bind, bind_assoc]
    have forward : (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp World _) =
        liftM (World.query (.inl n)) := rfl
    rw [forward, WeightedCap.capCompOpt_query_bind]
    simp only [worldFee, zero_le, ↓reduceIte, Nat.sub_zero]
    exact bind_congr ih

/-- The original budget preserves the master-source observation and the whole real cache. -/
theorem master_cap_real (A : Adversary) (q : Nat) (bounded : HasHashQueryBound A q) :
    (simulateQ HashSpec.romImpl ((liftM XmssSecurity.sampleMasterSeed : OracleComp World _) >>=
      fun s =>
      simulateQ (seedEncoding.deriveImpl s)
        (WeightedCap.capCompOpt masterFee q (masterSource A)))).run ∅ =ᵈ
      (fun z : Outcome × Raw => (some z.1,
        z.2)) <$> (simulateQ HashSpec.romImpl (observe A)).run ∅ := by
  have h := observe_cap A q bounded
  conv at h => lhs; rw [observe_eq_master, free_prefix]
  simpa only [master_cap] using h

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
