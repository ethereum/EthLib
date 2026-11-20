module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.WatchedClient
public import VCVio.OracleComp.QueryTracking.RandomOracle.MarkedReplies.Cost
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealClient
import all EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.ConcreteStatement

/-!
# Later digest matches under the original adversary's query bound

The leanXMSS draft in "Security" counts every call to the public hash.

The meter counts key generation, every signing attempt, the client and verification.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch

open Constants HashSig OracleComp OracleSpec PostSigning
open scoped ENNReal

variable {σ : Type}

/-- Use the actual parameter and carry the key-generation charge into the adaptive watch. -/
@[expose] noncomputable def countedSource (pass : QueryImpl World (OracleComp World))
    (seed : OracleComp World σ) (derive : σ → SeedPrf (OracleComp World)) (A : Adversary)
    (s : HashSpec.QueryCache × Nat) : ProbComp (Outcome × WatchState × Nat) := do
  let z ← (simulateQ randomOracle.Targets.publicMeter
    (seed >>= fun x => publicKeyOf (hashOf pass) (derive x))).run s
  let pp := z.1.publicParam
  (simulateQ (randomOracle.Targets.counted (record pp) (messageKey pp) low)
    (afterKey pass seed derive A z.1)).run (⟨z.2.1, fun _ => none, 0, false⟩, z.2.2)

/-- Charge each post-signing match against the same total count as the original source. -/
theorem prEvent_countedSource (pass : QueryImpl World (OracleComp World))
    (seed : OracleComp World σ)
    (derive : σ → SeedPrf (OracleComp World)) (A : Adversary) (s : HashSpec.QueryCache × Nat)
    (q : Nat) :
    Pr{let z ← countedSource pass seed derive A s}[z.2.1.hit = true ∧ z.2.2 ≤ q] ≤
      (q : ℝ≥0∞) / 2 ^ 128 := by
  apply prEvent_bind_le_of_forall_le_of_support
  intro z _
  apply (randomOracle.Targets.prEvent_hit_and_count _ _ _ ((1 : ℝ≥0∞) / 2 ^ 128)
    (by norm_num) ?_ _ _ rfl _ (Nat.zero_le _) q).trans
  · simp [div_eq_mul_inv]
  · intro b k _ d
    unfold low
    rw [prEvent_halfOf_ofOutput (fun h => h = d)]
    simp

/-- The source keeps the original outcome, complete cache and physical query count. -/
theorem countedSource_erase (pass : QueryImpl World (OracleComp World)) (seed : OracleComp World σ)
    (derive : σ → SeedPrf (OracleComp World)) (A : Adversary) (s : HashSpec.QueryCache × Nat) :
    (fun z => (z.1, (z.2.1.cache, z.2.2))) <$> countedSource pass seed derive A s =
      (simulateQ randomOracle.Targets.publicMeter (sourceOf pass seed derive A)).run s := by
  rw [← forget_watchedSource]
  simp only [countedSource, watchedSource, map_bind, simulateQ_bind, StateT.run_bind, bind_assoc]
  have passThrough {α : Type} (x : OracleComp World α) :
      simulateQ forget (simulateQ ordinary x) = x :=
    (QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := QueryImpl.id' World)
      (fun t => by simp [ordinary, forget, randomOracle.Targets.forget]) x).trans (simulateQ_id' x)
  simp only [passThrough]
  refine bind_congr fun seeded => bind_congr fun keyed => ?_
  exact randomOracle.Targets.counted_forget_run _ _ _ _ _ _

/-- Count all public operations of the original game, starting from its real empty cache. -/
@[expose] noncomputable def countedGame (A : Adversary) :
    ProbComp (Outcome × WatchState × Nat) := do
  let z ← (simulateQ randomOracle.Targets.publicMeter
    (liftM XmssSecurity.sampleMasterSeed : OracleComp World _)).run (∅, 0)
  let H := hashOf (QueryImpl.id' World)
  countedSource (QueryImpl.id' World) (schemeSeed H (ofSeed z.1)) (seedPrf H) A z.2

/-- Removing the watch gives the original execution under its public hash meter. -/
theorem countedGame_erase (A : Adversary) :
    (fun z => (z.1, (z.2.1.cache, z.2.2))) <$> countedGame A =
      (simulateQ randomOracle.Targets.publicMeter (observe A)).run (∅, 0) := by
  rw [observe_eq_source]
  simp only [countedGame, map_bind, countedSource_erase, simulateQ_bind, StateT.run_bind]

/-- The original cost bound applies to every execution of the game with registered targets. -/
theorem countedGame_projection (A : Adversary) :
    (fun z => (z.1, z.2.2)) <$> countedGame A = countedObservation A := by
  have h := congrArg (fun p : ProbComp (Outcome × HashSpec.QueryCache × Nat) =>
      (fun z => (z.1, z.2.2)) <$> p) (countedGame_erase A)
  rw [randomOracle.Targets.publicMeter_run] at h
  have handler : (unifFwdImpl HashSpec + HashSpec.randomOracle).withAddCost
      (randomOracle.Targets.hashCost (pub := HashSpec)) = countedOracle := by
    unfold countedOracle
    congr 1
    funext t
    cases t <;> rfl
  rw [handler] at h
  have view : (fun a : (Outcome × Multiplicative Nat) × HashSpec.QueryCache =>
      (a.1.1, Multiplicative.toAdd a.1.2)) = (fun a => a.1) := by
    funext ⟨⟨value, cost⟩, cache⟩
    rfl
  simp only [Functor.map_map, AddWriterT.runAdd, StateT.run_map, Nat.zero_add,
    Prod.map, id_eq, view] at h
  exact h

/-- A fresh match against a registered signing digest uses the original adversary's budget. -/
theorem prEvent_registered_digest (A : Adversary) (q : Nat) (bounded : HasHashQueryBound A q) :
    Pr{let z ← countedGame A}[z.2.1.hit = true] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
  have budget := (hashQueryBound_iff A q).1 bounded
  rw [← countedGame_projection, support_map] at budget
  refine (prEvent_mono_of_support _ _ (fun z => z.2.1.hit = true ∧ z.2.2 ≤ q) ?_).trans ?_
  · intro z hz hit
    exact ⟨hit, budget _ ⟨z, hz, rfl⟩⟩
  · exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun _ _ =>
      prEvent_countedSource _ _ _ _ _ q

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch
