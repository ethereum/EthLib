module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.ConcreteStatement
import all EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.ConcreteStatement

/-!
# The original client with raw signing replies

The leanXMSS draft, section "Security", excludes repeated leaf indices from winning executions.
An error still counts as an attempt at its leaf.
The public client receives its usual optional signature while the experiment retains the exact error.
-/

public section
open OracleComp OracleSpec
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient

abbrev World := XmssSecurity.OracleWorld
abbrev RawLog := List (SignRequest × Except XmssError Signature)

/-- Erase only the error payload, keeping every original request and its position. -/
@[expose] def eraseLog (log : RawLog) : QueryLog SigningSpec :=
  log.map fun entry => ⟨entry.1, entry.2.toOption⟩

/-- The public verification key, candidate, signing replies and verification outcome from one run. -/
structure Outcome where
  key : PublicKey
  candidate : Forgery
  log : RawLog
  verified : Bool

/-- Give each signing answer to the same option-valued client and record its original raw reply. -/
@[expose] def signRaw (seed : Seed) :
    QueryImpl SigningSpec (WriterT RawLog (OracleComp World)) := fun r => WriterT.mk
  ((fun reply => (reply.toOption, [(r, reply)])) <$> liftM (statelessSignWith H seed r.leafIndex r.message))

open scoped Classical in
/-- Keep the entire actual client, including private draws and requests after a signing failure. -/
@[expose] noncomputable def rawRun {α : Type} (seed : Seed) (client : OracleComp (World + SigningSpec) α) :=
  (simulateQ (QueryImpl.ofLift World (WriterT RawLog (OracleComp World)) + signRaw seed) client).run

/-- The option-valued signature experiment sees exactly the projected raw log and candidate. -/
theorem rawRun_erase {α : Type} (seed : Seed) (client : OracleComp (World + SigningSpec) α) :
    (fun w => (w.1, eraseLog w.2)) <$> rawRun seed client =
      (simulateQ (QueryImpl.ofLift World (WriterT (QueryLog SigningSpec) (OracleComp World)) +
        statelessSigningOracle seed) client).run := by
  induction client using OracleComp.inductionOn with
  | pure a => simp [rawRun, eraseLog]
  | query_bind t k ih =>
    cases t with
    | inl q =>
      have forwarded (L : Type) [EmptyCollection L] [Append L] :
          ((liftM (World.query q) : WriterT L (OracleComp World) _)).run =
            (fun x => (x, (∅ : L))) <$> (liftM (World.query q) : OracleComp World _) := rfl
      simp [rawRun, QueryImpl.ofLift, WriterT.run_bind, map_bind, forwarded,
        bind_map_left] at ih ⊢
      exact bind_congr ih
    | inr r =>
      simp [rawRun, signRaw, statelessSigningOracle, WriterT.run_bind, map_bind, bind_map_left,
        Functor.map_map] at ih ⊢
      apply bind_congr
      intro reply
      rw [← ih reply.toOption]
      simp [eraseLog, Functor.map_map]

/-- Run the actual hash and signing calls and preserve their complete result. -/
@[expose] noncomputable def observe (A : Adversary) : OracleComp World Outcome := do
  let seed ← liftM sampleSeed
  let (sk, pk) ← liftM (statelessKeyGenWith H seed)
  let (candidate, log) ← rawRun sk (A.main pk)
  let ok ← liftM (verifyWith H pk candidate.message candidate.signature)
  return ⟨pk, candidate, log, ok⟩

/-- Test the original winning condition after erasing the diagnostic error payload. -/
noncomputable def wins (z : Outcome) : Bool :=
  decide (Valid (eraseLog z.log) ∧ ¬Contains (eraseLog z.log) z.candidate) && z.verified

theorem stateless_core (A : Adversary) :
    wins <$> observe A = statelessGameCore A := by
  unfold observe statelessGameCore
  simp only [map_bind, map_pure]
  apply bind_congr
  intro seed
  apply bind_congr
  rintro ⟨sk, pk⟩
  rw [← rawRun_erase, bind_map_left]
  rfl

/-- Preserve the original count, including hash calls on failed and repeated signing attempts. -/
noncomputable def countedObservation (A : Adversary) : ProbComp (Outcome × Nat) :=
  (simulateQ countedOracle (observe A)).run.run' ∅

theorem statelessExperiment_observe (A : Adversary) :
    statelessExperiment A = (fun z => (wins z.1, z.2)) <$> countedObservation A := by
  unfold statelessExperiment countedObservation
  rw [← stateless_core]
  simp only [simulateQ_map, StateT.run', WriterT.run_map]
  change Prod.fst <$> ((WriterT.run (simulateQ countedOracle (observe A))) ∅ >>= fun z =>
    pure ((wins z.1.1, z.1.2), z.2)) = _
  simp only [bind_pure_comp, Functor.map_map]
  exact (Functor.map_map (f := ProbComp) Prod.fst
    (fun z : Outcome × Multiplicative Nat => (wins z.1, z.2)) ((WriterT.run (simulateQ countedOracle (observe A))) ∅)).symm

theorem hashQueryBound_iff (A : Adversary) (q : Nat) :
    HasHashQueryBound A q ↔ ∀ z ∈ support (countedObservation A), z.2 ≤ q := by
  rw [HasHashQueryBound, statelessExperiment_observe]
  constructor
  · intro h z hz
    apply h (wins z.1, z.2)
    rw [support_map]
    exact ⟨z, hz, rfl⟩
  · intro h z hz
    rw [support_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact h w hw

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
