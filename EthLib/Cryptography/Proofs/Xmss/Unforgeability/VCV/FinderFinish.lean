module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderChronicleGame
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderAttemptPrice
public import VCVio.OracleComp.QueryTracking.WeightedCap.Handler

/-!
# Observe complete signing searches under a shared physical budget

The finder returns either the accepted trial or exhaustion.

A physical refusal interrupts the finder before either return.
-/

@[expose] public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open Constants HashSig OracleComp OracleSpec TwoLayerGraph EarlierDigest
    EarlierDigest.Ledger TrialGraphWatch
open scoped Classical

abbrev Answer := Option (Randomizer × Vector (Fin CHAIN_LENGTH) V)

/-- The private state is the state at this invocation, before the attempt notice. -/
structure Call (pp : PublicParam) where
  layer : Layer
  epoch : UInt32
  msg : ByteArray
  privateIn : ResidualCache pp

abbrev Ops (pp : PublicParam) := Queries + (Call pp →ₒ (Answer × ResidualCache pp))

/-- Running a search operation issues the native signing search, including its attempt notice. -/
noncomputable def expandCall (pp : PublicParam) : QueryImpl (Ops pp) (OracleComp Queries)
  | .inl t => liftM (Queries.query t)
  | .inr c => (find pp c.layer c.epoch c.msg).run c.privateIn

/-- A finder return carries its exact entry and exit chronology.

An exhaustion has result 'none' and still yields an observation. -/
structure Finish (pp : PublicParam) where
  call : Call pp
  before : ChronicleState
  result : Answer × ResidualCache pp
  after_ : ChronicleState

/-- Was the selected physical row already partnered at the end of the first search at this key? -/
def FirstHit {pp : PublicParam} (x : Finish pp) : Prop :=
  let c := x.call
  x.before.1.1.2.2 (c.layer,c.epoch) = none ∧
    c.privateIn.2 ⟨.inl (pp, addrRnd c.layer c.epoch, c.msg),
      (randomizer_residual pp c.layer c.epoch c.msg).1⟩ = none ∧
    ∃ rho digits, x.result.1 = some (rho,digits) ∧
      Partner pp x.after_.1.1.2.1.1 (CachedCodeword.trialInput pp c.layer c.epoch c.msg rho)

abbrev State (pp : PublicParam) := ChronicleState × List (Finish pp)
abbrev Execution (pp : PublicParam) := OptionT (StateT Nat (StateT (State pp) ProbComp))

/-- The budget guard acts inside each search.

The end observation is appended only after an actual return from the whole finder. -/
noncomputable def observeCall (pp : PublicParam) (q : Nat) : QueryImpl (Ops pp) (Execution pp) :=
  fun t => OptionT.mk <| StateT.mk fun left => StateT.mk fun s => do
    let z ← (((simulateQ (WeightedCap.guard fee (chronicle pp q)) (expandCall pp t)).run).run
      left).run s.1
    let marks := match t, z.1.1 with
      | .inr c, some ans => ⟨c,s.1,ans,z.2⟩ :: s.2
      | _, _ => s.2
    return (z.1,z.2,marks)

/-- Erasing the finder ends preserves the remaining budget even on refusal. -/
theorem erase_guards {pp : PublicParam} (q : Nat) {α : Type} (p : OracleComp (Ops pp) α)
    (left : Nat) (s : State pp) :
    (fun z => (z.1,z.2.1)) <$> (((simulateQ (observeCall pp q) p).run).run left).run s =
      (((simulateQ (WeightedCap.guard fee (chronicle pp q)) (simulateQ (expandCall pp) p)).run).run
        left).run s.1 := by
  induction p using OracleComp.inductionOn generalizing left s with
  | pure a => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind,
      observeCall, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, map_bind]
    apply bind_congr
    rintro ⟨⟨_ | a, rem⟩, st⟩
    · simp
    · exact ih a rem _

/-- The capped caller observes the same attempts, registrations and first full words. -/
theorem erase {pp : PublicParam} (q : Nat) {α : Type} (p : OracleComp (Ops pp) α)
    (left : Nat) (s : State pp) :
    (fun z => (z.1.1,z.2.1)) <$> (((simulateQ (observeCall pp q) p).run).run left).run s =
      (simulateQ (chronicle pp q) (WeightedCap.capCompOpt fee left
        (simulateQ (expandCall pp) p))).run s.1 := by
  rw [← WeightedCap.run_guard]
  have eq := congrArg (Functor.map (fun z => (z.1.1,z.2))) (erase_guards q p left s)
  simpa [StateT.run_map, Functor.map_map] using eq

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
