module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeSigner
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.NormalizedForgery

/-!
# Observing the finder in the actual capped forgery experiment

The client receives the original optional signing reply.

Its verifier runs with the public key and final residual table reached by that client.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open EthLib.Cryptography HashSig OracleComp OracleSpec Constants TwoLayerGraph
    Honest LayerGraph.Hidden

/-- The private tick and warm parameter read precede the instrumented native signer. -/
@[expose] noncomputable def request (pp : PublicParam) (r : SignRequest) :
    Program pp (Option Signature × RawLog) := do
  let _ ← carry (mixedTick pp)
  let _ ← carry (mixedParameter pp)
  let answer ← signature pp r.leafIndex r.message
  return (answer.toOption, [(r, answer)])

/-- The original adversary's coins and all its direct full-word requests pass through. -/
@[expose] noncomputable def oracle (pp : PublicParam) :
    QueryImpl (World + SigningSpec) (WriterT RawLog (Program pp))
  | .inl t => liftM (carry (mixedWorldPass pp t))
  | .inr r => WriterT.mk (request pp r)

private theorem forget_query (pp : PublicParam) (t : (World + SigningSpec).Domain) :
    forget ((oracle pp t).run) = (mixedOracle pp t).run := by
  rcases t with t | r
  · simp [oracle, mixedOracle]
  · simp [oracle, mixedOracle, request, mixedRequest, forget_signature]

/-- Erasure preserves the exact raw error log for every adaptive optional-signature client. -/
theorem forget_client {α : Type} (pp : PublicParam) (p : OracleComp (World + SigningSpec) α) :
    forget ((simulateQ (oracle pp) p).run) = (simulateQ (mixedOracle pp) p).run := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', forget_bind, forget_query,
      forget_map, ih]

/-- The underlying physical mixed game with finder notices. -/
@[expose] noncomputable def game (pp : PublicParam) (A : Adversary) : Program pp Outcome := do
  let root ← carry (liftM (emitStructure (simulateQ (selection pp .top).liftQuery
    (beforeNode pp .top LAYER_HEIGHT 0 >>= fun _ => LayerGraph.readOutput
      (LayerGraph.treeRole LAYER_HEIGHT 0)))))
  let pk : PublicKey := ⟨root, pp⟩
  let (candidate, records) ← (simulateQ (oracle pp) (A.main pk)).run
  let valid ← carry (liftM (verifyWith mixedHash pk candidate.message candidate.signature))
  return ⟨pk, candidate, records, valid⟩

/-- Removing the notices preserves the whole native mixed computation and every residual table. -/
theorem forget_game (pp : PublicParam) (A : Adversary) : forget (game pp A) = mixedGame pp A := by
  simp [game, mixedGame, forget_client]

private theorem cap_forget {pp : PublicParam} {α : Type} (p : Program pp α) (u : MixedLocal pp α)
    (same : forget p = u) (left : Nat) (r : ResidualCache pp) :
    simulateQ TrialGraphWatch.erase (WeightedCap.capCompOpt TrialGraphWatch.fee left (p.run r)) =
      WeightedCap.capCompOpt (CanonicalGraph.PairedQueries.mixedCost (H := ChainGraph.Word)
        (F := HashOutput) (fun _ => 0)) left (u.run r) := by
  subst u
  exact TrialGraphWatch.erase_cap (p.run r) left

/-- The physical guard acts before both hash halves, including on a refused signing prefix. -/
theorem erase_capped_game (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp) :
    simulateQ TrialGraphWatch.erase (WeightedCap.capCompOpt TrialGraphWatch.fee left
      ((game pp A).run r)) =
      WeightedCap.capCompOpt (CanonicalGraph.PairedQueries.mixedCost (H := ChainGraph.Word)
        (F := HashOutput) (fun _ => 0)) left ((mixedGame pp A).run r) :=
  cap_forget (game pp A) (mixedGame pp A) (forget_game pp A) left r

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
