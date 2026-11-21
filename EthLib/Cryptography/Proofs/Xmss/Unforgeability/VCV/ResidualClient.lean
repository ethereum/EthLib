module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ResidualSchedule
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LocalSignature
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.SigningSource
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# The adaptive client with residual-aware signing

Each production signing request fetches its seed and rederives its parameter.

A successful request reports its two-layer signature and a failed one reports its error.

The hidden schedule preserves both local tables, both graph tables and the complete raw signing log.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants OracleSpec OracleComp TwoLayerGraph

private theorem map_inGraph {α β : Type} (pp : PublicParam) (f : α → β) (p : OracleComp Source α) :
    inGraph pp (f <$> p) = f <$> inGraph pp p := by
  simp only [← bind_pure_comp, inGraph_bind, inGraph_pure]

private theorem local_map {pp : PublicParam} {R α β : Type} {a b : Honest.WithLocal R α}
    (same : Honest.SameLocal pp a b) (f : α → β) : Honest.SameLocal pp (f <$> a) (f <$> b) := by
  simp only [← bind_pure_comp]
  exact same.bind (fun _ _ => rfl)

/-- A determined request at the sampled parameter uses the hidden stateful signer. -/
@[expose] noncomputable def requestSchedule (pp : PublicParam) (r : SignRequest) :
    Honest.WithLocal (ResidualCache pp) (Except XmssError Signature) := do
  let _ ← inGraph pp sourceTick
  let drawn ← inGraph pp (publicParamOf sourcePrf)
  if drawn = pp then
    Honest.localReleased pp (graphPrf pp) r.leafIndex r.message
  else
    inGraph pp (signDerived (hashOf sourcePass) sourcePrf drawn r.leafIndex r.message)

/-- State the query interpreter at the interface of the original optional-signature client. -/
@[expose] noncomputable def clientOracle (pp : PublicParam) :
    QueryImpl (World + SigningSpec) (WriterT RawLog (Honest.WithLocal (ResidualCache pp)))
  | .inl q => liftM (inGraph pp (sourcePass q))
  | .inr r => WriterT.mk ((fun ans => (ans.toOption, [(r, ans)])) <$> requestSchedule pp r)

attribute [local irreducible] Xmss.signDerived Honest.localReleased

private theorem source_sign (pp : PublicParam) (r : SignRequest) (drawn : PublicParam) :
    inGraph pp (signDerived (hashOf sourcePass) sourcePrf drawn r.leafIndex r.message) =
      signDerived (fun b => liftM (Honest.hash b)) (graphPrf pp) drawn r.leafIndex r.message := by
  rw [signDerived_map_monad (fun {_} p => inGraph pp p) (inGraph_pure pp) (inGraph_bind pp)]
  simp only [inGraph_hash]
  rfl

private theorem request_same (pp : PublicParam) (r : SignRequest) :
    Honest.SameLocal pp (inGraph pp (do
      let _ ← sourceTick
      let drawn ← publicParamOf sourcePrf
      signDerived (hashOf sourcePass) sourcePrf drawn r.leafIndex r.message))
        (requestSchedule pp r) := by
  simp only [requestSchedule, inGraph_bind]
  apply Honest.SameLocal.bind (fun _ => rfl)
  intro _
  apply Honest.SameLocal.bind (fun _ => rfl)
  intro drawn
  split_ifs with yes
  · subst drawn
    rw [source_sign]
    exact Honest.signDerived_local pp (graphPrf pp) (fun l => Honest.prf pp l emptyPrf)
      (graphPrf_pairs pp) (fun l => Honest.prf_pair pp l emptyPrf) _ _
  · exact fun _ => rfl

private theorem query_same (pp : PublicParam) (q : (World + SigningSpec).Domain) :
    Honest.SameLocal pp (inGraph pp (signerOf sourcePass sourceTick (fun _ => sourcePrf) q).run)
      ((clientOracle pp q).run) := by
  cases q with
  | inl q =>
    simp [clientOracle, signerOf, map_inGraph]
    exact fun _ => rfl
  | inr r =>
    simp only [signerOf, failSignerOf, WriterT.run_mk, map_bind, map_pure, clientOracle,
      inGraph_bind, inGraph_pure]
    have combined := local_map (request_same pp r) (fun ans => (ans.toOption, [(r, ans)]))
    simpa only [← bind_pure_comp, inGraph_bind, inGraph_pure, bind_assoc] using combined

/--
Private draws, signing errors, raw queries and future adaptively selected requests stay in order.
-/
theorem adaptive_requests {α : Type} (pp : PublicParam) (oa : OracleComp (World + SigningSpec) α) :
    Honest.SameLocal pp
      (inGraph pp (simulateQ (signerOf sourcePass sourceTick (fun _ => sourcePrf)) oa).run)
      (simulateQ (clientOracle pp) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [inGraph_pure, Honest.SameLocal]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', inGraph_bind, map_inGraph]
    apply Honest.SameLocal.bind (query_same pp t)
    intro pair
    exact local_map (ih pair.1) _

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
