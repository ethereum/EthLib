module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedRelease
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedQueryTrace
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedRelease
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ClientRelease

/-!
# Directly disclosed positions in the concrete mixed client's transcript

A public oracle call makes no direct read of a chain value.

Only a successful return from the two-layer signer authorizes such reads.

The original adversary may use each reply to select its next request.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleSpec OracleComp
open CanonicalGraph.PairedQueries

private theorem map_image {α β : Type} (pp : PublicParam) (p : MixedLocal pp α) (f : α → β) :
    expandLocal pp (f <$> p) = f <$> expandLocal pp p := by
  simp only [← bind_pure_comp, bind_image, pure_image]

private noncomputable def expandedOracle (pp : PublicParam) :
    QueryImpl (World + SigningSpec) (WriterT RawLog (WithLocal (ResidualCache pp))) :=
  fun q => WriterT.mk (expandLocal pp (mixedOracle pp q).run)

private theorem client_image {α : Type} (pp : PublicParam) (body : OracleComp
    (World + SigningSpec) α) :
    expandLocal pp (simulateQ (mixedOracle pp) body).run
      = (simulateQ (expandedOracle pp) body).run := by
  induction body using OracleComp.inductionOn with
  | pure _ => simp only [simulateQ_pure, WriterT.run_pure, pure_image]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', bind_image, map_image, ih,
      expandedOracle, WriterT.run_mk]

private theorem request_reads (pp : PublicParam) (req : SignRequest) (r : ResidualCache pp)
    {s ans out xs t} (ran : Logged pp ((expandedOracle pp (.inr req)).run.run r) s (ans,out) xs t) :
    LogWithin (releasedCells pp t.1 ans.2) xs := by
  simp only [expandedOracle, WriterT.run_mk, mixedOracle, mixedRequest, expandLocal, StateT.run_mk,
    StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure] at ran
  obtain ⟨⟨_, next⟩, tickLog, sg, tailLog, tick, tail, rfl⟩ := ran.bind
  obtain ⟨⟨_, afterParam⟩, paramLog, sh, restLog, param, rest, rfl⟩ := tail.bind
  obtain ⟨⟨sig, afterSign⟩, signLog, sk, finalLog, signed, delivered, rfl⟩ := rest.bind
  obtain ⟨answer, rfl, state⟩ := delivered.pure_result
  cases answer
  subst t
  rw [List.append_nil]
  exact (tick.within ∅ (tick_no_chain pp r)).mono (Set.empty_subset _) |>.append
    (((param.within ∅ (parameter_no_chain pp next)).mono (Set.empty_subset _)).append
      (mixed_logged_cells pp req afterParam signed))

private theorem public_reads (pp : PublicParam) (q : World.Domain) (r : ResidualCache pp)
    {s ans out xs t} (ran : Logged pp ((expandedOracle pp (.inl q)).run.run r) s (ans,out) xs t) :
    LogWithin (releasedCells pp t.1 ans.2) xs := by
  change Logged pp ((expandLocal pp ((fun a => (a, ([] : RawLog))) <$> mixedWorldPass pp q)).run r)
    s (ans,out) xs t at ran
  simp only [expandLocal, StateT.run_mk, StateT.run_map, simulateQ_map] at ran
  obtain ⟨_, call, _⟩ := map_inverse ran
  exact (call.within ∅ (adversary_no_chain pp q r)).mono (Set.empty_subset _)

/-- Every direct chain read belongs to a successful reply in the same adaptive prefix. -/
theorem mixed_client_reads {α : Type} (pp : PublicParam) (p : OracleComp (World + SigningSpec) α)
    (r : ResidualCache pp) {s ans out xs t}
    (ran : Logged pp ((expandLocal pp (simulateQ (mixedOracle pp) p).run).run r) s (ans,out) xs t) :
    LogWithin (releasedCells pp t.1 ans.2) xs := by
  rw [client_image] at ran
  apply (adaptive_log pp (expandedOracle pp) (fun _ => True) _ p r trivial ran).2
  intro q before st response after log finish _ real
  refine ⟨trivial, ?_⟩
  cases q with
  | inl t => exact public_reads pp t before real
  | inr req => exact request_reads pp req before real

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
