module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealClient
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.SeedHops

/-!
# The stateless strong-forgery client over sources of derivations

Each request uses the stateless signer's single bottom-tree build.
Its raw signing reply is logged before the original client receives its optional signature.
The source used in key generation is called again at every request.

Source: leanXMSS draft, sections "The scheme" and "Security".
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient

open OracleComp OracleSpec
open XmssSecurity (HashSpec HashOutput MasterSeed)
variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- Use the existing single-build signer and retain its literal error in the private log. -/
@[expose] def signerOf (pass : QueryImpl World (OracleComp spec)) (seed : OracleComp spec σ)
    (derive : σ → SeedPrf (OracleComp spec)) :
    QueryImpl (World + SigningSpec) (WriterT RawLog (OracleComp spec))
  | .inl q => liftM (pass q)
  | .inr r => WriterT.mk ((fun w => (w.1.toOption, [(r, w.1)])) <$>
      (failSignerOf pass seed derive (.inr r)).run)

/-- Return the current key, candidate, all raw replies and the result of production verification. -/
@[expose] def sourceOf (pass : QueryImpl World (OracleComp spec)) (seed : OracleComp spec σ)
    (derive : σ → SeedPrf (OracleComp spec)) (A : Adversary) : OracleComp spec Outcome := do
  let s ← seed
  let pk ← publicKeyOf (hashOf pass) (derive s)
  let (candidate, log) ← (simulateQ (signerOf pass seed derive) (A.main pk)).run
  let accepted ← verifyWith (hashOf pass) pk candidate.message candidate.signature
  return ⟨pk, candidate, log, accepted⟩

section Map
variable {ι' : Type} {spec' : OracleSpec ι'} (f : QueryImpl spec (OracleComp spec'))
variable (pass : QueryImpl World (OracleComp spec)) (seed : OracleComp spec σ)
variable (derive : σ → SeedPrf (OracleComp spec))

private theorem signer_map_apply (t : (World + SigningSpec).Domain) :
    simulateQ f (signerOf pass seed derive t).run =
      (signerOf (f ∘ₛ pass) (simulateQ f seed)
        (fun s p a b => simulateQ f (derive s p a b)) t).run := by
  cases t with
  | inl q => simp [signerOf, QueryImpl.apply_compose]
  | inr r => simp only [signerOf, WriterT.run_mk, simulateQ_map, simulateQ_run_failSignerOf_apply]

private theorem signer_map {α} (body : OracleComp (World + SigningSpec) α) :
    simulateQ f (simulateQ (signerOf pass seed derive) body).run =
      (simulateQ (signerOf (f ∘ₛ pass) (simulateQ f seed)
        (fun s p a b => simulateQ f (derive s p a b))) body).run := by
  induction body using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', simulateQ_map,
      signer_map_apply, ih]

/-- Realizing a source realizes every key-generation, client, signing and verification query. -/
theorem source_map (A : Adversary) :
    simulateQ f (sourceOf pass seed derive A) =
      sourceOf (f ∘ₛ pass) (simulateQ f seed) (fun s p a b => simulateQ f (derive s p a b)) A := by
  simp only [sourceOf, simulateQ_bind, simulateQ_pure, signer_map]
  apply bind_congr
  intro s
  rw [publicKeyOf_map_monad (simulateQ f) (fun _ => simulateQ_pure f _) (fun _ _ => simulateQ_bind f _ _)]
  simp only [simulateQ_hashOf]
  refine bind_congr fun pk => bind_congr fun z => ?_
  rw [verifyWith_map_monad (simulateQ f) (fun _ => simulateQ_pure f _) (fun _ _ => simulateQ_bind f _ _)]
  simp only [simulateQ_hashOf]
end Map

private theorem signer_real (s : Seed) :
    signerOf (QueryImpl.id' World)
      (schemeSeed (hashOf (QueryImpl.id' World)) s) (seedPrf (hashOf (QueryImpl.id' World))) =
    QueryImpl.ofLift World (WriterT RawLog (OracleComp World)) + signRaw s := by
  funext t
  cases t with
  | inl q => rfl
  | inr r =>
    rw [signerOf, ← reasonOracles_eq_failSignerOf, QueryImpl.add_apply_inr, QueryImpl.add_apply_inr]
    simp [statelessReasonSigningOracle, signRaw, Functor.map_map]

/-- The real source keeps the production stateless observation and every physical call. -/
theorem observe_eq_source (A : Adversary) :
    observe A = (liftM XmssSecurity.sampleMasterSeed : OracleComp World _) >>= fun s0 =>
      sourceOf (QueryImpl.id' World) (schemeSeed (hashOf (QueryImpl.id' World)) (ofSeed s0))
        (seedPrf (hashOf (QueryImpl.id' World))) A := by
  unfold observe sampleSeed
  simp only [liftM_map, bind_map_left]
  apply bind_congr
  intro s0
  have hs : (liftM (schemeSeed H (ofSeed s0)) : OracleComp World Seed) =
      schemeSeed (hashOf (QueryImpl.id' World)) (ofSeed s0) := liftM_H _
  simp only [sourceOf, statelessKeyGenWith, liftM_bind, liftM_pure, bind_assoc, pure_bind, hs]
  apply bind_congr
  intro s
  rw [publicKeyOf_map_monad (fun {β} (c : OracleComp HashSpec β) => (liftM c : OracleComp World β))
    (fun b => liftM_pure b) (fun x f => liftM_bind x f), funext liftM_H, liftM_seedPrf]
  simp only [signer_real, rawRun]
  refine bind_congr fun pk => bind_congr fun z => ?_
  rw [verifyWith_map_monad (fun {β} (c : OracleComp HashSpec β) => (liftM c : OracleComp World β))
    (fun b => liftM_pure b) (fun x f => liftM_bind x f), funext liftM_H]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
