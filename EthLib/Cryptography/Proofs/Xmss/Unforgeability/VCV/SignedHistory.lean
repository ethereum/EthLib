module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SigningSuccess
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SameTopKey
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedGameLaw

/-!
# Authentic signing facts for every successful raw entry

The original adversary selects each signing request after observing the preceding replies.

Earlier search and graph facts persist through later requests, public calls and the final verifier.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleSpec OracleComp

@[expose] def LogFacts (pp : PublicParam) (raw : RawLog) (r : ResidualCache pp)
    (s : SharedState) : Prop :=
  ∀ req sig, (req,.ok sig) ∈ raw → SignedFact pp req sig r s

private theorem MixedRun.map_result {pp : PublicParam} {α β : Type} {p : MixedLocal pp α}
    {f : α → β}
    {r s b out t} (ran : MixedRun (deferredMixed pp) (f <$> p) r s b out t) :
    ∃ a, MixedRun (deferredMixed pp) p r s a out t ∧ f a = b := by
  rw [← bind_pure_comp] at ran
  obtain ⟨a,mid,g,body,done⟩ := ran.bind
  obtain ⟨eq, rfl, rfl⟩ := done.pure_result
  exact ⟨a,body,eq.symm⟩

attribute [local irreducible] simulateQ graph deferredMixed Xmss.verifyWith mixedSignature

private theorem step_facts (pp : PublicParam) (q : (World + SigningSpec).Domain) {r s z out t}
    (ran : MixedRun (deferredMixed pp) (mixedOracle pp q).run r s z out t) :
    r.2 ≤ out.2 ∧ LogFacts pp z.2 out t.1 := by
  cases q with
  | inl word =>
    change MixedRun _ ((fun a => (a,([] : RawLog))) <$> mixedWorldPass pp word) _ _ _ _ _ at ran
    obtain ⟨reply,step,rfl⟩ := ran.map_result
    have same := step.lifted.1
    exact ⟨le_of_eq (congrArg Prod.snd same.symm), fun _ _ h => (List.not_mem_nil h).elim⟩
  | inr req =>
    have growth := ran.private_mono (request_grows pp req)
    change MixedRun _ (mixedRequest pp req _) _ _ _ _ _ at ran
    unfold mixedRequest at ran
    obtain ⟨_,_,_,_,rest⟩ := ran.bind
    obtain ⟨_,_,_,_,rest⟩ := rest.bind
    obtain ⟨reply,mid,endSign,sign,done⟩ := rest.bind
    obtain ⟨eq, rfl, rfl⟩ := done.pure_result
    subst z
    refine ⟨growth, ?_⟩
    intro request sig member
    obtain ⟨rfl,eq⟩ := Prod.mk.inj (List.mem_singleton.mp member)
    rw [← eq] at sign
    exact signing_facts pp request sign

/-- Each logged success retains the components of the actual signature. -/
theorem client_facts {α : Type} (pp : PublicParam) (body : OracleComp (World + SigningSpec) α)
    {r s z out t} (ran : MixedRun (deferredMixed pp) (simulateQ
      (mixedOracle pp) body).run r s z out t) :
    r.2 ≤ out.2 ∧ LogFacts pp z.2 out t.1 := by
  induction body using OracleComp.inductionOn generalizing r s t out z with
  | pure a =>
    simp only [simulateQ_pure, WriterT.run_pure] at ran
    obtain ⟨rfl,rfl,rfl⟩ := ran.pure_result
    exact ⟨le_rfl,fun _ _ h => (List.not_mem_nil h).elim⟩
  | query_bind query k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind'] at ran
    obtain ⟨⟨reply,pre⟩,mid,g,head,tail⟩ := ran.bind
    obtain ⟨⟨a,post⟩, rest, eq⟩ := tail.map_result
    subst z
    obtain ⟨firstGrows, first⟩ := step_facts pp query head
    obtain ⟨lastGrows, last⟩ := ih reply rest
    refine ⟨firstGrows.trans lastGrows,?_⟩
    intro req sig h
    rcases List.mem_append.mp h with left | right
    · exact (first req sig left).mono lastGrows rest.public_mono
    · exact last req sig right

/-- Every logged signature retains its authentic rows through the final verifier. -/
theorem signed_history (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    (s : DeferredState) (obs : Outcome) (out : ResidualCache pp) (t : DeferredState)
    (actual : (some (obs,out),t) ∈ support ((simulateQ (graph pp).deferredImpl
      (guardedGraph left ((mixedGame pp A).run r))).run s))
    (last : SharedState) (extended : t.1 ≤ last) : LogFacts pp obs.log out last := by
  obtain ⟨_,atClient,cut,_,_,log,_,verified⟩ := mixed_verifier_cut pp A left r s obs out t actual
  have client := log.raw
  change ((_,_),_) ∈ support ((simulateQ (graph pp).deferredImpl
    (simulateQ (CanonicalGraph.PairedQueries.expand PairedHashWord.halves) _)).run _) at client
  rw [← QueryImpl.simulateQ_compose] at client
  have ran : MixedRun (deferredMixed pp) (simulateQ (mixedOracle pp)
    (A.main obs.key)).run r atClient
      (obs.candidate,obs.log) out cut := by
    unfold MixedRun deferredMixed
    exact client
  have facts := (client_facts pp _ ran).2
  have grows := (graph pp).le_of_mem_support_simulateQ_deferredImpl _ verified
  exact fun req sig member => (facts req sig member).mono le_rfl (grows.trans extended)

/-- Two logged successes at the same upper key return the same upper signature and finder digits. -/
theorem logged_top_agreement (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    (s : DeferredState) (obs : Outcome) (out : ResidualCache pp) (t : DeferredState)
    (actual : (some (obs,out),t) ∈ support ((simulateQ (graph pp).deferredImpl
      (guardedGraph left ((mixedGame pp A).run r))).run s))
    (last : SharedState) (extended : t.1 ≤ last) (clean : ¬ (graph pp).Conflict last)
    {a b : SignRequest} {sa sb : Signature} (first : (a,.ok sa) ∈ obs.log)
    (second : (b,.ok sb) ∈ obs.log) (same : bottomTree a.leafIndex = bottomTree b.leafIndex) :
    sa.top = sb.top ∧ ∃ root y,
      last.2 (.inr (.inl (.bottom,LayerGraph.treeRole LAYER_HEIGHT (bottomTree a.leafIndex)))) =
        some (ChainGraph.digestEquiv root) ∧
      LayerFact pp .top (bottomTree a.leafIndex) (packBytes root) sa.top y out last ∧
      LayerFact pp .top (bottomTree b.leafIndex) (packBytes root) sb.top y out last := by
  have facts := signed_history pp A left r s obs out t actual last extended
  exact (facts a sa first).same_top (facts b sb second) same clean

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
