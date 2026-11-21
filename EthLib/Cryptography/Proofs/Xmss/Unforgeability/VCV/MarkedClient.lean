module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedRequest

/-!
# Requests and finder returns on the same adaptive client path

The adversary sees the optional signing result and can choose every later request from it.

Every completed search still belongs to one of the raw replies on that same path.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open EthLib.Cryptography HashSig Constants OracleSpec OracleComp TwoLayerGraph Honest

private def Explains {pp} (xs : RawLog) (s t : State pp) : Prop :=
  ∀ x ∈ t.2, x ∈ s.2 ∨ ∃ req ans, (req,ans) ∈ xs ∧
    IssuedAt x req.leafIndex req.message ans (FinderNotices.physical t.1.1).1 t.1.2

private theorem Done.mapped_result {pp q} {α β : Type} {p : Body pp α} {f : α → β} {r s b out t}
    (ran : Done q (f <$> p) r s b out t) : ∃ a, Done q p r s a out t ∧ f a = b := by
  rw [← bind_pure_comp] at ran
  obtain ⟨a,_,_,first,ret⟩ := ran.bind
  obtain ⟨same,rfl,rfl⟩ := ret.pure_result
  exact ⟨_,first,same.symm⟩

attribute [local irreducible] signing Xmss.verifyWith selection emitStructure

private theorem explains_query {pp q} (query : (World + SigningSpec).Domain) {r s z out t}
    (ran : Done q (clientOracle pp query).run r s z out t) : Explains z.2 s t := by
  cases query with
  | inl u =>
    change Done q ((fun v => (v,
      ([] : RawLog))) <$> physical (carry (mixedWorldPass pp u))) _ _ _ _ _ at ran
    obtain ⟨_,actual,rfl⟩ := ran.mapped_result
    intro x mem
    exact Or.inl (actual.physical.2 ▸ mem)
  | inr req =>
    obtain ⟨_,_,_,tick,rest⟩ := ran.bind
    obtain ⟨_,_,_,param,rest⟩ := rest.bind
    obtain ⟨ans,_,_,sign,done⟩ := rest.bind
    obtain ⟨rfl,_,rfl⟩ := done.pure_result
    intro x mem
    by_cases old : x ∈ s.2
    · exact Or.inl old
    · right
      refine ⟨req,ans,List.mem_cons_self,signing_issued sign x mem ?_⟩
      rw [param.physical.2,tick.physical.2]
      exact old

private theorem explains_client {pp q} {α : Type} (p : OracleComp (World + SigningSpec) α)
    {r s z out t} (ran : Done q (simulateQ (clientOracle pp) p).run r s z out t) :
    Explains z.2 s t := by
  induction p using OracleComp.inductionOn generalizing r s z out t with
  | pure a =>
    simp only [simulateQ_pure,WriterT.run_pure] at ran
    obtain ⟨rfl,_,rfl⟩ := ran.pure_result
    exact fun _ m => Or.inl m
  | query_bind query k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,WriterT.run_bind'] at ran
    obtain ⟨⟨answer,pre⟩,_,g,step,tail⟩ := ran.bind
    obtain ⟨⟨_,post⟩,rest,rfl⟩ := tail.mapped_result
    intro x mem
    rcases ih answer rest x mem with earlier | ⟨req,a,logged,fact⟩
    · rcases explains_query query step x earlier with old | ⟨req,a,logged,fact⟩
      · exact Or.inl old
      · exact Or.inr ⟨req,a,List.mem_append_left _ logged,
            fact.mono rest.real.graph_mono rest.arrivals⟩
    · exact Or.inr ⟨req,a,List.mem_append_right _ logged,fact⟩

attribute [local irreducible] caller complete chronicle

/-- Each marked finder on this completed original caller names an actual raw signing reply. -/
theorem observed_issued (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    {obs : Outcome} {out : ResidualCache pp} {rem : Nat} {t : State pp}
    (ran : ((some (obs,out),rem),t) ∈ support (observedGame pp A left r)) :
    ∀ x ∈ t.2, ∃ req ans, (req,ans) ∈ obs.log ∧
      IssuedAt x req.leafIndex req.message ans (FinderNotices.physical t.1.1).1 t.1.2 := by
  have actual : Done left (caller pp A) r (initial,[]) obs out t :=
    complete_of_guard left ((caller pp A).run r) left (initial,[]) ran
  unfold caller at actual
  obtain ⟨_,_,_,key,tail⟩ := actual.bind
  obtain ⟨⟨_,_⟩,_,_,client,tail⟩ := tail.bind
  obtain ⟨_,_,_,verify,done⟩ := tail.bind
  obtain ⟨rfl,_,rfl⟩ := done.pure_result
  intro x mem
  rw [verify.physical.2] at mem
  rcases explains_client _ client x mem with old | ⟨req,a,logged,fact⟩
  · rw [key.physical.2] at old
    cases old
  · exact ⟨req,a,logged,fact.mono verify.real.graph_mono verify.arrivals⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
