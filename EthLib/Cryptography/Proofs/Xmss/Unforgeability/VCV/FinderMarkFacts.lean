module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderCallerInvariant
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SigningSearchFact

/-!
# Replay every completed signing search from the terminal private and public tables

The recorded finder returns its own optional answer.

Later operations preserve the private low word and extend the public graph.
-/

@[expose] public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open HashSig Constants OracleComp OracleSpec TwoLayerGraph

/-- Each saved result replays from its private base in every later clean graph. -/
def Facts {pp : PublicParam} (r : ResidualCache pp) (s : State pp) : Prop :=
  ∀ m ∈ s.2, SearchFact pp m.call.layer m.call.epoch m.call.msg m.result.1 r
    (FinderNotices.physical s.1.1).1

private theorem facts_physical {pp : PublicParam} {α : Type} (p : Program pp α)
    (grows : ∀ r z, z ∈ support (p.run r) → r.2 ≤ z.2.2) :
    Maintains Facts (physical p) := by
  intro q r s a out t prior ran m held
  obtain ⟨issued,marks⟩ := ran.physical
  rw [marks] at held
  exact (prior m held).mono
    (grows r (a,out) (mem_support_of_mem_support_simulateQ_run _ _ _ issued))
    (Ran.graph_mono issued)

private theorem facts_carry {pp : PublicParam} {α : Type} (p : MixedLocal pp α)
    (grows : ExtendsPrivate p) : Maintains Facts (physical (carry p)) :=
  facts_physical _ fun r z ran => grows r z (support_simulateQ_subset raw _ ran)

private theorem facts_search (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    Maintains Facts (search pp l e msg) := by
  intro q r s a out t prior ran m held
  obtain ⟨issued,marks⟩ := ran.search
  have source := Ran.project issued
  rw [forget_find] at source
  rw [marks] at held
  rcases List.mem_cons.mp held with same | earlier
  · subst m
    exact (find_cut pp (deferredMixed pp) l e msg source).fact
  · have growth : ExtendsPrivate (mixedFind pp l e msg) := by
      apply ExtendsPrivate.bind (fun st _ h => mixedRandomizer_extends pp l e msg st h)
      exact fun _ => ExtendsPrivate.lift _
    exact (prior m earlier).mono (source.private_mono growth) source.public_mono

private theorem facts_steps (pp : PublicParam) : Steps pp Facts := by
  refine ⟨facts_search pp, ?_, ?_, ?_⟩
  · intro α p same
    exact facts_physical p fun r z ran => le_of_eq (congrArg Prod.snd (same r z ran)).symm
  · exact facts_carry _ fun s z h => le_of_eq (mixedTick_private pp s h).symm
  · apply facts_carry
    unfold mixedParameter
    rw [← bind_pure_comp]
    exact ExtendsPrivate.bind (fun s z h => mixedLocalWord_extends pp _ _ _ s h)
      (fun _ => ExtendsPrivate.pure _)

attribute [local irreducible] caller complete chronicle signing find

/-- Each completed finder retains its exact selection or exhaustion in the final state. -/
theorem completed_facts (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    {obs : Outcome} {out : ResidualCache pp} {rem : Nat} {s : State pp}
    (reach : ((some (obs,out),rem),s) ∈ support (observedGame pp A left r)) : Facts out s := by
  have actual : Done left (caller pp A) r (initial,[]) obs out s :=
    complete_of_guard left ((caller pp A).run r) left (initial,[]) reach
  exact (facts_steps pp).caller A left r _ obs out s (fun _ h => (List.not_mem_nil h).elim) actual

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
