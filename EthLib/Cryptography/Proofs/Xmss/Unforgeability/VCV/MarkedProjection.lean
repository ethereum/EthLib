module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedCuts
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegistrationProjection

/-!
# The physical state under the marked finder stream

Projecting away completed finder observations preserves the whole chronological state.

Every marked segment therefore extends the same public graph as the ordinary signer.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open HashSig OracleSpec OracleComp

private theorem project_complete {pp : PublicParam} {α : Type} (q : Nat) (p : OracleComp (Ops pp) α)
    (s : State pp) :
    Prod.map id Prod.fst <$> (simulateQ (complete pp q) p).run s =
      (simulateQ (chronicle pp q) (simulateQ (expandCall pp) p)).run s.1 := by
  rw [← QueryImpl.simulateQ_compose]
  apply map_run_simulateQ_eq_of_query_map_eq
  intro t st
  simp only [complete, StateT.run_mk, bind_pure_comp, Functor.map_map, QueryImpl.compose]
  exact id_map _

/-- The same supported marked path gives a real path before observing the end marks. -/
protected theorem Done.real {pp q} {α : Type} {p : Body pp α} {r s a out t}
    (ran : Done q p r s a out t) : Ran q (realize p) r s.1 a out t.1 := by
  unfold Ran realize
  rw [StateT.run_mk,← project_complete q (p.run r) s,support_map]
  exact ⟨_,ran,rfl⟩

/-- Every chronological arrival in a marked prefix remains in a marked continuation. -/
protected theorem Done.arrivals {pp q} {α : Type} {p : Body pp α} {r s a out t}
    (ran : Done q p r s a out t) : s.1.2 ⊆ t.1.2 := by
  intro n old
  apply simulateQ_run_preservesInv (chronicle pp q) (fun g => n ∈ g.2) _ _ _ old _ ran.real
  intro op st was z step
  have added := ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp step).2
  change z.2.2 = remember pp op st.1 z.1 st.2 at added
  rw [added]
  rcases op with ((u | b) | g) | note
  · exact was
  · by_cases fresh : TrialGraphWatch.MessageAt pp b ∧ st.1.1.2.1.1 b = none
    · simpa only [remember,ite_eq_left fresh] using (List.mem_cons_of_mem (.word b z.1 st.1) was)
    · simpa only [remember,ite_eq_right fresh] using was
  · exact was
  · exact List.mem_cons_of_mem _ was

/-- A newly completed finder prepends a mark and every other operation keeps all previous marks. -/
protected theorem Done.marks {pp q} {α : Type} {p : Body pp α} {r s a out t}
    (ran : Done q p r s a out t) : s.2 ⊆ t.2 := by
  intro x old
  apply simulateQ_run_preservesInv (complete pp q) (fun g => x ∈ g.2) _ _ _ old _ ran
  intro op st was z step
  simp only [complete,StateT.run_mk,mem_support_bind_iff,mem_support_pure_iff] at step
  obtain ⟨⟨_,_⟩,_,rfl⟩ := step
  cases op with
  | inl => exact was
  | inr => exact List.mem_cons_of_mem _ was

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
