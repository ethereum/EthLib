module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinishedRun
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinishGame

/-!
# Local-state cuts of an actual marked signing run

The marked observer records the incoming private state of a complete finder.

It leaves the list of marks unchanged throughout every physical operation.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open OracleComp OracleSpec

/-- A completed marked program between the original residual and chronological states. -/
@[expose] def Done {pp : PublicParam} (q : Nat) {α : Type} (p : Body pp α)
    (r : ResidualCache pp) (s : State pp) (a : α) (out : ResidualCache pp) (t : State pp) : Prop :=
  ((a,out),t) ∈ support ((simulateQ (complete pp q) (p.run r)).run s)

protected theorem Done.bind {pp q} {α β : Type} {p : Body pp α} {f : α → Body pp β}
    {r s a out t} (ran : Done q (p >>= f) r s a out t) :
    ∃ b mid g, Done q p r s b mid g ∧ Done q (f b) mid g a out t := by
  unfold Done at ran ⊢
  simp only [StateT.run_bind,simulateQ_bind,mem_support_bind_iff] at ran
  obtain ⟨⟨⟨b,mid⟩,g⟩,h,k⟩ := ran
  exact ⟨b,mid,g,h,k⟩

protected theorem Done.pure_result {pp q} {α : Type} {a b : α} {r s out t}
    (ran : Done (pp := pp) q (pure b) r s a out t) : a = b ∧ out = r ∧ t = s := by
  unfold Done at ran
  simpa [and_assoc] using ran

private theorem forward {pp : PublicParam} (q : Nat) {α : Type} (p : OracleComp Queries α)
    (s : ChronicleState) (marks : List (Finish pp)) :
    (simulateQ (complete pp q) (simulateQ (fun t => liftM ((Ops pp).query (.inl t))) p)).run (s,
      marks) =
      (fun z => (z.1,z.2,marks)) <$> (simulateQ (chronicle pp q) p).run s := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, complete, expandCall,
      StateT.run_mk, bind_pure_comp, bind_map_left, map_bind]
    exact bind_congr fun z => ih z.1 z.2

protected theorem Done.physical {pp q} {α : Type} {p : Program pp α} {r s a out t}
    (ran : Done q (physical p) r s a out t) :
    ((a,out),t.1) ∈ support ((simulateQ (chronicle pp q) (p.run r)).run s.1) ∧ t.2 = s.2 := by
  rw [Done,physical,StateT.run_mk,forward,support_map] at ran
  obtain ⟨⟨z,g⟩,h,eq⟩ := ran
  cases eq
  exact ⟨h,rfl⟩

protected theorem Done.search {pp q l e m r s a out t}
    (ran : Done q (search pp l e m) r s a out t) :
    ((a,out),t.1) ∈ support ((simulateQ (chronicle pp q) ((find pp l e m).run r)).run s.1) ∧
    t.2 = ⟨⟨l,e,m,r⟩,s.1,(a,out),t.1⟩ :: s.2 := by
  simp only [Done,search,StateT.run_mk,simulateQ_spec_query,complete,expandCall,
    mem_support_bind_iff,mem_support_pure_iff] at ran
  obtain ⟨⟨z,g⟩,h,eq⟩ := ran
  cases eq
  exact ⟨h,rfl⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
