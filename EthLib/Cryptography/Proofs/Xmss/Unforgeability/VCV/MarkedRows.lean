module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegistrationProjection
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderIntervals
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.NoticeOrder

/-!
# Message rows between successful finder returns and their registrations

The full chronological observer projects to the physical search ledger.

Structural tree operations can update graph labels while preserving every message row.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig Constants OracleComp OracleSpec TwoLayerGraph Honest EarlierDigest EarlierDigest.Ledger
open TrialGraphWatch PostSigning CachedCodeword

/-- The two complete physical caches give equal answers to every row at this key. -/
@[expose] def SameRows (pp : PublicParam) (k : Key) (a b : JointState) : Prop :=
  ∀ input, messageKey pp input = some k → live b input = live a input

theorem SameRows.trans {pp k a b c} (h : SameRows pp k a b) (g : SameRows pp k b c) :
    SameRows pp k a c := fun input key => (g input key).trans (h input key)

/-- Project the supported original state, including its complete live message-word table. -/
protected theorem Ran.ledger {pp q} {α : Type} {p : Program pp α} {r s a out t}
    (ran : Ran q p r s a out t) :
    ((a,out),(physical t.1,t.1.1.2)) ∈ support ((simulateQ (handler pp cut) (p.run r)).run
      (physical s.1,s.1.1.2)) := by
  have jointRun := chronicle_joint pp q (p.run r) s.1 s.2
  have watchedRun := joint_ledger pp q (p.run r) s.1.1 s.1.2
  have ledgerRun := project_watch pp cut register (fun reg b => (target pp reg b).isSome)
    q (fun w => (digits w).isSome) (p.run r) s.1.1
  simp only [physical]
  dsimp only at ledgerRun
  rw [← ledgerRun, support_map]
  refine ⟨((a,out),t.1.1),?_,rfl⟩
  change ((a,out),t.1.1) ∈ support ((simulateQ (Ledger.watched pp cut register
    (fun reg b => (target pp reg b).isSome) q) (p.run r)).run s.1.1)
  rw [← watchedRun,support_map]
  refine ⟨((a,out),t.1),?_,rfl⟩
  rw [← jointRun,support_map]
  exact ⟨_,ran,rfl⟩

protected theorem Ran.outside_rows {pp q} {α : Type} {p : Program pp α} {r s a out t}
    (ran : Ran q p r s a out t) {k : Key} (away : AllQueriesSatisfy (p.run r) (Outside pp k)) :
    SameRows pp k s.1 t.1 := outside_frame pp k (p.run r) away ran.ledger

protected theorem Ran.structural_rows {pp q} {α : Type} {p : OracleComp SharedSpec α}
    {r s a out t} (ran : Ran q (carry (emitted emitStructure pp p)) r s a out t)
    (k : Key) (structural : StructuralSchedule p) : SameRows pp k s.1 t.1 :=
  ran.outside_rows (structural_outside structural pp k r)

protected theorem Ran.notice_rows {pp q n r s a out t}
    (ran : Ran (pp := pp) q (emit n) r s a out t) (k : Key) : SameRows pp k s.1 t.1 := by
  apply ran.outside_rows
  rw [emit, StateT.run_mk, ← bind_pure_comp]
  exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).2 trivial) fun _ =>
    allQueriesSatisfy_pure _ _

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
