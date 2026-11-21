module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LocalSigner

/-!
# Delaying a graph read across stateful signing

A marked value can be read in any later graph state without changing its value or the graph.

The intervening computation can also change a private cache and return an error.

Both outcomes keep the final private cache of that computation.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open EthLib.Cryptography HashSig OracleSpec OracleComp Constants LayerGraph.Hidden

private theorem extends_eager (pp : PublicParam) {α : Type} {oa : OracleComp SharedSpec α}
    {s : SharedState} {z}
    (ran : z ∈ support ((simulateQ (graph pp).eagerImpl oa).run s)) : s ≤ z.2 :=
  simulateQ_run_preservesInv _ (s ≤ ·)
    (fun _ _ prev _ hz => prev.trans ((graph pp).le_of_mem_support_eagerImpl hz)) oa s le_rfl z ran

/-- Preserve the local cache on failure while postponing the read until success. -/
theorem delayLocal {R α β γ θ ε : Type} (pp : PublicParam) (mark : OracleComp SharedSpec θ)
    (read : OracleComp SharedSpec α) (next : θ → WithLocal R (Except ε β)) (pack : α → β → γ)
    (ready : StableRead pp mark read) :
    SameLocal pp (do
      let u ← liftM mark
      let a ← liftM read
      let reply ← next u
      return reply.map (pack a)) (do
      let u ← liftM mark
      match ← next u with
      | .error e => return .error e
      | .ok b => return .ok (pack (← liftM read) b)) := by
  intro localState
  ext graphState : 1
  simp only [StateT.run_bind, StateT.run_pure, StateT.run_monadLift, monadLift_self,
    bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro u marked
  obtain ⟨a, stable⟩ := ready graphState u marked
  rw [stable u.2 le_rfl, pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨⟨answer, localFinal⟩, final⟩ later
  have stored := stable final (extends_eager pp later)
  cases answer with
  | error err => rfl
  | ok b =>
    simp only [StateT.run_bind, StateT.run_pure, StateT.run_monadLift, monadLift_self,
      bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, stored, Except.map]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
