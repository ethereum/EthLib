module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LocalDelay
public import VCVio.OracleComp.SimSemantics.OptionT.Basic

/-!
# Postpone disclosure past a capped computation

A marked chain value is stable throughout the eager graph.

If the continuation exhausts its budget, its earlier effects and its remaining budget survive.

Both the budget refusal and an ordinary signing error skip disclosure.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open EthLib.Cryptography HashSig OracleSpec OracleComp

abbrev WithCap (R : Type) := OptionT (StateT Nat (WithLocal R))

/-- Compare the budget and all private and graph state on every outcome. -/
@[expose] def SameCap {R α : Type} (pp : PublicParam) (a b : WithCap R α) : Prop :=
  ∀ q, SameLocal pp (a.run.run q) (b.run.run q)

protected theorem SameCap.bind {pp : PublicParam} {R α β : Type} {a b : WithCap R α}
    {f g : α → WithCap R β} (head : SameCap pp a b) (tail : ∀ x, SameCap pp (f x) (g x)) :
    SameCap pp (a >>= f) (b >>= g) := by
  intro q
  simp only [OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply (head q).bind
  rintro ⟨(_ | x), left⟩
  · exact fun _ => rfl
  · exact tail x left

private theorem extends_eager {pp : PublicParam} {α : Type} {op : OracleComp SharedSpec α}
    {s : SharedState} {z} (ran : z ∈ support ((simulateQ (graph pp).eagerImpl op).run s)) :
    s ≤ z.2 :=
  simulateQ_run_preservesInv _ (s ≤ ·)
    (fun _ _ prev _ hz => prev.trans ((graph pp).le_of_mem_support_eagerImpl hz)) op s le_rfl z ran

/-- Run the marker and continuation on every admitted prefix and read only on a successful reply. -/
theorem delayCap {R α β γ θ ε : Type} (pp : PublicParam) (mark : OracleComp SharedSpec θ)
    (read : OracleComp SharedSpec α) (next : θ → WithCap R (Except ε β)) (pack : α → β → γ)
    (ready : StableRead pp mark read) :
    SameCap pp (do
      let u ← liftM mark
      let a ← liftM read
      let reply ← next u
      return reply.map (pack a)) (do
      let u ← liftM mark
      match ← next u with
      | .error err => return .error err
      | .ok b => return .ok (pack (← liftM read) b)) := by
  intro budget initial
  ext s : 1
  simp only [OptionT.run_bind, OptionT.run_monadLift, OptionT.run_pure, Option.elimM,
      Option.elim_some,
    StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc,
    pure_bind, bind_map_left, simulateQ_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro u marked
  obtain ⟨a, stable⟩ := ready s u marked
  rw [stable u.2 le_rfl, pure_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨⟨⟨(_ | (_ | b)), left⟩, extra⟩, final⟩ later
  · rfl
  · rfl
  · have stored := stable final (extends_eager later)
    simp only [OptionT.run_bind, OptionT.run_monadLift, OptionT.run_pure, Option.elimM,
      Option.elim_some,
      StateT.run_bind, StateT.run_monadLift, StateT.run_pure, monadLift_self, bind_assoc,
      pure_bind, bind_map_left, simulateQ_bind, simulateQ_pure,
      stored, Except.map]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest
