module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedGraph
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedDelay
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedResidual
public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Mixed

/-!
# Residual state and refusal in the normalized caller

The mixed program has public full words and internal graph operations.

Its successful result carries both residual tables.

A refusal keeps the graph effects of the completed prefix.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig TwoLayerGraph Honest OracleComp OracleSpec CanonicalGraph.PairedQueries


/-- Keep the residual tables on a successful return and the remaining budget on either outcome. -/
@[expose] def visible {α R : Type} (z : (Option α × Nat) × R) : Option (α × R) × Nat :=
  (z.1.1.map (fun a => (a, z.2)), z.1.2)

/-- The mixed caller charges full public words and admits internal graph operations for free. -/
@[expose] noncomputable def mixedImpl :
    QueryImpl MixedWorld (OptionT (StateT Nat (OracleComp SharedSpec))) :=
  WeightedCap.guard (mixedCost (H := ChainGraph.Word) (F := HashOutput) (fun _ =>
      0)) (expand PairedHashWord.halves)

/--
Compare the admitted caller and the mixed pre-cap source at arbitrary warm local and graph states.
-/
@[expose] def SameMixed {α : Type} (pp : PublicParam) (p : Selected pp α)
    (m : MixedLocal pp α) : Prop :=
  ∀ q r, simulateQ (graph pp).eagerImpl (visible <$> (((p.run).run q).run r)) =
    simulateQ (graph pp).eagerImpl (((simulateQ mixedImpl (m.run r)).run).run q)

private theorem normalized_bind {α β R : Type} (p : WithCap R α) (f : α → WithCap R β)
    (q : Nat) (r : R) :
    visible <$> ((((p >>= f).run).run q).run r) =
      ((visible <$> (((p.run).run q).run r)) >>= fun z => match z with
        | (none, left) => pure (none, left)
        | (some (a, localState), left) => visible <$> ((((f a).run).run left).run localState)) := by
  simp only [OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind, bind_map_left]
  apply bind_congr
  rintro ⟨⟨(_ | a), left⟩, extra⟩
  · rfl
  · rfl

protected theorem SameMixed.bind {pp : PublicParam} {α β : Type} {p : Selected pp α}
    {m : MixedLocal pp α}
    {f : α → Selected pp β} {g : α → MixedLocal pp β}
    (first : SameMixed pp p m) (rest : ∀ a, SameMixed pp (f a) (g a)) :
    SameMixed pp (p >>= f) (m >>= g) := by
  intro q r
  rw [normalized_bind, simulateQ_bind, first q r]
  simp only [StateT.run_bind, simulateQ_bind, OptionT.run_bind, Option.elimM]
  apply bind_congr
  rintro ⟨(_ | ⟨a, extra⟩), left⟩
  · rfl
  · exact rest a left extra

theorem SameMixed.pure {pp : PublicParam} {α : Type} (a : α) :
    SameMixed pp (pure a) (pure a) := by
  intro q r
  simp [visible]

theorem SameMixed.of_eager {pp : PublicParam} {α : Type} {p p' : Selected pp α}
    {m : MixedLocal pp α}
    (equiv : SameCap pp p p') (matched : SameMixed pp p' m) : SameMixed pp p m := by
  intro q r
  simpa only [simulateQ_map, equiv q r] using matched q r

/-- A returned mixed result was supported by the original, unguarded mixed caller. -/
theorem mixed_completed {α : Type} (pp : PublicParam) (p : OracleComp MixedWorld α)
    {q initial a left final}
    (ran : ((some a, left), final) ∈ support
      ((simulateQ (graph pp).eagerImpl (((simulateQ mixedImpl p).run).run q)).run initial)) :
    a ∈ support p := by
  let native := (graph pp).eagerImpl ∘ₛ expand PairedHashWord.halves
  have projected : (some a, final) ∈ support ((simulateQ (graph pp).eagerImpl
      (Prod.fst <$> (((simulateQ mixedImpl p).run).run q))).run initial) := by
    simp only [simulateQ_map, StateT.run_map, support_map]
    exact ⟨_, ran, rfl⟩
  rw [mixedImpl, WeightedCap.run_guard, ← QueryImpl.simulateQ_compose] at projected
  have orig := WeightedCap.mem_support_of_capCompOpt_some native
    (mixedCost (H := ChainGraph.Word) (F := HashOutput) (fun _ => 0)) p q initial a final projected
  exact mem_support_of_mem_support_simulateQ_run native p initial orig

/-- Compare an adaptive suffix using the private table actually returned by the prefix. -/
theorem mixed_bind_at {pp : PublicParam} {α β : Type} {p : Selected pp α} {m : MixedLocal pp α}
    {f : α → Selected pp β} {g : α → MixedLocal pp β} (q : Nat) (r : ResidualCache pp)
    (head : simulateQ (graph pp).eagerImpl (visible <$> (((p.run).run q).run r)) =
      simulateQ (graph pp).eagerImpl (((simulateQ mixedImpl (m.run r)).run).run q))
    (tail : ∀ a localState, (a, localState) ∈ support (m.run r) → ∀ left,
      simulateQ (graph pp).eagerImpl (visible <$> ((((f a).run).run left).run localState)) =
      simulateQ (graph pp).eagerImpl (((simulateQ mixedImpl
        ((g a).run localState)).run).run left)) :
    simulateQ (graph pp).eagerImpl (visible <$> (((((p >>= f).run).run q).run r))) =
      simulateQ (graph pp).eagerImpl (((simulateQ mixedImpl ((m >>= g).run r)).run).run q) := by
  rw [normalized_bind, simulateQ_bind, head]
  simp only [StateT.run_bind, simulateQ_bind, OptionT.run_bind, Option.elimM]
  ext initial : 1
  simp only [StateT.run_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨⟨(_ | ⟨a, extra⟩), left⟩, st⟩ ran
  · rfl
  · exact congrArg (fun op => StateT.run op st) (tail a extra (mixed_completed pp _ ran) left)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
