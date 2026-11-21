module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedMixed
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MarkedSource

/-!
# The mixed cutoff over an adaptive client's raw signing log

Each returned signing reply supplies the local tables for the next request.

The private table invariant is required only on completions of the actual prefix.

A refused operation terminates the client and preserves its previous graph effects.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open OracleComp OracleSpec TwoLayerGraph Honest HashSig

/-- The marked and mixed phases agree at this concrete quota and residual table. -/
@[expose] def MixedAt {α : Type} (pp : PublicParam) (left : Nat) (r : ResidualCache pp)
    (p : Selected pp α) (m : MixedLocal pp α) :=
  simulateQ (graph pp).eagerImpl (visible <$> (((p.run).run left).run r)) =
    simulateQ (graph pp).eagerImpl (((simulateQ mixedImpl (m.run r)).run).run left)

private theorem map_at {pp : PublicParam} {α β : Type} {p : Selected pp α} {m : MixedLocal pp α}
    {left r} (same : MixedAt pp left r p m) (f : α → β) :
    MixedAt pp left r (f <$> p) (f <$> m) := by
  simp only [← bind_pure_comp]
  exact mixed_bind_at left r same (fun a _ _ => fun q => SameMixed.pure (pp := pp) (f a) q _)

/-- The actual optional-reply adversary keeps its returned raw log in chronological order. -/
theorem client_at {α : Type} (pp : PublicParam)
    (oracle : QueryImpl (World + SigningSpec) (WriterT RawLog (MixedLocal pp)))
    (warm : ResidualCache pp → Prop)
    (step : ∀ query left r, warm r → MixedAt pp left r
      (simulateQ (selectedImpl pp) (markedSigner query).run) (oracle query).run)
    (preserved : ∀ query r, warm r → ∀ result ∈ support ((oracle query).run.run r), warm result.2)
    (p : OracleComp (World + SigningSpec) α) (left : Nat) (r : ResidualCache pp)
    (initial : warm r) :
    MixedAt pp left r (simulateQ (selectedImpl pp) (simulateQ markedSigner p).run)
      (simulateQ oracle p).run := by
  induction p using OracleComp.inductionOn generalizing left r with
  | pure a => simpa [MixedAt] using (SameMixed.pure (pp := pp) (a, ([] : RawLog)) left r)
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', simulateQ_map]
    apply mixed_bind_at left r (step t left r initial)
    rintro ⟨reply, log⟩ state reached remain
    exact map_at (ih reply remain state (preserved t r initial _ reached)) _

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
