module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RepeatedSearch
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RepeatedSearch
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedCacheGrowth

/-!
# Completed signing searches in a common later state

The private low row fixes the search base.

The public rows fix the answer of the whole counter window.

Both facts persist after other requests.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants OracleComp OracleSpec TwoLayerGraph Honest
open ChainGraph (Word)

/-- Store a search at its actual private input and retain its replay in any clean extension. -/
@[expose] def SearchFact (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (ans : FindAnswer) (r : ResidualCache pp) (s : SharedState) : Prop :=
  ∃ v : Word, r.2 ⟨.inl (pp,addrRnd l e,msg),(randomizer_residual pp l e msg).1⟩ = some v ∧
    ∀ g, s ≤ g → ¬ (graph pp).Conflict g →
      Xmss.Internal.findCodeword (VerifierProbe.hashAt pp g) pp l e msg (ofBV 16 v)
        0 MAX_RANDOMIZER_TRIALS = some ans

theorem SearchFact.mono {pp l e msg ans r s r' s'} (h : SearchFact pp l e msg ans r s)
    (privateRows : r.2 ≤ r'.2) (publicRows : s ≤ s') : SearchFact pp l e msg ans r' s' := by
  obtain ⟨v,old,run⟩ := h
  exact ⟨v, privateRows old, fun last later => run last (publicRows.trans later)⟩

/-- All completed searches at the same private input agree in a clean extension. -/
theorem SearchFact.agree {pp l e msg a b r s} (first : SearchFact pp l e msg a r s)
    (second : SearchFact pp l e msg b r s) (clean : ¬ (graph pp).Conflict s) : a = b := by
  obtain ⟨v, row, left⟩ := first
  obtain ⟨v', row', right⟩ := second
  obtain rfl := Option.some.inj (row.symm.trans row')
  exact Option.some.inj ((left s le_rfl clean).symm.trans (right s le_rfl clean))

/-- The conditioned private and public facts refer to the same realized search. -/
theorem SearchCut.fact {pp l e msg r s ans next t}
    (h : SearchCut pp (deferredMixed pp) l e msg r s ans next t) :
    SearchFact pp l e msg ans next t.1 := by
  obtain ⟨v, begin, stored, actual⟩ := h.saves_low
  exact ⟨v, stored, fun _ later clean => deferred_finder pp l e msg _ actual later clean⟩

theorem MixedRun.public_mono {pp : PublicParam} {α : Type} {p : MixedLocal pp α}
    {r s a next t} (ran : MixedRun (deferredMixed pp) p r s a next t) : s.1 ≤ t.1 := by
  unfold MixedRun deferredMixed at ran
  rw [QueryImpl.simulateQ_compose] at ran
  exact (graph pp).le_of_mem_support_simulateQ_deferredImpl _ ran

theorem MixedRun.private_mono {pp : PublicParam} {α : Type} {p : MixedLocal pp α}
    {r s a next t} (ran : MixedRun (deferredMixed pp) p r s a next t)
    (grows : ExtendsPrivate p) : r.2 ≤ next.2 :=
  grows _ _ (mem_support_of_mem_support_simulateQ_run _ _ _ ran)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
