module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchPrivateSource
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifierConflict
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedCalls
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# Repeating a signing search in the deferred game

Equal private randomizer inputs return the same base on later attempts.

The two completed public searches replay against one conflict-free cache extension.

This includes exhaustion of the counter window.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants OracleComp OracleSpec TwoLayerGraph Honest
open CanonicalGraph.PairedQueries

/-- Expand the physical mixed queries before interpreting them against the deferred graph. -/
@[expose] noncomputable def deferredMixed (pp : PublicParam) :=
  ((graph pp).deferredImpl).compose (expand PairedHashWord.halves)

private theorem deferred_finder (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) {s z last}
    (ran : z ∈ support ((simulateQ (deferredMixed pp)
      (Xmss.Internal.findCodeword mixedHash pp l e msg base 0 MAX_RANDOMIZER_TRIALS)).run s))
    (extended : z.2.1 ≤ last) (clean : ¬ (graph pp).Conflict last) :
    Xmss.Internal.findCodeword (VerifierProbe.hashAt pp last) pp l e msg base 0
      MAX_RANDOMIZER_TRIALS = some z.1 := by
  rw [deferredMixed, QueryImpl.simulateQ_compose] at ran
  rw [findCodeword_map_monad (simulateQ (expand PairedHashWord.halves)) (simulateQ_pure _)
    (simulateQ_bind _)] at ran
  simp only [expand_hash] at ran
  exact VerifierProbe.finder_replay pp l e msg base 0 MAX_RANDOMIZER_TRIALS ran extended clean

/-- A second completed attempt at the same private input returns exactly the first answer.

Both deferred runs may start from different public caches. -/
theorem SearchCut.repeat_deferred {pp l e msg r s a next t later g b final h last}
    (first : SearchCut pp (deferredMixed pp) l e msg r s a next t)
    (second : SearchCut pp (deferredMixed pp) l e msg later g b final h)
    (privateRows : next.2 ≤ later.2) (firstRows : t.1 ≤ last) (secondRows : h.1 ≤ last)
    (clean : ¬ (graph pp).Conflict last) : a = b := by
  obtain ⟨v, u, w, ha, hb⟩ := first.repeat_base second privateRows
  have firstWord := deferred_finder pp l e msg (ofBV 16 v) ha firstRows clean
  have secondWord := deferred_finder pp l e msg (ofBV 16 v) hb secondRows clean
  exact Option.some.inj (firstWord.symm.trans secondWord)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
