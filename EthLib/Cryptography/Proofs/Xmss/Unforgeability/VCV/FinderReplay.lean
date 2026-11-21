module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CachedCodeword
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial.Cost

/-!
# Repeating a completed search from the same randomizer

The leanXMSS draft in "WOTS+C", paragraph "Signing", searches a fixed counter window.

A repeated search can use the same base after a top-layer signing attempt fails.

All replies required for the first result are then in the cache, including every rejection.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.CachedCodeword

open Constants HashSig OracleComp OracleSpec

/-- A completed search repeats its result from a later cache, including an exhausted search. -/
theorem replay_finder (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : Nat) (initial live : HashSpec.QueryCache) {z}
    (first : z ∈ support ((simulateQ HashSpec.randomOracle
      (Internal.findCodeword hash pp l e msg base c fuel)).run initial)) (extended : z.2 ≤ live) :
    (simulateQ HashSpec.randomOracle (Internal.findCodeword hash pp l e msg base c fuel)).run live =
      pure (z.1, live) :=
  QueryImpl.run_simulateQ_withCaching_eq_pure_of_toPartialImpl uniformSampleImpl _
    (QueryCache.simulateQ_toPartialImpl_mono extended _
      (QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
        uniformSampleImpl _ first))

/-- The repeated search pays the same physical hash count on its now-cached replies. -/
theorem replay_counted_finder (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : Nat) (initial live : HashSpec.QueryCache) {z}
    (first : z ∈ support (((simulateQ (HashSpec.randomOracle.withAddCost (fun _ => (1 : Nat)))
      (Internal.findCodeword hash pp l e msg base c fuel)).runAdd).run initial))
    (extended : z.2 ≤ live) :
    ((simulateQ (HashSpec.randomOracle.withAddCost (fun _ => (1 : Nat)))
      (Internal.findCodeword hash pp l e msg base c fuel)).runAdd).run live = pure (z.1, live) := by
  rw [← QueryImpl.simulateQ_withAddCost_runAdd_fusion] at first ⊢
  exact QueryImpl.run_simulateQ_withCaching_eq_pure_of_toPartialImpl uniformSampleImpl _
    (QueryCache.simulateQ_toPartialImpl_mono extended _
      (QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
        uniformSampleImpl _ first))

private theorem run_finder_world (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : Nat) (cache : HashSpec.QueryCache) :
    (simulateQ HashSpec.romImpl
      (Internal.findCodeword (queryH (m := OracleComp OracleWorld)) pp l e msg base c fuel)).run
      cache = (simulateQ HashSpec.randomOracle
        (Internal.findCodeword hash pp l e msg base c fuel)).run cache := by
  rw [← findCodeword_world]
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := HashSpec.randomOracle)
    (fun t => by simp [forward])]

/-- A repeated search in the signer's random-oracle game returns the first result. -/
theorem replay_finder_world (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (c fuel : Nat) (initial live : HashSpec.QueryCache) {z}
    (first : z ∈ support ((simulateQ HashSpec.romImpl
      (Internal.findCodeword (queryH (m := OracleComp OracleWorld)) pp l e msg base c fuel)).run
      initial)) (extended : z.2 ≤ live) :
    (simulateQ HashSpec.romImpl
      (Internal.findCodeword (queryH (m := OracleComp OracleWorld)) pp l e msg base c fuel)).run
      live = pure (z.1, live) := by
  rw [run_finder_world] at first ⊢
  exact replay_finder pp l e msg base c fuel initial live first extended

end EthLib.Cryptography.Xmss.Unforgeability.VCV.CachedCodeword
