module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedSearchCuts
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RandomizerFreshness
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedResidual

/-!
# The original draw or hit of a signing search

The low private row supplies the 16-byte randomizer base.

Only an absent low row executes a fresh sampling operation.

The high lookup still runs from the real resulting table before the public finder starts.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants OracleSpec OracleComp
open ChainGraph (Word)
open scoped OracleSpec.PrimitiveQuery Classical

private theorem randomizer_project (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (r : ResidualCache pp) :
    (mixedBase pp l e msg).run r = (fun z => (halfOf 0 z.1,
      z.2)) <$> (mixedRandomizer pp l e msg).run r := by
  simp only [mixedBase, mixedRandomizer, StateT.run_mk, StateT.run_map, Functor.map_map]

private theorem image_preimage {G α β : Type} (impl : QueryImpl MixedWorld (StateT G ProbComp))
    (p : OracleComp MixedWorld α) (f : α → β) {r t b}
    (actual : (b,t) ∈ support ((simulateQ impl (f <$> p)).run r)) :
    ∃ a, (a,t) ∈ support ((simulateQ impl p).run r) ∧ f a = b := by
  simp only [simulateQ_map, StateT.run_map, support_map] at actual
  obtain ⟨⟨a,g⟩, h, eq⟩ := actual
  have state : g = t := congrArg Prod.snd eq
  exact ⟨a, state ▸ h, congrArg Prod.fst eq⟩

/-- Split a realized top or bottom search by its own private low row at entry.

The witnesses retain both public state cuts and the final private table in either branch. -/
theorem SearchCut.private_source {G : Type} {pp : PublicParam} {impl : QueryImpl MixedWorld
    (StateT G ProbComp)}
    {l e msg r s out next t} (cut : SearchCut pp impl l e msg r s out next t) :
    let key : PrfInput := (pp, addrRnd l e, msg)
    let lo : OtherPrivate pp := ⟨.inl key, (randomizer_residual pp l e msg).1⟩
    let hi : OtherPrivate pp := ⟨.inr key, (randomizer_residual pp l e msg).2⟩
    ∃ (v : Word) (atHigh atFinder : G) (table : (OtherPrivate pp →ₒ Word).QueryCache),
      ((r.2 lo = some v ∧ atHigh = s ∧ table = r.2) ∨
        (r.2 lo = none ∧ (v, atHigh) ∈ support ((simulateQ impl (liftM
          ($ᵗ Word) : OracleComp MixedWorld Word)).run s) ∧
          table = r.2.cacheQuery lo v)) ∧
      (∃ h finalTable, ((h, finalTable), atFinder) ∈ support ((simulateQ impl
        (liftM (((OtherPrivate pp →ₒ Word).randomOracle hi).run table) : OracleComp MixedWorld
          _)).run atHigh) ∧
        next = (r.1, finalTable)) ∧
      (out,t) ∈ support ((simulateQ impl (Xmss.Internal.findCodeword mixedHash pp l e msg
        (ofBV 16 v)
        0 MAX_RANDOMIZER_TRIALS)).run atFinder) := by
  intro key lo hi
  obtain ⟨bytes, atFinder, seed, finder⟩ := cut
  have base : ((halfOf 0 bytes,next), atFinder)
    ∈ support ((simulateQ impl ((mixedBase pp l e msg).run r)).run s) := by
    rw [randomizer_project]
    simp only [simulateQ_map, StateT.run_map, support_map]
    exact ⟨_, seed, rfl⟩
  cases lookup : r.2 lo with
  | some v =>
    rw [mixedBase_hit pp l e msg r v lookup] at base
    obtain ⟨⟨high, finalTable⟩, realHigh, eq⟩ := image_preimage impl _ _ base
    have value : ofBV 16 v = halfOf 0 bytes := congrArg Prod.fst eq
    have table : (r.1,finalTable) = next := congrArg Prod.snd eq
    refine ⟨v, s, atFinder, r.2, Or.inl ⟨rfl,rfl,rfl⟩, ⟨high, finalTable, realHigh, table.symm⟩, ?_⟩
    rw [value]
    exact finder
  | none =>
    rw [mixedBase_miss pp l e msg r lookup] at base
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at base
    obtain ⟨⟨v, cut⟩, drawn, rest⟩ := base
    obtain ⟨⟨high, finalTable⟩, realHigh, eq⟩ := image_preimage impl _ _ rest
    have value : ofBV 16 v = halfOf 0 bytes := congrArg Prod.fst eq
    have table : (r.1,finalTable) = next := congrArg Prod.snd eq
    refine ⟨v, cut, atFinder, _, Or.inr ⟨rfl,drawn,rfl⟩, ⟨high, finalTable, realHigh, table.symm⟩,
      ?_⟩
    rw [value]
    exact finder

/-- Each completed attempt keeps its finder base in the private low row. -/
theorem SearchCut.saves_low {G : Type} {pp : PublicParam} {impl : QueryImpl MixedWorld
    (StateT G ProbComp)}
    {l e msg r s out next t} (cut : SearchCut pp impl l e msg r s out next t) :
    let key : PrfInput := (pp, addrRnd l e, msg)
    let lo : OtherPrivate pp := ⟨.inl key, (randomizer_residual pp l e msg).1⟩
    ∃ (v : Word) (atFinder : G), next.2 lo = some v ∧
      (out,t) ∈ support ((simulateQ impl (Xmss.Internal.findCodeword mixedHash pp l e msg
        (ofBV 16 v)
        0 MAX_RANDOMIZER_TRIALS)).run atFinder) := by
  intro key lo
  obtain ⟨v, g, f, table, source, high, publicRun⟩ := cut.private_source
  obtain ⟨h, final, realHigh, eq⟩ := high
  have stored : table lo = some v := by
    rcases source with ⟨hit, _, rfl⟩ | ⟨_, _, rfl⟩
    · exact hit
    · exact QueryCache.cacheQuery_self _ _ _
  have raw := mem_support_of_mem_support_simulateQ_run impl _ g realHigh
  have grows := QueryImpl.withCaching_cache_le uniformSampleImpl _ _ _ (coin_support _ raw)
  refine ⟨v, f, ?_, publicRun⟩
  rw [eq]
  exact grows stored

/-- Two real attempts at the same private input use the same base, even after a first failure.

This statement permits different public caches and keeps both actual finder endpoints. -/
theorem SearchCut.repeat_base {G : Type} {pp : PublicParam} {impl : QueryImpl MixedWorld
    (StateT G ProbComp)}
    {l e msg r s a next t later g b last h}
    (first : SearchCut pp impl l e msg r s a next t)
      (second : SearchCut pp impl l e msg later g b last h)
    (laterRows : next.2 ≤ later.2) :
    ∃ (v : Word) (fa fb : G),
      (a,t) ∈ support ((simulateQ impl (Xmss.Internal.findCodeword mixedHash pp l e msg (ofBV 16 v)
        0 MAX_RANDOMIZER_TRIALS)).run fa) ∧
      (b,h) ∈ support ((simulateQ impl (Xmss.Internal.findCodeword mixedHash pp l e msg (ofBV 16 v)
        0 MAX_RANDOMIZER_TRIALS)).run fb) := by
  obtain ⟨v, fa, stored, ha⟩ := first.saves_low
  obtain ⟨u, _, fb, _, source, _, hb⟩ := second.private_source
  have old := laterRows stored
  rcases source with ⟨hit, _, _⟩ | ⟨cold, _, _⟩
  · have eq : v = u := Option.some.inj (old.symm.trans hit)
    subst u
    exact ⟨v, fa, fb, ha, hb⟩
  · rw [cold] at old
    cases old

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
