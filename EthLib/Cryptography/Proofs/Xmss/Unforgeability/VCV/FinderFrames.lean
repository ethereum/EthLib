module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegistry
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeSigner
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedStructure

/-!
# Physical message rows between a finder and its registration

Upper finder calls cannot insert a physical row for the bottom key.

The chain and sibling computations disclose no new physical message words at either key.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleComp OracleSpec
open EarlierDigest EarlierDigest.Ledger PostSigning CachedCodeword CanonicalGraph.PairedQueries

/-- An unrelated physical call cannot create a message row for this protected key. -/
@[expose] def Away (pp : PublicParam) (k : Key) : MixedWorld.Domain → Prop
  | .inl (.inr b) => messageKey pp b ≠ some k
  | _ => True

/-- Finder notices can save a snapshot while keeping the live physical words unchanged. -/
@[expose] def Outside (pp : PublicParam) (k : Key) : Queries.Domain → Prop
  | .inl t => Away pp k t
  | .inr _ => True

private theorem map_queries {ι α β : Type} {spec : OracleSpec ι} {p : OracleComp spec α}
    {P : ι → Prop} (f : α → β) (h : AllQueriesSatisfy p P) : AllQueriesSatisfy (f <$> p) P := by
  rw [← bind_pure_comp]
  exact allQueriesSatisfy_bind h fun _ => allQueriesSatisfy_pure _ _

private theorem free_away (pp : PublicParam) (k : Key) {α : Type} {p : OracleComp MixedWorld α}
    (free : AllQueriesSatisfy p (fun t => mixedCost (H := ChainGraph.Word) (F := HashOutput)
      (fun _ => 0) t = 0)) : AllQueriesSatisfy p (Away pp k) := by
  apply free.mono
  rintro ((u | b) | op) h
  · trivial
  · cases h
  · trivial

private theorem search_queries {ι κ β : Type} {spec : OracleSpec ι}
    (f : Nat → κ) (test : κ → OracleComp spec (Option β)) {P : ι → Prop}
    (each : ∀ v, AllQueriesSatisfy (test v) P) :
    ∀ c n, AllQueriesSatisfy (Wots.findFirst f test c n) P
  | _,0 => allQueriesSatisfy_pure _ _
  | c,n+1 => allQueriesSatisfy_bind (each _) fun
    | none => search_queries f test each (c+1) n
    | some _ => allQueriesSatisfy_pure _ _

private theorem marked_finder (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (c n : Nat) (k : Key) (other : (l,e) ≠ k) :
    AllQueriesSatisfy (Internal.findCodeword mixedHash pp l e msg base c n) (Away pp k) := by
  rw [Internal.findCodeword_eq]
  apply search_queries
  intro rho
  apply map_queries
  unfold messageDigest th
  rw [bind_pure_comp]
  apply map_queries
  unfold mixedHash
  apply map_queries
  apply (allQueriesSatisfy_query_iff _ _).2
  change messageKey pp (trialInput pp l e msg rho) ≠ some k
  rw [messageKey_trial]
  exact fun h => other (Option.some.inj h)

private theorem carried {pp : PublicParam} {k : Key} {α : Type} (p : MixedLocal pp α)
    (h : ∀ r, AllQueriesSatisfy (p.run r) (Away pp k)) (r) :
    AllQueriesSatisfy ((carry p).run r) (Outside pp k) := by
  exact (h r).simulateQ fun t ok => (allQueriesSatisfy_query_iff _ _).2 ok

theorem structural_outside {α : Type} {p : OracleComp SharedSpec α} (hp : StructuralSchedule p)
    (pp : PublicParam) (k : Key) (r : ResidualCache pp) :
    AllQueriesSatisfy ((carry (emitted emitStructure pp p)).run r) (Outside pp k) := by
  apply carried
  intro s
  simp only [emitted, StateT.run_monadLift, monadLift_self, bind_pure_comp]
  exact map_queries _ (free_away pp k hp.2)

/-- The entire private lookup and stopped finder can only fill physical rows at its own key. -/
theorem find_outside (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (k : Key) (other : (l,e) ≠ k) (r : ResidualCache pp) :
    AllQueriesSatisfy ((find pp l e msg).run r) (Outside pp k) := by
  unfold find
  rw [StateT.run_bind]
  apply allQueriesSatisfy_bind
  · apply map_queries
    exact (allQueriesSatisfy_query_iff _ _).2 trivial
  · intro z
    apply carried
    intro s
    rw [mixedFind, StateT.run_bind]
    apply allQueriesSatisfy_bind (free_away pp k (mixedRandomizer_free pp l e msg s))
    intro base
    simp only [StateT.run_monadLift, monadLift_self, bind_pure_comp]
    exact map_queries _ (marked_finder pp l e msg _ _ _ k other)

/-- All same-key live ledger rows survive a supported intervening program exactly. -/
theorem outside_frame {α : Type} (pp : PublicParam) (k : Key) (p : OracleComp Queries α)
    (outside : AllQueriesSatisfy p (Outside pp k)) {s : TrialGraphWatch.D × History} {z}
    (run : z ∈ support ((simulateQ (handler pp cut) p).run s)) :
    ∀ b, messageKey pp b = some k → z.2.2.1.1 b = s.2.1.1 b := by
  apply outside.holds_of_mem_support_run_simulateQ (fun g => ∀ b, messageKey pp b = some k →
    g.2.1.1 b = s.2.1.1 b) _ (fun _ _ => rfl) run
  intro t away g old result step b key
  have upd := ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).mp step).2
  change result.2.2 = update pp cut t result.1 g.2 at upd
  rw [upd]
  rcases t with ((u | a) | op) | note
  · exact old b key
  · have diff : b ≠ a := fun eq => away (eq ▸ key)
    simp only [update]
    split
    · simpa [recordWordAt, QueryCache.cacheQuery_of_ne, diff] using old b key
    · exact old b key
  · exact old b key
  · simp [update, cut, old b key]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
