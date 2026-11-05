module

public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Xmss.Types
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Proofs: inputs a hash-based algorithm never queries

The loops of leanXMSS and leanSPHINCS query only what their steps query.

So a set of inputs that no step queries is never queried.

In the random-oracle model, a cache that holds none of those inputs still holds none after the run.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleSpec OracleComp ENNReal

/-! ## The loops query what their steps query -/

section Loops

variable {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Prop} [DecidablePred p]

/-- Computing a vector in order queries `p` nowhere when no entry does. -/
theorem ofFnInOrder_isQueryBoundP_zero {α : Type} :
    ∀ (k : Nat) (f : Fin k → OracleComp spec α), (∀ i, IsQueryBoundP (f i) p 0) →
      IsQueryBoundP (Xmss.ofFnInOrder k f) p 0
  | 0, _, _ => isQueryBoundP_pure _ _ _
  | k + 1, f, h => by
    rw [Xmss.ofFnInOrder]
    exact isQueryBoundP_bind_zero _ _ (h 0) fun _ =>
      isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero k _ fun i => h i.succ)
        fun _ => isQueryBoundP_pure _ _ _

/-- A hash chain queries `p` nowhere when no step does. -/
theorem chain_isQueryBoundP_zero {α : Type} {k : Nat} (step : Fin k → α → OracleComp spec α)
    (hstep : ∀ i v, IsQueryBoundP (step i v) p 0) (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ k) (value : α),
      IsQueryBoundP (Wots.chain step start steps h value) p 0
  | 0, _, _ => isQueryBoundP_pure _ _ _
  | s + 1, h, value => by
    rw [Wots.chain_succ]
    exact isQueryBoundP_bind_zero _ _ (chain_isQueryBoundP_zero step hstep start s _ value)
      fun _ => hstep _ _

/-- A search over trials queries `p` nowhere when no test does. -/
theorem findFirst_isQueryBoundP_zero {κ β : Type} (trial : Nat → κ)
    (test : κ → OracleComp spec (Option β)) (htest : ∀ k, IsQueryBoundP (test k) p 0) :
    ∀ (c fuel : Nat), IsQueryBoundP (Wots.findFirst trial test c fuel) p 0
  | _, 0 => isQueryBoundP_pure _ _ _
  | c, fuel + 1 => by
    rw [Wots.findFirst]
    refine isQueryBoundP_bind_zero _ _ (htest _) fun r => ?_
    cases r with
    | none => exact findFirst_isQueryBoundP_zero trial test htest (c + 1) fuel
    | some x => exact isQueryBoundP_pure _ _ _

/-- A Merkle node queries `p` nowhere when no leaf and no node hash does. -/
theorem merkleNode_isQueryBoundP_zero {α : Type} (hash : Nat → Nat → α → α → OracleComp spec α)
    (leaves : Nat → OracleComp spec α) (hleaves : ∀ j, IsQueryBoundP (leaves j) p 0)
    (hhash : ∀ level j left right, IsQueryBoundP (hash level j left right) p 0)
    (level j : Nat) : IsQueryBoundP (Merkle.node hash leaves level j) p 0 :=
  Merkle.node_rec hash (fun x => IsQueryBoundP x p 0)
    (fun hx hf => isQueryBoundP_bind_zero _ _ hx hf) leaves hleaves hhash level j

/-- The siblings of a node query `p` nowhere when no leaf and no node hash does. -/
theorem merkleSiblings_isQueryBoundP_zero {α : Type}
    (hash : Nat → Nat → α → α → OracleComp spec α) (leaves : Nat → OracleComp spec α)
    (hleaves : ∀ j, IsQueryBoundP (leaves j) p 0)
    (hhash : ∀ level j left right, IsQueryBoundP (hash level j left right) p 0) :
    ∀ (level j k : Nat), IsQueryBoundP (Merkle.siblings hash leaves level j k) p 0
  | _, _, 0 => isQueryBoundP_pure _ _ _
  | level, j, k + 1 => by
    rw [Merkle.siblings]
    exact isQueryBoundP_bind_zero _ _
      (merkleNode_isQueryBoundP_zero hash leaves hleaves hhash _ _) fun _ =>
        isQueryBoundP_bind_zero _ _
          (merkleSiblings_isQueryBoundP_zero hash leaves hleaves hhash _ _ k)
          fun _ => isQueryBoundP_pure _ _ _

/-- A climb queries `p` nowhere when no node hash does. -/
theorem climb_isQueryBoundP_zero {α : Type} (hash : Nat → Nat → α → α → OracleComp spec α)
    (hhash : ∀ level j left right, IsQueryBoundP (hash level j left right) p 0) :
    ∀ (siblings : List α) (level j : Nat) (current : α),
      IsQueryBoundP (Merkle.climb hash level j current siblings) p 0
  | [], _, _, _ => isQueryBoundP_pure _ _ _
  | _ :: rest, level, j, current => by
    rw [Merkle.climb]
    exact isQueryBoundP_bind_zero _ _ (hhash _ _ _ _) fun _ =>
      climb_isQueryBoundP_zero hash hhash rest _ _ _

end Loops

/-! ## The cache keeps out what is never queried -/

section Cache

variable {ι : Type} [DecidableEq ι] {hashSpec : OracleSpec ι}
  [∀ t : hashSpec.Domain, SampleableType (hashSpec.Range t)]

/-- The cache holds no input that `p` marks. -/
def CacheAvoids (p : ℕ ⊕ ι → Prop) (cache : hashSpec.QueryCache) : Prop :=
  ∀ x, p (.inr x) → cache x = none

/-- **A run that never queries a set of inputs never caches one.**

The run starts from a cache that holds none of the inputs that `p` marks.

It makes no query that `p` marks.

Then every cache it can end with holds none of them either. -/
theorem cache_eq_none_of_mem_support_run_romImpl {α : Type} {p : ℕ ⊕ ι → Prop}
    [DecidablePred p] {oa : OracleComp (unifSpec + hashSpec) α} (h : IsQueryBoundP oa p 0)
    {cache : hashSpec.QueryCache} (hcache : CacheAvoids p cache)
    {z : α × hashSpec.QueryCache}
    (hz : z ∈ support ((simulateQ hashSpec.romImpl oa).run cache)) :
    CacheAvoids p z.2 := by
  have hall : oa.AllQueriesSatisfy (fun t => ¬p t) :=
    (isQueryBoundP_zero_iff oa _).1 ((isQueryBoundP_congr_pred fun _ => not_not.symm).1 h)
  refine hall.holds_of_mem_support_run_simulateQ (CacheAvoids p)
    (fun t ht s hs w hw => ?_) hcache hz
  rcases t with n | t
  · rw [roSim.run_apply_inl] at hw
    simp only [support_map, Set.mem_image] at hw
    obtain ⟨_, _, rfl⟩ := hw
    exact hs
  · rw [romImpl_apply_inr, randomOracle.run_eq] at hw
    intro x hx
    have hne : x ≠ t := fun he => ht (he ▸ hx)
    cases hst : s t with
    | some u =>
      simp only [hst, support_pure, Set.mem_singleton_iff] at hw
      exact hw ▸ hs x hx
    | none =>
      simp only [hst, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hw
      obtain ⟨u, _, rfl⟩ := hw
      rw [QueryCache.cacheQuery_of_ne _ _ hne]
      exact hs x hx

/-! ## Bounds on a run, step by step -/

/-- Simulating a bind runs the first part, then the rest from the cache it leaves. -/
theorem run'_simulateQ_romImpl_bind {α β : Type} (oa : OracleComp (unifSpec + hashSpec) α)
    (f : α → OracleComp (unifSpec + hashSpec) β) (cache : hashSpec.QueryCache) :
    (simulateQ hashSpec.romImpl (oa >>= f)).run' cache =
      (simulateQ hashSpec.romImpl oa).run cache >>= fun z =>
        (simulateQ hashSpec.romImpl (f z.1)).run' z.2 := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- An event of the value alone, read from the run with its cache. -/
theorem prEvent_run_romImpl_fst {α : Type} (oa : OracleComp (unifSpec + hashSpec) α)
    (cache : hashSpec.QueryCache) (E : α → Prop) :
    Pr{let z ← (simulateQ hashSpec.romImpl oa).run cache}[E z.1] =
      Pr{let a ← (simulateQ hashSpec.romImpl oa).run' cache}[E a] := by
  rw [StateT.run'_eq, prEvent_map]

/-- **A bound after a prefix that keeps an invariant of the cache.**

The prefix ends with the invariant from the starting cache.

From every cache with the invariant, the rest's event has probability at most `ε`.

Then the whole run's event has probability at most `ε`. -/
theorem prEvent_run'_romImpl_bind_le {α β : Type} (Inv : hashSpec.QueryCache → Prop)
    (oa : OracleComp (unifSpec + hashSpec) α) (f : α → OracleComp (unifSpec + hashSpec) β)
    (E : β → Prop) {ε : ℝ≥0∞} {cache : hashSpec.QueryCache}
    (hinv : ∀ z ∈ support ((simulateQ hashSpec.romImpl oa).run cache), Inv z.2)
    (hf : ∀ a c, Inv c → Pr{let y ← (simulateQ hashSpec.romImpl (f a)).run' c}[E y] ≤ ε) :
    Pr{let y ← (simulateQ hashSpec.romImpl (oa >>= f)).run' cache}[E y] ≤ ε := by
  rw [run'_simulateQ_romImpl_bind]
  exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => hf z.1 z.2 (hinv z hz)

/-- A run that ends by returning `some` never returns nothing. -/
theorem prEvent_run'_romImpl_bind_pure_some {α β : Type}
    (oa : OracleComp (unifSpec + hashSpec) α) (g : α → β) (cache : hashSpec.QueryCache) :
    Pr{let y ← (simulateQ hashSpec.romImpl
      (oa >>= fun a => pure (some (g a)))).run' cache}[y = none] = 0 :=
  le_antisymm (prEvent_run'_romImpl_bind_le (fun _ => True) _ _ _ (fun _ _ => trivial)
    fun _ _ _ => by simp) zero_le

/-- A run that ends by returning a success never returns an error. -/
theorem prEvent_run'_romImpl_bind_pure_ok {E α β : Type}
    (oa : OracleComp (unifSpec + hashSpec) α) (g : α → β) (cache : hashSpec.QueryCache) :
    Pr{let y ← (simulateQ hashSpec.romImpl
      (oa >>= fun a => pure (Except.ok (ε := E) (g a)))).run' cache}[y.isOk = false] = 0 :=
  le_antisymm (prEvent_run'_romImpl_bind_le (fun _ => True) _ _ _ (fun _ _ => trivial)
    fun _ _ _ => by simp [Except.isOk, Except.toBool]) zero_le

end Cache

end EthLib.Cryptography
