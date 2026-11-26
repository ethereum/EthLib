module

public import EthLib.Cryptography.Proofs.Merkle.Build
public import EthLib.Cryptography.Proofs.Merkle.QueryBound
public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Proofs.HashSig
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Proofs: inputs a hash-based algorithm never queries

The loops of leanXMSS and leanSPHINCS are charged at most the sum of the charges of their steps.

So they query only what their steps query.

So a set of inputs that no step queries is never queried.

In the random-oracle model, a cache that holds none of those inputs still holds none after the run.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleSpec OracleComp ENNReal

/-! ## The loops are charged what their steps are charged -/

section ChargeLoops

variable {ι : Type} {spec : OracleSpec ι} {c : ι → ℕ}

open PFunctor.FreeM (IsChargeBound isChargeBound_pure wpFold)
open PFunctor (OpSpec)

/-- Computing `k` entries in order is charged the sum of the charges of the entries. -/
theorem isChargeBound_ofFnInOrder {α : Type} :
    ∀ (k : Nat) (f : Fin k → OracleComp spec α) (n : Fin k → Nat),
      (∀ i, IsChargeBound (f i) c (n i)) →
        IsChargeBound (HashSig.ofFnInOrder k f) c (∑ i, n i)
  | 0, _, _, _ => isChargeBound_pure _
  | k + 1, f, n, h => by
    rw [HashSig.ofFnInOrder_succ]
    refine ((h 0).bind fun _ => (isChargeBound_ofFnInOrder k _ _ fun i => h i.succ).bind
      fun _ => isChargeBound_pure (B := 0) _).mono (le_of_eq ?_)
    simp only [Fin.sum_univ_succ, Nat.add_zero]

/-- Computing `k` entries in order is charged `k` times the charge of one. -/
theorem isChargeBound_ofFnInOrder_const {α : Type} {n : Nat} (k : Nat)
    (f : Fin k → OracleComp spec α) (h : ∀ i, IsChargeBound (f i) c n) :
    IsChargeBound (HashSig.ofFnInOrder k f) c (k * n) :=
  (isChargeBound_ofFnInOrder k f (fun _ => n) h).mono (by simp)

/-- A walk of `steps` steps is charged `steps` times the charge of one step. -/
theorem isChargeBound_chain {α : Type} {k n : Nat} (step : Fin k → α → OracleComp spec α)
    (hstep : ∀ i v, IsChargeBound (step i v) c n) (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ k) (value : α),
      IsChargeBound (Wots.chain step start steps h value) c (steps * n)
  | 0, _, _ => isChargeBound_pure _
  | s + 1, h, value => by
    rw [Wots.chain_succ, Nat.succ_mul]
    exact (isChargeBound_chain step hstep start s _ value).bind fun _ => hstep _ _

/-- A search of `fuel` trials is charged `fuel` times the charge of one test. -/
theorem isChargeBound_findFirst {κ β : Type} {n : Nat} (trial : Nat → κ)
    (test : κ → OracleComp spec (Option β)) (htest : ∀ k, IsChargeBound (test k) c n) :
    ∀ (start fuel : Nat), IsChargeBound (Wots.findFirst trial test start fuel) c (fuel * n)
  | _, 0 => isChargeBound_pure _
  | start, fuel + 1 => by
    rw [Wots.findFirst, Nat.succ_mul]
    refine ((htest _).bind fun r => ?_).mono (le_of_eq (Nat.add_comm _ _))
    cases r with
    | none => exact isChargeBound_findFirst trial test htest (start + 1) fuel
    | some x => exact isChargeBound_pure _

/-- Every result of a search is a result of its test. -/
theorem wpFold_findFirst {κ β : Type} (trial : Nat → κ) (test : κ → OracleComp spec (Option β))
    {Q : β → Prop}
    (htest : ∀ k, wpFold (OpSpec.demonic _) (test k) fun r => ∀ b, r = some b → Q b) :
    ∀ (start fuel : Nat), wpFold (OpSpec.demonic _) (Wots.findFirst trial test start fuel)
      fun r => ∀ t b, r = some (t, b) → Q b
  | _, 0 => fun _ _ h => nomatch h
  | start, fuel + 1 => by
    rw [Wots.findFirst, PFunctor.FreeM.wpFold_bind]
    refine PFunctor.FreeM.wpFold_mono OpSpec.demonic_mono _ (fun r hr => ?_) (htest _)
    cases r with
    | none => exact wpFold_findFirst trial test htest (start + 1) fuel
    | some b => exact fun t b' h => by cases h; exact hr b rfl

end ChargeLoops

/-! ## The loops query what their steps query

A count of the queries that `p` accepts charges one per such query.

So making no such query is a charge of 0.
-/

section Loops

variable {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Prop} [DecidablePred p]

/-- Computing a vector in order queries `p` nowhere when no entry does. -/
theorem ofFnInOrder_isQueryBoundP_zero {α : Type} :
    ∀ (k : Nat) (f : Fin k → OracleComp spec α), (∀ i, IsQueryBoundP (f i) p 0) →
      IsQueryBoundP (HashSig.ofFnInOrder k f) p 0 := fun k f h =>
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_ofFnInOrder_const k f fun i =>
    (isQueryBoundP_iff_isChargeBound p _ _).1 (h i)).mono (le_of_eq (Nat.mul_zero k))

/-- A hash chain queries `p` nowhere when no step does. -/
theorem chain_isQueryBoundP_zero {α : Type} {k : Nat} (step : Fin k → α → OracleComp spec α)
    (hstep : ∀ i v, IsQueryBoundP (step i v) p 0) (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ k) (value : α),
      IsQueryBoundP (Wots.chain step start steps h value) p 0 := fun steps h value =>
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_chain step
    (fun i v => (isQueryBoundP_iff_isChargeBound p _ _).1 (hstep i v)) start steps h
      value).mono (le_of_eq (Nat.mul_zero steps))

/-- A search over trials queries `p` nowhere when no test does. -/
theorem findFirst_isQueryBoundP_zero {κ β : Type} (trial : Nat → κ)
    (test : κ → OracleComp spec (Option β)) (htest : ∀ k, IsQueryBoundP (test k) p 0) :
    ∀ (c fuel : Nat), IsQueryBoundP (Wots.findFirst trial test c fuel) p 0 := fun c fuel =>
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_findFirst trial test
    (fun k => (isQueryBoundP_iff_isChargeBound p _ _).1 (htest k)) c fuel).mono
      (le_of_eq (Nat.mul_zero fuel))

/-- A Merkle node queries `p` nowhere when no leaf and no node hash does. -/
theorem merkleNode_isQueryBoundP_zero {α : Type}
    (hash : Merkle.Position → α → α → OracleComp spec α)
    (leaves : Nat → OracleComp spec α) (hleaves : ∀ j, IsQueryBoundP (leaves j) p 0)
    (hhash : ∀ q left right, IsQueryBoundP (hash q left right) p 0)
    (q : Merkle.Position) : IsQueryBoundP (Merkle.node hash leaves q) p 0 :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (Merkle.isChargeBound_node
    (fun j => (isQueryBoundP_iff_isChargeBound p _ _).1 (hleaves j))
    (fun q a b => (isQueryBoundP_iff_isChargeBound p _ _).1 (hhash q a b)) q).mono
      (le_of_eq (by simp))

/-- A Merkle build queries `p` nowhere when no leaf and no node hash does. -/
theorem merkleBuild_isQueryBoundP_zero {α : Type}
    (hash : Merkle.Position → α → α → OracleComp spec α)
    (leaves : Nat → OracleComp spec α) (hleaves : ∀ j, IsQueryBoundP (leaves j) p 0)
    (hhash : ∀ q left right, IsQueryBoundP (hash q left right) p 0)
    (q : Merkle.Position) : IsQueryBoundP (Merkle.build hash leaves q) p 0 :=
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (Merkle.isChargeBound_build
    (fun j => (isQueryBoundP_iff_isChargeBound p _ _).1 (hleaves j))
    (fun q a b => (isQueryBoundP_iff_isChargeBound p _ _).1 (hhash q a b)) q).mono
      (le_of_eq (by simp))

/-- The siblings of a node query `p` nowhere when no leaf and no node hash does. -/
theorem merkleSiblings_isQueryBoundP_zero {α : Type}
    (hash : Merkle.Position → α → α → OracleComp spec α) (leaves : Nat → OracleComp spec α)
    (hleaves : ∀ j, IsQueryBoundP (leaves j) p 0)
    (hhash : ∀ q left right, IsQueryBoundP (hash q left right) p 0) :
    ∀ (q : Merkle.Position) (k : Nat), IsQueryBoundP (Merkle.siblings hash leaves q k) p 0 :=
  fun q k => (isQueryBoundP_iff_isChargeBound p _ _).2 <| (Merkle.isChargeBound_siblings
    (fun j => (isQueryBoundP_iff_isChargeBound p _ _).1 (hleaves j))
    (fun q a b => (isQueryBoundP_iff_isChargeBound p _ _).1 (hhash q a b)) q k).mono
      (le_of_eq (by simp))

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
