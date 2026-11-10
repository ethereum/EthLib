module

public import EthLib.Engine.PayloadBodies
public import EthLib.Engine.Proofs.Json

/-!
# Proofs: `engine_getPayloadBodiesByHash` and `engine_getPayloadBodiesByRange`

A request is too large exactly when it asks for more bodies than the node takes.

So a request of at most 32 bodies is never too large.

The withdrawals of a body are `null` exactly for a block before Shapella.

Its block access list is `null` exactly for a block before Glamsterdam, or when it was pruned.

By hash, an answer has one entry per requested hash, in order.

Each entry is the body that the store holds for its hash, or `null` where it holds none.

By range, a request with `start` or `count` at 0 is invalid, whatever the store.

`start` is checked first, so a request with both at 0 fails on `start`.

An answer has `count` entries, or fewer when the range passes the latest known block.

Entry `i` is the body of canonical block `start + i`, which is at most the latest known block.

When the range reaches the latest known block, the last entry is that block's entry.

The store holds the body of that block, so the entry is not `null`.

A range that starts past the latest known block has an empty answer.
-/

public section

namespace EthLib.Engine

open EthLib.Base

/-! ## The request limit -/

/-- A request of at most 32 bodies is never too large. -/
theorem checkRequestSize_eq_ok_of_le_bodies (store : BodyStore) (count : Nat)
    (h : count ≤ MIN_BODIES_REQUEST_LIMIT) : checkRequestSize store.maxRequest count = .ok () :=
  (checkRequestSize_eq_ok_iff _ _).2 (Nat.le_trans h store.le_maxRequest)

/-! ## The fields of a body -/

namespace StoredBody

/-- The withdrawals of a body are `null` exactly for a block before Shapella. -/
theorem toV1_withdrawals_eq_none_iff (b : StoredBody) :
    b.toV1.withdrawals = none ↔ b.fork < .shapella := by
  simp only [toV1, sinceValue]
  by_cases h : Fork.shapella ≤ b.fork
  · simp only [h, dite_true, reduceCtorEq, false_iff]
    exact Nat.not_lt.2 h
  · simp only [h, dite_false, true_iff]
    exact Nat.not_le.1 h

/-- From Shapella, the withdrawals of a body are those of the block. -/
theorem toV1_withdrawals_of_le (b : StoredBody) (h : .shapella ≤ b.fork) :
    b.toV1.withdrawals = some (b.withdrawals h) := by
  simp [toV1, sinceValue, h]

/-- The transactions of a body are those of the block. -/
@[simp] theorem toV1_transactions (b : StoredBody) : b.toV1.transactions = b.transactions := rfl

/-- Version 2 holds the transactions and withdrawals of version 1. -/
@[simp] theorem toV2_toV1 (b : StoredBody) : b.toV2.toExecutionPayloadBodyV1 = b.toV1 := rfl

/-- The block access list of a body is `null` exactly before Glamsterdam or when it was pruned.
-/
theorem toV2_blockAccessList_eq_none_iff (b : StoredBody) :
    b.toV2.blockAccessList = none ↔
      b.fork < .glamsterdam ∨ ∃ h : .glamsterdam ≤ b.fork, b.blockAccessList h = none := by
  simp only [toV2, sinceValue]
  by_cases h : Fork.glamsterdam ≤ b.fork
  · simp only [h, dite_true, Option.join_some, exists_true_left]
    have : ¬ b.fork < .glamsterdam := Nat.not_lt.2 h
    simp [this]
  · simp only [h, dite_false, Option.join_none, true_iff]
    exact .inl (Nat.not_le.1 h)

/-- From Glamsterdam, the block access list of a body is the one that the store holds. -/
theorem toV2_blockAccessList_of_le (b : StoredBody) (h : .glamsterdam ≤ b.fork) :
    b.toV2.blockAccessList = b.blockAccessList h := by
  simp [toV2, sinceValue, h]

end StoredBody

/-! ## By hash -/

/-- A request by hash succeeds exactly when it is not too large.

Its answer is the stored body of each hash, in order. -/
theorem bodiesByHash_eq_ok_iff (store : BodyStore) (hashes : List Hash32)
    (bodies : List (Option StoredBody)) :
    bodiesByHash store hashes = .ok bodies ↔
      hashes.length ≤ store.maxRequest ∧ bodies = hashes.map store.byHash := by
  unfold bodiesByHash checkRequestSize
  by_cases h : store.maxRequest < hashes.length
  · simp only [h, ite_true, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
      reduceCtorEq, false_iff, not_and]
    exact fun hle => absurd h (Nat.not_lt.2 hle)
  · simp [h, pure, Except.pure, bind, Except.bind, eq_comm]; omega

/-- A request by hash fails exactly when it is too large. -/
theorem bodiesByHash_eq_error_iff (store : BodyStore) (hashes : List Hash32) (e : EngineError) :
    bodiesByHash store hashes = .error e ↔
      store.maxRequest < hashes.length ∧ e = .tooLargeRequest := by
  unfold bodiesByHash checkRequestSize
  by_cases h : store.maxRequest < hashes.length
  · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, eq_comm]
  · simp [h, pure, Except.pure, bind, Except.bind]

/-- Version 1 by hash answers the body of each hash, in order, or `null` where none is held. -/
theorem getPayloadBodiesByHashV1_eq_ok_iff (store : BodyStore) (hashes : List Hash32)
    (answer : List (Option ExecutionPayloadBodyV1)) :
    getPayloadBodiesByHashV1 store hashes = .ok answer ↔
      hashes.length ≤ store.maxRequest ∧
        answer = hashes.map fun h => (store.byHash h).map StoredBody.toV1 := by
  unfold getPayloadBodiesByHashV1
  cases hb : bodiesByHash store hashes with
  | error e =>
    simp only [Functor.map, Except.map, reduceCtorEq, false_iff, not_and]
    intro hle
    exact absurd ((bodiesByHash_eq_error_iff store hashes e).1 hb).1 (Nat.not_lt.2 hle)
  | ok bodies =>
    obtain ⟨hle, rfl⟩ := (bodiesByHash_eq_ok_iff store hashes bodies).1 hb
    simp [Functor.map, Except.map, hle, eq_comm, Function.comp_def]

/-- Version 2 by hash answers the body of each hash, in order, or `null` where none is held. -/
theorem getPayloadBodiesByHashV2_eq_ok_iff (store : BodyStore) (hashes : List Hash32)
    (answer : List (Option ExecutionPayloadBodyV2)) :
    getPayloadBodiesByHashV2 store hashes = .ok answer ↔
      hashes.length ≤ store.maxRequest ∧
        answer = hashes.map fun h => (store.byHash h).map StoredBody.toV2 := by
  unfold getPayloadBodiesByHashV2
  cases hb : bodiesByHash store hashes with
  | error e =>
    simp only [Functor.map, Except.map, reduceCtorEq, false_iff, not_and]
    intro hle
    exact absurd ((bodiesByHash_eq_error_iff store hashes e).1 hb).1 (Nat.not_lt.2 hle)
  | ok bodies =>
    obtain ⟨hle, rfl⟩ := (bodiesByHash_eq_ok_iff store hashes bodies).1 hb
    simp [Functor.map, Except.map, hle, eq_comm, Function.comp_def]

/-- An answer by hash has one entry per requested hash. -/
theorem length_of_bodiesByHash_eq_ok {store : BodyStore} {hashes : List Hash32}
    {bodies : List (Option StoredBody)} (h : bodiesByHash store hashes = .ok bodies) :
    bodies.length = hashes.length := by
  rw [((bodiesByHash_eq_ok_iff store hashes bodies).1 h).2, List.length_map]

/-- Entry `i` of an answer by hash is the stored body of hash `i`. -/
theorem getElem_of_bodiesByHash_eq_ok {store : BodyStore} {hashes : List Hash32}
    {bodies : List (Option StoredBody)} (h : bodiesByHash store hashes = .ok bodies)
    (i : Nat) (hi : i < bodies.length) :
    bodies[i] = store.byHash (hashes[i]'(length_of_bodiesByHash_eq_ok h ▸ hi)) := by
  simp only [((bodiesByHash_eq_ok_iff store hashes bodies).1 h).2, List.getElem_map]

/-! ## By range -/

/-- A request by range with `start` at 0 is invalid, whatever the store. -/
theorem bodiesByRange_of_start_eq_zero (store : BodyStore) (count : UInt64) :
    bodiesByRange store 0 count = .error (.invalidParams "start: below 1") := rfl

/-- A request by range with `start` at least 1 and `count` at 0 is invalid, whatever the store.
-/
theorem bodiesByRange_of_count_eq_zero (store : BodyStore) (start : UInt64) (h : start ≠ 0) :
    bodiesByRange store start 0 = .error (.invalidParams "count: below 1") := by
  simp [bodiesByRange, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A request by range fails exactly when `start` or `count` is 0, or `count` is too large. -/
theorem bodiesByRange_eq_error_iff (store : BodyStore) (start count : UInt64) (e : EngineError) :
    bodiesByRange store start count = .error e ↔
      (start = 0 ∧ e = .invalidParams "start: below 1") ∨
      (start ≠ 0 ∧ count = 0 ∧ e = .invalidParams "count: below 1") ∨
      (start ≠ 0 ∧ count ≠ 0 ∧ store.maxRequest < count.toNat ∧ e = .tooLargeRequest) := by
  unfold bodiesByRange checkRequestSize
  by_cases hs : start = 0
  · subst hs; simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, eq_comm]
  by_cases hc : count = 0
  · subst hc; simp [hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, eq_comm]
  by_cases hm : store.maxRequest < count.toNat
  · simp [hs, hc, hm, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, eq_comm]
  · simp [hs, hc, hm, pure, Except.pure, bind, Except.bind]

/-- A request by range succeeds exactly when three conditions hold.

Both `start` and `count` are at least 1, and `count` is at most the limit.

Its answer is the stored body of each canonical block from `start`, up to the latest one. -/
theorem bodiesByRange_eq_ok_iff (store : BodyStore) (start count : UInt64)
    (bodies : List (Option StoredBody)) :
    bodiesByRange store start count = .ok bodies ↔
      start ≠ 0 ∧ count ≠ 0 ∧ count.toNat ≤ store.maxRequest ∧
        bodies = (List.range (rangeLength store start.toNat count.toNat)).map fun i =>
          store.canonical (start.toNat + i) := by
  unfold bodiesByRange checkRequestSize
  by_cases hs : start = 0
  · subst hs; simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  by_cases hc : count = 0
  · subst hc; simp [hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  by_cases hm : store.maxRequest < count.toNat
  · simp only [hs, hc, hm, ite_true, ite_false, throw, throwThe, MonadExceptOf.throw, bind,
      Except.bind, reduceCtorEq, false_iff, not_and]
    exact fun _ _ hle => absurd hm (Nat.not_lt.2 hle)
  · simp [hs, hc, hm, pure, Except.pure, bind, Except.bind, eq_comm]; omega

/-- An answer by range has `count` entries, or fewer when it passes the latest known block. -/
theorem length_of_bodiesByRange_eq_ok {store : BodyStore} {start count : UInt64}
    {bodies : List (Option StoredBody)} (h : bodiesByRange store start count = .ok bodies) :
    bodies.length = min count.toNat (store.latest + 1 - start.toNat) := by
  rw [((bodiesByRange_eq_ok_iff store start count bodies).1 h).2.2.2]
  simp [rangeLength]

/-- Entry `i` of an answer by range is the stored body of canonical block `start + i`. -/
theorem getElem_of_bodiesByRange_eq_ok {store : BodyStore} {start count : UInt64}
    {bodies : List (Option StoredBody)} (h : bodiesByRange store start count = .ok bodies)
    (i : Nat) (hi : i < bodies.length) :
    bodies[i] = store.canonical (start.toNat + i) := by
  simp only [((bodiesByRange_eq_ok_iff store start count bodies).1 h).2.2.2, List.getElem_map,
    List.getElem_range]

/-- Each entry of an answer by range is for a block at most the latest known one. -/
theorem le_latest_of_bodiesByRange_eq_ok {store : BodyStore} {start count : UInt64}
    {bodies : List (Option StoredBody)} (h : bodiesByRange store start count = .ok bodies)
    (i : Nat) (hi : i < bodies.length) : start.toNat + i ≤ store.latest := by
  have := length_of_bodiesByRange_eq_ok h
  omega

/-- When a range reaches the latest known block, the last entry of its answer is that block's.

The store holds the body of that block, so that entry is not `null`. -/
theorem getLast?_of_bodiesByRange_eq_ok {store : BodyStore} {start count : UInt64}
    {bodies : List (Option StoredBody)} (h : bodiesByRange store start count = .ok bodies)
    (hstart : start.toNat ≤ store.latest) (hend : store.latest < start.toNat + count.toNat) :
    bodies.getLast? = some (store.canonical store.latest) := by
  have hlen := length_of_bodiesByRange_eq_ok h
  have hpos : 0 < bodies.length := by omega
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega),
    getElem_of_bodiesByRange_eq_ok h _ (by omega)]
  congr 2
  omega

/-- When a range reaches the latest known block, the last entry of its answer holds a body.

That rests on the store holding the body of its latest known block. -/
theorem getLast?_isSome_of_bodiesByRange_eq_ok {store : BodyStore} {start count : UInt64}
    {bodies : List (Option StoredBody)} (h : bodiesByRange store start count = .ok bodies)
    (hstart : start.toNat ≤ store.latest) (hend : store.latest < start.toNat + count.toNat) :
    ∃ body, bodies.getLast? = some (some body) := by
  rw [getLast?_of_bodiesByRange_eq_ok h hstart hend]
  exact ⟨_, congrArg some (Option.some_get store.latest_held).symm⟩

/-- A range that starts past the latest known block has an empty answer. -/
theorem eq_nil_of_bodiesByRange_eq_ok {store : BodyStore} {start count : UInt64}
    {bodies : List (Option StoredBody)} (h : bodiesByRange store start count = .ok bodies)
    (hstart : store.latest < start.toNat) : bodies = [] := by
  have := length_of_bodiesByRange_eq_ok h
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- Version 1 by range answers the body of each canonical block from `start`, or `null`. -/
theorem getPayloadBodiesByRangeV1_eq_ok_iff (store : BodyStore) (start count : UInt64)
    (answer : List (Option ExecutionPayloadBodyV1)) :
    getPayloadBodiesByRangeV1 store start count = .ok answer ↔
      start ≠ 0 ∧ count ≠ 0 ∧ count.toNat ≤ store.maxRequest ∧
        answer = (List.range (rangeLength store start.toNat count.toNat)).map fun i =>
          (store.canonical (start.toNat + i)).map StoredBody.toV1 := by
  unfold getPayloadBodiesByRangeV1
  cases hb : bodiesByRange store start count with
  | error e =>
    simp only [Functor.map, Except.map, reduceCtorEq, false_iff, not_and]
    intro hs hc hle
    rcases (bodiesByRange_eq_error_iff store start count e).1 hb with h | h | h
    · exact (hs h.1).elim
    · exact (hc h.2.1).elim
    · exact absurd h.2.2.1 (Nat.not_lt.2 hle)
  | ok bodies =>
    obtain ⟨hs, hc, hle, rfl⟩ := (bodiesByRange_eq_ok_iff store start count bodies).1 hb
    simp [Functor.map, Except.map, hs, hc, hle, eq_comm, Function.comp_def]

/-- Version 2 by range answers the body of each canonical block from `start`, or `null`. -/
theorem getPayloadBodiesByRangeV2_eq_ok_iff (store : BodyStore) (start count : UInt64)
    (answer : List (Option ExecutionPayloadBodyV2)) :
    getPayloadBodiesByRangeV2 store start count = .ok answer ↔
      start ≠ 0 ∧ count ≠ 0 ∧ count.toNat ≤ store.maxRequest ∧
        answer = (List.range (rangeLength store start.toNat count.toNat)).map fun i =>
          (store.canonical (start.toNat + i)).map StoredBody.toV2 := by
  unfold getPayloadBodiesByRangeV2
  cases hb : bodiesByRange store start count with
  | error e =>
    simp only [Functor.map, Except.map, reduceCtorEq, false_iff, not_and]
    intro hs hc hle
    rcases (bodiesByRange_eq_error_iff store start count e).1 hb with h | h | h
    · exact (hs h.1).elim
    · exact (hc h.2.1).elim
    · exact absurd h.2.2.1 (Nat.not_lt.2 hle)
  | ok bodies =>
    obtain ⟨hs, hc, hle, rfl⟩ := (bodiesByRange_eq_ok_iff store start count bodies).1 hb
    simp [Functor.map, Except.map, hs, hc, hle, eq_comm, Function.comp_def]

end EthLib.Engine
