module

public import EthLib.Engine.ForkchoiceUpdated
public import EthLib.Base.Except

/-!
# Proofs: the parameters and the head of `engine_forkchoiceUpdated`

The update is syncing exactly when the execution layer does not hold the head.

A valid update selects a valid head that the execution layer holds.

Its safe and finalized blocks are then zero, or the head or one of its known ancestors.

An invalid head names as latest valid hash a valid block of its own chain.

The parameters decode exactly when they are a JSON array of two values.

The first value must also decode as a forkchoice state.

The result is that state when the payload attributes are `null`, and no state otherwise.
-/

public section

namespace EthLib.Engine

open EthLib.Base

variable {tree : PayloadTree} {state : ForkchoiceState}

/-- Each hash of the ancestors of a block is held by the tree. -/
theorem lookup_of_mem_ancestors {fuel : Nat} {start h : Hash32}
    (hMem : h ∈ ancestors tree fuel start) : ∃ p, tree.lookup h = some p := by
  induction fuel generalizing start with
  | zero => simp [ancestors] at hMem
  | succ fuel ih =>
    unfold ancestors at hMem
    split at hMem
    · rename_i p hp
      rcases List.mem_cons.mp hMem with rfl | hMem
      · exact ⟨p, hp⟩
      · exact ih hMem
    · simp at hMem

/-- A block that the tree holds is the first block of its chain. -/
theorem chainOf_head {h : Hash32} {p : KnownPayload} (hp : tree.lookup h = some p) :
    (chainOf tree h).head? = some h := by
  have hLen : 0 < tree.length := by
    cases tree with
    | nil => simp at hp
    | cons _ _ => simp
  obtain ⟨n, hn⟩ : ∃ n, tree.length = n + 1 := ⟨tree.length - 1, by omega⟩
  simp [chainOf, hn, ancestors, hp]

/-- The latest valid block of a chain is a valid block of that chain. -/
theorem latestValid_spec {h v : Hash32} (hv : latestValid tree h = some v) :
    v ∈ chainOf tree h ∧ (tree.lookup v).any (·.valid) = true := by
  unfold latestValid at hv
  have hValid := List.find?_some hv
  exact ⟨List.mem_of_find?_eq_some hv, hValid⟩

/-- The update is syncing exactly when the tree does not hold the head. -/
theorem forkchoiceUpdated_syncing_iff {result : PayloadStatus × Option Hash32}
    (h : forkchoiceUpdated tree state = .ok result) :
    result.1.status = .syncing ↔ tree.lookup state.headBlockHash = none := by
  unfold forkchoiceUpdated at h
  split at h
  · rename_i hNone
    cases h
    simp [hNone]
  · rename_i p hp
    simp only [hp, reduceCtorEq, iff_false]
    split at h
    · cases h
      simp
    · split at h
      · cases h
        simp
      · cases h

/-- A valid update selects a valid, known head, with its safe and finalized blocks on its chain.

A safe or finalized block of zero bytes stands for no block. -/
theorem forkchoiceUpdated_valid {result : PayloadStatus × Option Hash32}
    (h : forkchoiceUpdated tree state = .ok result) (hValid : result.1.status = .valid) :
    (∃ p, tree.lookup state.headBlockHash = some p ∧ p.valid = true) ∧
      result = (⟨.valid, some state.headBlockHash⟩, some state.headBlockHash) ∧
      onChain tree state.headBlockHash state.safeBlockHash = true ∧
      onChain tree state.headBlockHash state.finalizedBlockHash = true := by
  unfold forkchoiceUpdated at h
  split at h
  · cases h
    simp at hValid
  · rename_i p hp
    split at h
    · cases h
      simp at hValid
    · rename_i hNotInvalid
      split at h
      · rename_i hChain
        cases h
        simp only [Bool.and_eq_true] at hChain
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hNotInvalid
        exact ⟨⟨p, hp, by simpa using hNotInvalid⟩, rfl, hChain.1, hChain.2⟩
      · cases h

/-! ## The parameters -/

/-- The parameters decode exactly when they are a JSON array of two values.

The first value must also decode as a forkchoice state.

The result is that state when the payload attributes are `null`, and no state otherwise. -/
theorem forkchoiceUpdatedParams_eq_ok_iff {params : Lean.Json} {r : Option ForkchoiceState} :
    forkchoiceUpdatedParams params = .ok r ↔
      ∃ stateJson attributes s, params = .arr #[stateJson, attributes] ∧
        forkchoiceStateOfJson stateJson = .ok s ∧
          r = if attributes.isNull then some s else none := by
  unfold forkchoiceUpdatedParams
  cases params with
  | arr items =>
    obtain ⟨l⟩ := items
    -- Only a list of two values gets past the shape check.
    match l with
    | [stateJson, attributes] =>
      simp only [bind_ok_iff]
      constructor
      · rintro ⟨s, hs, hr⟩
        exact ⟨stateJson, attributes, s, rfl, hs, (Except.ok.inj hr).symm⟩
      · rintro ⟨stateJson', attributes', s, heq, hs, rfl⟩
        cases heq
        exact ⟨s, hs, rfl⟩
    | [] => simp [Json.invalid, throw, throwThe, MonadExceptOf.throw]
    | [_] => simp [Json.invalid, throw, throwThe, MonadExceptOf.throw]
    | _ :: _ :: _ :: _ => simp [Json.invalid, throw, throwThe, MonadExceptOf.throw]
  -- Any other JSON value is not an array.
  | _ => simp [Json.invalid, throw, throwThe, MonadExceptOf.throw]

end EthLib.Engine
