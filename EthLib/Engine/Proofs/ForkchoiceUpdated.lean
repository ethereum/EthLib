module

public import EthLib.Engine.ForkchoiceUpdated
public import EthLib.Base.Except
public import EthLib.Engine.Proofs.Json

/-!
# Proofs: the parameters and the head of `engine_forkchoiceUpdated`

The update is syncing exactly when the execution layer does not hold the head.

A valid head below the known finalized block is valid, and the head does not change.

Any other valid update selects a valid head that the execution layer holds.

Its safe and finalized blocks are then zero, or the head or one of its known ancestors.

An invalid head names as latest valid hash a valid block of its own chain.

That block is the valid block nearest the head.

There is none when no block of the chain is valid.

Each block of a chain after the first is the parent of the block before it.

The forkchoice state decodes exactly when its object holds exactly its three fields.

Each of them is a hash of 32 bytes.

The parameters decode exactly when they are a JSON array of two values.

The first value must also decode as a forkchoice state.

The result is that state, and whether the payload attributes are not `null`.
-/

public section

namespace EthLib.Engine

open EthLib.Base

variable {tree : PayloadTree} {finalized : Option Hash32} {state : ForkchoiceState}

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

/-- The latest valid block of a chain is its valid block nearest the head.

Every block between the head and it is invalid. -/
theorem latestValid_eq_some_iff {h v : Hash32} :
    latestValid tree h = some v ↔
      ∃ (i : Nat) (hi : i < (chainOf tree h).length), (chainOf tree h)[i] = v ∧
        (tree.lookup v).any (·.valid) = true ∧
        ∀ (j : Nat) (hj : j < i), (tree.lookup (chainOf tree h)[j]).any (·.valid) = false := by
  unfold latestValid
  rw [List.find?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hv, i, hi, rfl, hj⟩
    exact ⟨i, hi, rfl, hv, fun j hj' => by simpa using hj j hj'⟩
  · rintro ⟨i, hi, rfl, hv, hj⟩
    exact ⟨hv, i, hi, rfl, fun j hj' => by simpa using hj j hj'⟩

/-- A chain has no latest valid block exactly when none of its blocks is valid. -/
theorem latestValid_eq_none_iff {h : Hash32} :
    latestValid tree h = none ↔ ∀ x ∈ chainOf tree h, (tree.lookup x).any (·.valid) = false := by
  unfold latestValid
  simp [List.find?_eq_none]

/-- Each block of the ancestors of a block, after the first, is the parent of the one before. -/
theorem getElem?_succ_ancestors {fuel : Nat} {start b : Hash32} {i : Nat}
    (h : (ancestors tree fuel start)[i + 1]? = some b) :
    ∃ a p, (ancestors tree fuel start)[i]? = some a ∧ tree.lookup a = some p ∧
      b = p.parentHash := by
  induction fuel generalizing start i with
  | zero => simp [ancestors] at h
  | succ fuel ih =>
    cases hp : tree.lookup start with
    | none => simp [ancestors, hp] at h
    | some p =>
      simp only [ancestors, hp, List.getElem?_cons_succ] at h ⊢
      cases i with
      | zero =>
        -- The second block is the first of the ancestors of the parent, so it is the parent.
        refine ⟨start, p, rfl, hp, ?_⟩
        cases hf : fuel with
        | zero => simp [hf, ancestors] at h
        | succ fuel' =>
          rw [hf] at h
          cases hq : tree.lookup p.parentHash with
          | none => simp [ancestors, hq] at h
          | some q => simp [ancestors, hq] at h; exact h.symm
      | succ i =>
        simp only [List.getElem?_cons_succ]
        exact ih h

/-- Each block of the chain of a block, after the first, is the parent of the one before. -/
theorem getElem?_succ_chainOf {h b : Hash32} {i : Nat} (hb : (chainOf tree h)[i + 1]? = some b) :
    ∃ a p, (chainOf tree h)[i]? = some a ∧ tree.lookup a = some p ∧ b = p.parentHash :=
  getElem?_succ_ancestors hb

/-- The update is syncing exactly when the tree does not hold the head. -/
theorem forkchoiceUpdated_syncing_iff {result : PayloadStatus × Option Hash32}
    (h : forkchoiceUpdated tree finalized state = .ok result) :
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
      · split at h
        · cases h
          simp
        · cases h

/-- A valid update of a head not below the known finalized block selects that head.

The head is valid and known, and its safe and finalized blocks are on its chain.

A safe or finalized block of zero bytes stands for no block. -/
theorem forkchoiceUpdated_valid {result : PayloadStatus × Option Hash32}
    (h : forkchoiceUpdated tree finalized state = .ok result) (hValid : result.1.status = .valid)
    (hAbove : belowFinalized tree finalized state.headBlockHash = false) :
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
      -- The branch of a head below the known finalized block is excluded.
      rw [ite_eq_right (by simp [hAbove])] at h
      split at h
      · rename_i hChain
        cases h
        simp only [Bool.and_eq_true] at hChain
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hNotInvalid
        exact ⟨⟨p, hp, by simpa using hNotInvalid⟩, rfl, hChain.1, hChain.2⟩
      · cases h

/-- A valid head below the known finalized block is valid, and the head does not change.

Neither the safe nor the finalized block of the request is checked. -/
theorem forkchoiceUpdated_of_belowFinalized {p : KnownPayload}
    (hp : tree.lookup state.headBlockHash = some p) (hValid : p.valid = true)
    (hBelow : belowFinalized tree finalized state.headBlockHash = true) :
    forkchoiceUpdated tree finalized state = .ok (⟨.valid, some state.headBlockHash⟩, none) := by
  simp [forkchoiceUpdated, hp, hValid, hBelow, pure, Except.pure]

/-- An invalid head that the tree holds is invalid, with the latest valid block of its chain. -/
theorem forkchoiceUpdated_of_invalid {p : KnownPayload}
    (hp : tree.lookup state.headBlockHash = some p) (hInvalid : p.valid = false) :
    forkchoiceUpdated tree finalized state =
      .ok (⟨.invalid, latestValid tree state.headBlockHash⟩, none) := by
  simp [forkchoiceUpdated, hp, hInvalid, pure, Except.pure]

/-- Without a known finalized block, no head is below it. -/
@[simp] theorem belowFinalized_none (h : Hash32) : belowFinalized tree none h = false := rfl

/-! ## The parameters -/

/-- The forkchoice state decodes exactly when its object holds exactly its three fields.

Each of them must decode as a hash of 32 bytes, which becomes that field of the state. -/
theorem forkchoiceStateOfJson_eq_ok_iff {j : Lean.Json} {s : ForkchoiceState} :
    forkchoiceStateOfJson j = .ok s ↔
      ∃ fs, Json.fields "forkchoiceState" j = .ok fs ∧
        Json.hasExactly fs ["headBlockHash", "safeBlockHash", "finalizedBlockHash"] = true ∧
        ∃ head safe finalized, fs.lookup "headBlockHash" = some head ∧
          fs.lookup "safeBlockHash" = some safe ∧ fs.lookup "finalizedBlockHash" = some finalized ∧
          Json.fixed "headBlockHash" 32 head = .ok s.headBlockHash ∧
          Json.fixed "safeBlockHash" 32 safe = .ok s.safeBlockHash ∧
          Json.fixed "finalizedBlockHash" 32 finalized = .ok s.finalizedBlockHash := by
  unfold forkchoiceStateOfJson
  simp only [bind_ok_iff]
  constructor
  · rintro ⟨fs, hfs, h⟩
    by_cases hc : Json.hasExactly fs ["headBlockHash", "safeBlockHash", "finalizedBlockHash"] = true
    · rw [ite_eq_left hc] at h
      simp only [bind_ok_iff, Json.field_eq_ok_iff] at h
      obtain ⟨head, hl1, h1, hf1, safe, hl2, h2, hf2, fin, hl3, h3, hf3, hs⟩ := h
      cases hs
      exact ⟨fs, hfs, hc, head, safe, fin, hl1, hl2, hl3, hf1, hf2, hf3⟩
    -- An object with other fields fails with an invalid parameter, never with a state.
    · rw [ite_eq_right hc, bind_ok_iff] at h
      obtain ⟨_, hInvalid, -⟩ := h
      cases hInvalid
  · rintro ⟨fs, hfs, hc, head, safe, fin, hl1, hl2, hl3, hf1, hf2, hf3⟩
    refine ⟨fs, hfs, ?_⟩
    rw [ite_eq_left hc]
    simp only [bind_ok_iff, Json.field_eq_ok_iff]
    exact ⟨head, hl1, _, hf1, safe, hl2, _, hf2, fin, hl3, _, hf3, rfl⟩

/-- The parameters decode exactly when they are a JSON array of two values.

The first value must also decode as a forkchoice state.

The result is that state, and whether the payload attributes are not `null`. -/
theorem forkchoiceUpdatedParams_eq_ok_iff {params : Lean.Json} {r : ForkchoiceState × Bool} :
    forkchoiceUpdatedParams params = .ok r ↔
      ∃ stateJson attributes s, params = .arr #[stateJson, attributes] ∧
        forkchoiceStateOfJson stateJson = .ok s ∧
          r = (s, !attributes.isNull) := by
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
