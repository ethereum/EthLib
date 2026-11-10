module

public import EthLib.Engine.ForkchoiceUpdated
public import EthLib.Base.Except
public import EthLib.Engine.Proofs.Json

/-!
# Proofs: the parameters and the head of `engine_forkchoiceUpdated`

The update is syncing exactly when the execution layer does not hold the head.

A valid head below the known finalized block is valid, and the head does not change.

A valid update that keeps the head is exactly that case.

Any other valid update selects a valid head that the execution layer holds.

Its safe and finalized blocks are then zero, or the head or one of its known ancestors.

The update fails in one case only.

The head is valid and not below the known finalized block.

But its safe or its finalized block is neither zero nor on the chain of the head.

Otherwise such a head is valid and becomes the head.

A head that the execution layer does not hold gives a syncing update.

An invalid head names as latest valid hash a valid block of its own chain.

That block is the valid block nearest the head.

There is none when no block of the chain is valid.

Each block of a chain after the first is the parent of the block before it.

The forkchoice state decodes exactly when its object holds exactly its three fields.

Each of them is a hash of 32 bytes.

The parameters decode exactly when they are a JSON array of the state and the attributes.

From version 4 custody columns may follow, and they must then decode.

The state must decode, and the attributes must be `null` or an object.

Custody columns that decode never change the answer.

Without payload attributes, every version gives the same answer.

When the update applies a valid head, attributes of no layout of the version give `-38003`.

When it applies none, the attributes are not read.
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

/-- An update is valid with no new head exactly for a valid head below the known finalized block.

This is the answer of step 2, with the head as the latest valid block. -/
theorem forkchoiceUpdated_valid_none_iff {result : PayloadStatus × Option Hash32} :
    (forkchoiceUpdated tree finalized state = .ok result ∧ result.1.status = .valid ∧
        result.2 = none) ↔
      (∃ p, tree.lookup state.headBlockHash = some p ∧ p.valid = true) ∧
        belowFinalized tree finalized state.headBlockHash = true ∧
        result = (⟨.valid, some state.headBlockHash⟩, none) := by
  unfold forkchoiceUpdated
  cases hp : tree.lookup state.headBlockHash with
  | none =>
    simp [pure, Except.pure]
    rintro rfl
    simp
  | some p =>
    by_cases hv : p.valid = true
    · by_cases hb : belowFinalized tree finalized state.headBlockHash = true
      · simp only [hv, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq]
        simp only [Option.some.injEq, exists_eq_left', hv, true_and]
        constructor
        · rintro ⟨rfl, -, -⟩
          rfl
        · rintro rfl
          simp
      · by_cases hc : onChain tree state.headBlockHash state.safeBlockHash = true ∧
            onChain tree state.headBlockHash state.finalizedBlockHash = true
        · simp [hv, hb, hc, pure, Except.pure]
          rintro rfl
          simp
        · simp [hv, hb, hc]
    · simp [hv, pure, Except.pure]
      rintro rfl
      simp

/-- An invalid head that the tree holds is invalid, with the latest valid block of its chain. -/
theorem forkchoiceUpdated_of_invalid {p : KnownPayload}
    (hp : tree.lookup state.headBlockHash = some p) (hInvalid : p.valid = false) :
    forkchoiceUpdated tree finalized state =
      .ok (⟨.invalid, latestValid tree state.headBlockHash⟩, none) := by
  simp [forkchoiceUpdated, hp, hInvalid, pure, Except.pure]

/-- An update of a head that the tree does not hold is syncing, and the head does not change. -/
theorem forkchoiceUpdated_of_unknown (hNone : tree.lookup state.headBlockHash = none) :
    forkchoiceUpdated tree finalized state = .ok (⟨.syncing, none⟩, none) := by
  simp [forkchoiceUpdated, hNone, pure, Except.pure]

/-- A valid head with its safe and finalized blocks zero or on its chain becomes the head.

The head must not be below the known finalized block. -/
theorem forkchoiceUpdated_of_onChain {p : KnownPayload}
    (hp : tree.lookup state.headBlockHash = some p) (hValid : p.valid = true)
    (hAbove : belowFinalized tree finalized state.headBlockHash = false)
    (hSafe : onChain tree state.headBlockHash state.safeBlockHash = true)
    (hFinalized : onChain tree state.headBlockHash state.finalizedBlockHash = true) :
    forkchoiceUpdated tree finalized state =
      .ok (⟨.valid, some state.headBlockHash⟩, some state.headBlockHash) := by
  simp [forkchoiceUpdated, hp, hValid, hAbove, hSafe, hFinalized, pure, Except.pure]

/-- An update fails in one case only.

The head is valid and not below the known finalized block.

Its safe or its finalized block is then neither zero nor on the chain of the head.

The error is then that of an invalid forkchoice state. -/
theorem forkchoiceUpdated_eq_error_iff {e : EngineError} :
    forkchoiceUpdated tree finalized state = .error e ↔
      e = .invalidForkchoiceState ∧
        ∃ p, tree.lookup state.headBlockHash = some p ∧ p.valid = true ∧
          belowFinalized tree finalized state.headBlockHash = false ∧
          ¬(onChain tree state.headBlockHash state.safeBlockHash = true ∧
            onChain tree state.headBlockHash state.finalizedBlockHash = true) := by
  unfold forkchoiceUpdated
  cases hp : tree.lookup state.headBlockHash with
  | none => simp [pure, Except.pure]
  | some p =>
    by_cases hv : p.valid = true
    · by_cases hb : belowFinalized tree finalized state.headBlockHash = true
      · simp [hv, hb, pure, Except.pure]
      · by_cases hc : onChain tree state.headBlockHash state.safeBlockHash = true ∧
            onChain tree state.headBlockHash state.finalizedBlockHash = true
        · simp [hv, hb, hc, pure, Except.pure]
        · simp [hv, hb, hc, throw, throwThe, MonadExceptOf.throw]
          exact eq_comm
    · simp [hv, pure, Except.pure]

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

/-- The parameters decode exactly when they are a JSON array of the state and the attributes.

From version 4 the custody columns may follow them.

The first value must decode as a forkchoice state.

The second value must be `null` or an object.

The custody columns, `null` when absent, must decode.

The result is that state, and the payload attributes when they are an object. -/
theorem forkchoiceUpdatedParams_eq_ok_iff {version : Nat} {params : Lean.Json}
    {r : ForkchoiceState × Option Lean.Json} :
    forkchoiceUpdatedParams version params = .ok r ↔
      ∃ stateJson attributes custody s,
        (params = .arr #[stateJson, attributes] ∧ custody = .null ∨
          4 ≤ version ∧ params = .arr #[stateJson, attributes, custody]) ∧
        forkchoiceStateOfJson stateJson = .ok s ∧
        (∃ columns, custodyColumnsOfJson custody = .ok columns) ∧
        (attributes = .null ∧ r = (s, none) ∨
          ∃ kvs, attributes = .obj kvs ∧ r = (s, some (.obj kvs))) := by
  have hNull : custodyColumnsOfJson .null = .ok none := rfl
  unfold forkchoiceUpdatedParams
  cases params with
  | arr items =>
    obtain ⟨l⟩ := items
    match l with
    | [stateJson, attributes] =>
      cases hs : forkchoiceStateOfJson stateJson <;> cases attributes <;>
        simp [Json.paramsArray, hs, hNull, bind, Except.bind, pure, Except.pure, eq_comm,
          and_assoc]
    | [stateJson, attributes, custody] =>
      by_cases h4 : 4 ≤ version
      · cases hs : forkchoiceStateOfJson stateJson <;> cases hc : custodyColumnsOfJson custody <;>
          cases attributes <;>
          simp [Json.paramsArray, h4, hs, hc, bind, Except.bind, pure, Except.pure, eq_comm,
            and_assoc]
      · simp [Json.paramsArray, h4, bind, Except.bind, pure, Except.pure]
    | [] => simp [Json.paramsArray, bind, Except.bind, pure, Except.pure]
    | [_] => simp [Json.paramsArray, bind, Except.bind, pure, Except.pure]
    | _ :: _ :: _ :: _ :: _ => simp [Json.paramsArray, bind, Except.bind, pure, Except.pure]
  | _ => simp [Json.paramsArray, bind, Except.bind]

/-- Payload attributes that are neither `null` nor an object are an invalid parameter.

That holds for every version and every forkchoice state that decodes.

No rule reads the payload tree before. -/
theorem forkchoiceUpdatedParams_not_object {version : Nat} {stateJson attributes : Lean.Json}
    {s : ForkchoiceState} (hs : forkchoiceStateOfJson stateJson = .ok s)
    (hNull : attributes ≠ .null) (hObj : ∀ kvs, attributes ≠ .obj kvs) :
    forkchoiceUpdatedParams version (.arr #[stateJson, attributes]) =
      .error (.invalidParams "payloadAttributes: not an object") := by
  unfold forkchoiceUpdatedParams
  cases attributes <;> simp_all [Json.paramsArray, bind, Except.bind, pure, Except.pure]

/-- From version 4, custody columns that decode leave the parameters as they are without them. -/
theorem forkchoiceUpdatedParams_custody {version : Nat} (four : 4 ≤ version)
    {stateJson attributes custody : Lean.Json} {columns : Option (Vector UInt8 16)}
    (decoded : custodyColumnsOfJson custody = .ok columns) :
    forkchoiceUpdatedParams version (.arr #[stateJson, attributes, custody]) =
      forkchoiceUpdatedParams version (.arr #[stateJson, attributes]) := by
  have hNull : custodyColumnsOfJson .null = .ok none := rfl
  cases hs : forkchoiceStateOfJson stateJson <;> cases attributes <;>
    simp [forkchoiceUpdatedParams, Json.paramsArray, four, decoded, hNull, hs, bind, Except.bind,
      pure, Except.pure]

/-- In version 4, custody columns that decode never change the answer of the method.

The answer is the same as without them. -/
theorem forkchoiceUpdatedCall_custody {stateJson attributes custody : Lean.Json}
    {columns : Option (Vector UInt8 16)} (decoded : custodyColumnsOfJson custody = .ok columns) :
    forkchoiceUpdatedCall 4 tree finalized (.arr #[stateJson, attributes, custody]) =
      forkchoiceUpdatedCall 4 tree finalized (.arr #[stateJson, attributes]) := by
  simp only [forkchoiceUpdatedCall, forkchoiceUpdatedParams_custody (Nat.le_refl 4) decoded]

/-- Without payload attributes, every version of the method gives the same answer.

So version 4 answers as version 3. -/
theorem forkchoiceUpdatedCall_of_null {version version' : Nat} {stateJson : Lean.Json} :
    forkchoiceUpdatedCall version tree finalized (.arr #[stateJson, .null]) =
      forkchoiceUpdatedCall version' tree finalized (.arr #[stateJson, .null]) := by
  cases hs : forkchoiceStateOfJson stateJson <;>
    simp [forkchoiceUpdatedCall, forkchoiceUpdatedParams, Json.paramsArray, custodyColumnsOfJson,
      hs, bind, Except.bind, pure, Except.pure]

/-- When the update applies a valid head, attributes of no layout of the version give `-38003`.

The answer is the error of invalid payload attributes, not the status of the head. -/
theorem forkchoiceUpdatedCall_invalidPayloadAttributes {version : Nat}
    {stateJson : Lean.Json} {kvs : Std.TreeMap.Raw String Lean.Json compare}
    {s : ForkchoiceState} {status : PayloadStatus} {head : Hash32}
    (hs : forkchoiceStateOfJson stateJson = .ok s)
    (hf : forkchoiceUpdated tree finalized s = .ok (status, some head))
    (hm : methodPayloadAttributes version (.obj kvs) = .error .invalidPayloadAttributes) :
    forkchoiceUpdatedCall version tree finalized (.arr #[stateJson, .obj kvs]) =
      .error .invalidPayloadAttributes := by
  simp [forkchoiceUpdatedCall, forkchoiceUpdatedParams, Json.paramsArray, custodyColumnsOfJson,
    hs, hf, hm, bind, Except.bind, pure, Except.pure]

/-- When the update applies no head, the payload attributes are not read.

The answer is that of the update, whatever object the attributes are. -/
theorem forkchoiceUpdatedCall_of_no_head {version : Nat}
    {stateJson : Lean.Json} {kvs : Std.TreeMap.Raw String Lean.Json compare}
    {s : ForkchoiceState} {status : PayloadStatus}
    (hs : forkchoiceStateOfJson stateJson = .ok s)
    (hf : forkchoiceUpdated tree finalized s = .ok (status, none)) :
    forkchoiceUpdatedCall version tree finalized (.arr #[stateJson, .obj kvs]) =
      .ok (status, none, none) := by
  simp [forkchoiceUpdatedCall, forkchoiceUpdatedParams, Json.paramsArray, custodyColumnsOfJson,
    hs, hf, bind, Except.bind, pure, Except.pure]

end EthLib.Engine
