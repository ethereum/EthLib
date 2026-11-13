module

public import EthLib.Engine.ForkchoiceUpdated
public import EthLib.Base.Except
public import EthLib.Engine.Proofs.Json

/-!
# Proofs: the parameters, the head and the payload attributes of `engine_forkchoiceUpdated`

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

When the update applies a valid head, attributes that fit no structure of the version give `-38003`.

When it applies none, the attributes are not read.

Attributes that fit give the answer of their checks against the head, which the tree holds.

They pass exactly when the version takes their fork and their structure is that of the fork.

Their timestamp must also be above the head's.

The attributes at that fork keep every field.

A fork that the version does not take, or no fork at all, gives `-38005`.

A structure that is not that of the fork, or a timestamp not above the head's, gives `-38003`.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Serialization.JsonRpc (field_eq_ok_iff fields fixed hasExactly paramsArray)

variable {tree : PayloadTree} {finalized : Option Hash32} {state : ForkchoiceState}
  {config : ChainConfig}

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
      ∃ fs, fields "forkchoiceState" j = .ok fs ∧
        hasExactly fs ["headBlockHash", "safeBlockHash", "finalizedBlockHash"] = true ∧
        ∃ head safe finalized, fs.lookup "headBlockHash" = some head ∧
          fs.lookup "safeBlockHash" = some safe ∧ fs.lookup "finalizedBlockHash" = some finalized ∧
          fixed "headBlockHash" 32 head = .ok s.headBlockHash ∧
          fixed "safeBlockHash" 32 safe = .ok s.safeBlockHash ∧
          fixed "finalizedBlockHash" 32 finalized = .ok s.finalizedBlockHash := by
  unfold forkchoiceStateOfJson
  simp only [bind_ok_iff, Json.liftM_eq_ok_iff]
  constructor
  · rintro ⟨fs, hfs, h⟩
    by_cases hc : hasExactly fs ["headBlockHash", "safeBlockHash", "finalizedBlockHash"] = true
    · rw [ite_eq_left hc] at h
      simp only [bind_ok_iff, Json.liftM_eq_ok_iff, field_eq_ok_iff] at h
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
    simp only [bind_ok_iff, Json.liftM_eq_ok_iff, field_eq_ok_iff]
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
        simp [paramsArray, hs, hNull, bind, Except.bind, pure, Except.pure, eq_comm,
          and_assoc]
    | [stateJson, attributes, custody] =>
      by_cases h4 : 4 ≤ version
      · cases hs : forkchoiceStateOfJson stateJson <;> cases hc : custodyColumnsOfJson custody <;>
          cases attributes <;>
          simp [paramsArray, h4, hs, hc, bind, Except.bind, pure, Except.pure, eq_comm,
            and_assoc]
      · simp [paramsArray, h4, bind, Except.bind, pure, Except.pure]
    | [] => simp [paramsArray, bind, Except.bind, pure, Except.pure]
    | [_] => simp [paramsArray, bind, Except.bind, pure, Except.pure]
    | _ :: _ :: _ :: _ :: _ => simp [paramsArray, bind, Except.bind, pure, Except.pure]
  | _ => simp [paramsArray, bind, Except.bind]

/-- Payload attributes that are neither `null` nor an object are an invalid parameter.

That holds for every version and every forkchoice state that decodes.

The error comes before any rule reads the payload tree. -/
theorem forkchoiceUpdatedParams_not_object {version : Nat} {stateJson attributes : Lean.Json}
    {s : ForkchoiceState} (hs : forkchoiceStateOfJson stateJson = .ok s)
    (hNull : attributes ≠ .null) (hObj : ∀ kvs, attributes ≠ .obj kvs) :
    forkchoiceUpdatedParams version (.arr #[stateJson, attributes]) =
      .error (.invalidParams "payloadAttributes: not an object") := by
  unfold forkchoiceUpdatedParams
  cases attributes <;> simp_all [paramsArray, bind, Except.bind, pure, Except.pure]

/-- From version 4, custody columns that decode leave the parameters as they are without them. -/
theorem forkchoiceUpdatedParams_custody {version : Nat} (four : 4 ≤ version)
    {stateJson attributes custody : Lean.Json} {columns : Option (Vector UInt8 16)}
    (decoded : custodyColumnsOfJson custody = .ok columns) :
    forkchoiceUpdatedParams version (.arr #[stateJson, attributes, custody]) =
      forkchoiceUpdatedParams version (.arr #[stateJson, attributes]) := by
  have hNull : custodyColumnsOfJson .null = .ok none := rfl
  cases hs : forkchoiceStateOfJson stateJson <;> cases attributes <;>
    simp [forkchoiceUpdatedParams, paramsArray, four, decoded, hNull, hs, bind, Except.bind,
      pure, Except.pure]

/-- In version 4, custody columns that decode never change the answer of the method.

The answer is the same as without them. -/
theorem forkchoiceUpdatedCall_custody {stateJson attributes custody : Lean.Json}
    {columns : Option (Vector UInt8 16)} (decoded : custodyColumnsOfJson custody = .ok columns) :
    forkchoiceUpdatedCall config 4 tree finalized (.arr #[stateJson, attributes, custody]) =
      forkchoiceUpdatedCall config 4 tree finalized (.arr #[stateJson, attributes]) := by
  simp only [forkchoiceUpdatedCall, forkchoiceUpdatedParams_custody (Nat.le_refl 4) decoded]

/-- Without payload attributes, every version of the method gives the same answer.

So version 4 answers as version 3. -/
theorem forkchoiceUpdatedCall_of_null {version version' : Nat} {stateJson : Lean.Json} :
    forkchoiceUpdatedCall config version tree finalized (.arr #[stateJson, .null]) =
      forkchoiceUpdatedCall config version' tree finalized (.arr #[stateJson, .null]) := by
  cases hs : forkchoiceStateOfJson stateJson <;>
    simp [forkchoiceUpdatedCall, forkchoiceUpdatedParams, paramsArray, custodyColumnsOfJson,
      hs, bind, Except.bind, pure, Except.pure]

/-- Version 4 with custody columns that decode and no attributes answers as version 3. -/
theorem forkchoiceUpdatedCall_four_of_null {stateJson custody : Lean.Json}
    {columns : Option (Vector UInt8 16)} (decoded : custodyColumnsOfJson custody = .ok columns) :
    forkchoiceUpdatedCall config 4 tree finalized (.arr #[stateJson, .null, custody]) =
      forkchoiceUpdatedCall config 3 tree finalized (.arr #[stateJson, .null]) := by
  rw [forkchoiceUpdatedCall_custody decoded, forkchoiceUpdatedCall_of_null]

/-- Attributes without exactly the fields of a version of their structure do not decode at it. -/
theorem payloadAttributesOfJson_wrong_fields {v : Nat} {j : Lean.Json}
    {fs : List (String × Lean.Json)} (hf : fields "payloadAttributes" j = .ok fs)
    (hx : hasExactly fs (attributesFields v) = false) :
    payloadAttributesOfJson v j = .error (.invalidParams "payloadAttributes: wrong fields") := by
  simp [payloadAttributesOfJson, hf, hx, bind, Except.bind, Json.invalid, throw, throwThe,
    MonadExceptOf.throw]

/-- The attributes of a version of the method fail exactly when no structure that it takes decodes.

The error is then that of invalid payload attributes. -/
theorem payloadAttributesOfVersion_eq_error_iff {version : Nat} {j : Lean.Json}
    {e : EngineError} :
    payloadAttributesOfVersion version j = .error e ↔
      e = .invalidPayloadAttributes ∧
        ∀ v ∈ attributesVersions version, ∃ e', payloadAttributesOfJson v j = .error e' := by
  unfold payloadAttributesOfVersion
  constructor
  · intro h
    split at h
    · cases h
    · next hn =>
      cases h
      refine ⟨rfl, fun v hv => ?_⟩
      have := List.findSome?_eq_none_iff.mp hn v hv
      cases hj : payloadAttributesOfJson v j <;> simp_all [Except.toOption]
  · rintro ⟨rfl, h⟩
    split
    · next a ha =>
      obtain ⟨v, hv, hf⟩ := List.exists_of_findSome?_eq_some ha
      obtain ⟨e', he⟩ := h v hv
      simp [he, Except.toOption] at hf
    · rfl

/-- On an applied valid head, attributes whose fields fit no structure of the version fail.

The answer is then the error of invalid payload attributes, `-38003`, not the status of the head.
-/
theorem forkchoiceUpdatedCall_eq_error_of_attributes {version : Nat}
    {stateJson : Lean.Json} {kvs : Std.TreeMap.Raw String Lean.Json compare}
    {fs : List (String × Lean.Json)} {s : ForkchoiceState} {status : PayloadStatus}
    {head : Hash32} (hs : forkchoiceStateOfJson stateJson = .ok s)
    (hf : forkchoiceUpdated tree finalized s = .ok (status, some head))
    (hfs : fields "payloadAttributes" (.obj kvs) = .ok fs)
    (hx : ∀ v ∈ attributesVersions version, hasExactly fs (attributesFields v) = false) :
    forkchoiceUpdatedCall config version tree finalized (.arr #[stateJson, .obj kvs]) =
      .error .invalidPayloadAttributes := by
  have hm : payloadAttributesOfVersion version (.obj kvs) = .error .invalidPayloadAttributes :=
    payloadAttributesOfVersion_eq_error_iff.mpr ⟨rfl, fun v hv =>
      ⟨_, payloadAttributesOfJson_wrong_fields hfs (hx v hv)⟩⟩
  simp [forkchoiceUpdatedCall, forkchoiceUpdatedParams, paramsArray, custodyColumnsOfJson,
    hs, hf, hm, bind, Except.bind, pure, Except.pure]

/-- When the update applies no head, the payload attributes are not read.

The answer is that of the update, whatever object the attributes are. -/
theorem forkchoiceUpdatedCall_of_no_head {version : Nat}
    {stateJson : Lean.Json} {kvs : Std.TreeMap.Raw String Lean.Json compare}
    {s : ForkchoiceState} {status : PayloadStatus}
    (hs : forkchoiceStateOfJson stateJson = .ok s)
    (hf : forkchoiceUpdated tree finalized s = .ok (status, none)) :
    forkchoiceUpdatedCall config version tree finalized (.arr #[stateJson, .obj kvs]) =
      .ok (status, none, none) := by
  simp [forkchoiceUpdatedCall, forkchoiceUpdatedParams, paramsArray, custodyColumnsOfJson,
    hs, hf, bind, Except.bind, pure, Except.pure]

/-- An applied head is a head that the tree holds. -/
theorem exists_lookup_of_forkchoiceUpdated {status : PayloadStatus} {head : Hash32}
    (hf : forkchoiceUpdated tree finalized state = .ok (status, some head)) :
    ∃ known, tree.lookup head = some known := by
  unfold forkchoiceUpdated at hf
  split at hf
  · simp [pure, Except.pure] at hf
  · next p hp =>
    split at hf
    · simp [pure, Except.pure] at hf
    · split at hf
      · simp [pure, Except.pure] at hf
      · split at hf
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hf
          exact ⟨p, hf.2 ▸ hp⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at hf

/-- On an applied valid head, decoded attributes give the answer of their checks against it.

When they pass, the answer is the status, the head, and the attributes at their fork.

When they fail, the answer is the error of the check that fails. -/
theorem forkchoiceUpdatedCall_of_attributes {version : Nat}
    {stateJson : Lean.Json} {kvs : Std.TreeMap.Raw String Lean.Json compare}
    {s : ForkchoiceState} {status : PayloadStatus} {head : Hash32} {known : KnownPayload}
    {decoded : Σ f, PayloadAttributes f}
    (hs : forkchoiceStateOfJson stateJson = .ok s)
    (hf : forkchoiceUpdated tree finalized s = .ok (status, some head))
    (hk : tree.lookup head = some known)
    (ha : payloadAttributesOfVersion version (.obj kvs) = .ok decoded) :
    forkchoiceUpdatedCall config version tree finalized (.arr #[stateJson, .obj kvs]) =
      (checkAttributes config version known decoded).map
        fun attributes => (status, some head, some attributes) := by
  cases hc : checkAttributes config version known decoded <;>
    simp [forkchoiceUpdatedCall, forkchoiceUpdatedParams, paramsArray, custodyColumnsOfJson,
      hs, hf, hk, ha, hc, bind, Except.bind, pure, Except.pure, Except.map]

/-- Attributes move to a fork exactly when their structure is that of the fork. -/
theorem PayloadAttributes.atFork_isSome_iff {a : Σ f, PayloadAttributes f} {fork : Fork} :
    (PayloadAttributes.atFork a fork).isSome ↔ attributesForkAt fork = a.1 := by
  unfold PayloadAttributes.atFork
  split <;> simp_all

/-- A field read at another fork that has it exactly when the first does keeps its value. -/
theorem sinceValue_congr {f a b : Fork} {α : Type} (h : f ≤ a ↔ f ≤ b) (x : Since f a α) :
    sinceValue (x.congr h) = sinceValue x := by
  by_cases hb : f ≤ b
  · simp [sinceValue, Since.congr, hb, h.mpr hb]
  · simp [sinceValue, hb, mt h.mp hb]

/-- Attributes at a fork keep the timestamp, the RANDAO mix and the fee recipient.

They also keep each field that comes with a fork. -/
theorem PayloadAttributes.atFork_fields {a : Σ f, PayloadAttributes f} {fork : Fork}
    {b : PayloadAttributes fork} (h : PayloadAttributes.atFork a fork = some b) :
    b.timestamp = a.2.timestamp ∧ b.prevRandao = a.2.prevRandao ∧
      b.suggestedFeeRecipient = a.2.suggestedFeeRecipient ∧
      sinceValue b.withdrawals = sinceValue a.2.withdrawals ∧
      sinceValue b.parentBeaconBlockRoot = sinceValue a.2.parentBeaconBlockRoot ∧
      sinceValue b.slotNumber = sinceValue a.2.slotNumber ∧
      sinceValue b.targetGasLimit = sinceValue a.2.targetGasLimit := by
  obtain ⟨f, a⟩ := a
  unfold PayloadAttributes.atFork at h
  split at h
  · next hf =>
    simp only [Option.some.injEq] at h
    subst h
    dsimp only at hf
    subst hf
    simp only [PayloadAttributes.ofStructure, sinceValue_congr, true_and]
  · cases h

/-- Attributes pass their checks exactly when each check holds.

The active fork at the number after the head and at their timestamp is a fork of the version.

Their structure is that of the fork, and their timestamp is above that of the head.

The result is then the attributes at that fork. -/
theorem checkAttributes_eq_ok_iff {version : Nat} {head : KnownPayload}
    {a : Σ f, PayloadAttributes f} {fork : Fork} {b : PayloadAttributes fork} :
    checkAttributes config version head a = .ok ⟨fork, b⟩ ↔
      config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat = some fork ∧
        attributesTakeFork version fork = true ∧ PayloadAttributes.atFork a fork = some b ∧
        head.timestamp < a.2.timestamp := by
  constructor
  · intro h
    cases hF : config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat with
    | none => simp [checkAttributes, hF, throw, throwThe, MonadExceptOf.throw] at h
    | some fork' =>
      cases hT : attributesTakeFork version fork' with
      | false =>
        simp [checkAttributes, hF, hT, bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at h
      | true =>
        cases hA : PayloadAttributes.atFork a fork' with
        | none =>
          simp [checkAttributes, hF, hT, hA, throw, throwThe, MonadExceptOf.throw] at h
        | some b' =>
          by_cases hTime : head.timestamp < a.2.timestamp
          · simp only [checkAttributes, hF, hT, hA, hTime, bind, Except.bind, pure, Except.pure,
              reduceIte, Except.ok.injEq, Sigma.mk.injEq] at h
            obtain ⟨rfl, hb⟩ := h
            cases hb
            exact ⟨rfl, hT, hA, hTime⟩
          · simp [checkAttributes, hF, hT, hA, hTime, bind, Except.bind, throw, throwThe,
              MonadExceptOf.throw] at h
  · rintro ⟨hFork, hTake, hAt, hTime⟩
    simp [checkAttributes, hFork, hTake, hAt, hTime, pure, Except.pure]

/-- Attributes of no fork, or of a fork that the version does not take, give `-38005`. -/
theorem checkAttributes_eq_error_of_unsupportedFork {version : Nat} {head : KnownPayload}
    {a : Σ f, PayloadAttributes f}
    (h : ∀ fork, config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat = some fork →
      attributesTakeFork version fork = false) :
    checkAttributes config version head a = .error .unsupportedFork := by
  cases hF : config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat with
  | none => simp [checkAttributes, hF, throw, throwThe, MonadExceptOf.throw]
  | some fork =>
    simp [checkAttributes, hF, h fork hF, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A version other than 2 takes only forks whose structure is the one structure that it takes.

So only version 2 can give `-38003` for the structure at the fork. -/
theorem attributesForkAt_of_attributesTakeFork {version : Nat} (hv : version ≠ 2) {fork : Fork}
    (h : attributesTakeFork version fork = true) :
    attributesForkAt fork = attributesFork version := by
  match version with
  | 0 | 1 | 3 => revert h; cases fork <;> decide
  | 2 => exact absurd rfl hv
  | n + 4 =>
    revert h
    cases fork <;> simp [attributesTakeFork, attributesForkAt, attributesFork] <;> decide

/-- Attributes of a fork of the version, whose structure is not that of the fork, give `-38003`.

Only version 2 takes two structures, so only it can fail this way. -/
theorem checkAttributes_eq_error_of_wrong_structure {version : Nat} {head : KnownPayload}
    {a : Σ f, PayloadAttributes f} {fork : Fork}
    (hFork : config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat = some fork)
    (hTake : attributesTakeFork version fork = true) (hAt : attributesForkAt fork ≠ a.1) :
    checkAttributes config version head a = .error .invalidPayloadAttributes := by
  have hNone : PayloadAttributes.atFork a fork = none := by
    simpa using mt PayloadAttributes.atFork_isSome_iff.mp hAt
  simp [checkAttributes, hFork, hTake, hNone, throw, throwThe,
    MonadExceptOf.throw]

/-- Attributes that pass the other checks, with a timestamp not above the head's, give `-38003`. -/
theorem checkAttributes_eq_error_of_not_after_head {version : Nat} {head : KnownPayload}
    {a : Σ f, PayloadAttributes f} {fork : Fork} {b : PayloadAttributes fork}
    (hFork : config.activeFork (head.number.toNat + 1) a.2.timestamp.toNat = some fork)
    (hTake : attributesTakeFork version fork = true)
    (hAt : PayloadAttributes.atFork a fork = some b) (hTime : a.2.timestamp ≤ head.timestamp) :
    checkAttributes config version head a = .error .invalidPayloadAttributes := by
  have hNot : ¬ head.timestamp < a.2.timestamp := UInt64.not_lt.mpr hTime
  simp [checkAttributes, hFork, hTake, hAt, hNot, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

end EthLib.Engine
