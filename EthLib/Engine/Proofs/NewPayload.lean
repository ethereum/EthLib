module

public import EthLib.Engine.NewPayload
public import EthLib.Engine.Proofs.Block
public import EthLib.Engine.Proofs.Json

/-!
# Proofs: the checks of `engine_newPayload`

Each fork from Paris to Glamsterdam has a version of the method, and no other fork has one.

Version 5 takes Glamsterdam alone.

Below version 5 the payload decodes exactly as a structure of a version that the method takes.

From version 5 it decodes exactly as a payload of version 4, with its access list and its slot.

A request list passes the checks exactly when each request has more than one byte.

The first byte of each request is its type, and the types strictly increase along the list.

Without a JSON-RPC error, the parameters are an array of the values of the version, none null.

A payload that fails the checks is invalid, or has an invalid block hash at version 1.

It has an invalid block hash exactly when its block hash is wrong and the version is 1.

Its latest valid hash is null.

So without the parent's state a payload is never valid: it is syncing, or it failed the checks.

If the last block of a chain is not the parent, a payload that passes the checks is syncing.

If it is the parent, a payload whose block passes the state transition is valid.

A block that fails it without an abort makes the payload invalid, with the block error.

A block and a state come back exactly for a valid payload.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (BlockChain RecentBlock stateTransition)

/-- Two errors with one code come from one constructor. -/
theorem EngineError.code_injective (e₁ e₂ : EngineError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [EngineError.code] at h; exact absurd h (by decide))

/-- Two reasons with one code come from one constructor. -/
theorem PayloadError.code_injective (e₁ e₂ : PayloadError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [PayloadError.code] at h; exact absurd h (by decide))

/-- Some version of the method takes a fork exactly when the fork is from Paris to Glamsterdam. -/
theorem exists_acceptsFork_iff (fork : Fork) :
    (∃ version, acceptsFork version fork = true) ↔ .paris ≤ fork ∧ fork < .hegota := by
  constructor
  · rintro ⟨version, h⟩
    revert h
    unfold acceptsFork
    split <;> cases fork <;> decide
  · intro ⟨hLow, hHigh⟩
    cases fork <;> first
      | exact absurd hLow (by decide)
      | exact absurd hHigh (by decide)
      | exact ⟨1, rfl⟩
      | exact ⟨2, rfl⟩
      | exact ⟨3, rfl⟩
      | exact ⟨4, rfl⟩
      | exact ⟨5, rfl⟩

/-- Version 5 of the method takes exactly Glamsterdam. -/
theorem acceptsFork_five_iff (fork : Fork) : acceptsFork 5 fork = true ↔ fork = .glamsterdam := by
  simp [acceptsFork]

/-- The payload decoder of version 5 rejects a payload without its block access list.

The error is an invalid parameter, as step 2 of `engine_newPayloadV5` asks. -/
theorem payloadParam_five_of_not_mem {j : Lean.Json} {fs : List (String × Lean.Json)}
    (hfs : Json.fields "payload" j = .ok fs) (hmiss : "blockAccessList" ∉ fs.map Prod.fst) :
    payloadParam 5 j = .error (.invalidParams "payload: not the fields of version 4") := by
  -- No field has the name of the list, so the payload does not have the fields of version 4.
  have hany : (fs.any fun field => field.1 == "blockAccessList") = false := by
    rw [List.any_eq_false]
    intro field hmem heq
    exact hmiss (List.mem_map.mpr ⟨field, hmem, by simpa using heq⟩)
  have hfields : Json.hasExactly fs Json.payloadFieldsV4 = false := by
    simp [Json.hasExactly, Json.payloadFieldsV4, Json.amsterdamFields, hany]
  simp [payloadParam, Json.payloadV4, hfs, hfields, bind, Except.bind]

/-- Below version 5, the payload decodes exactly as a structure of a version that the method takes.

Version 1 takes structure version 1, version 2 takes 1 or 2, and versions 3 and 4 take 3.

No access list or slot comes with it. -/
theorem payloadParam_eq_ok_iff_of_lt {version : Nat} {j : Lean.Json}
    {r : Json.AnyPayload × Option (ByteArray × UInt64)} (hv : version < 5) :
    payloadParam version j = .ok r ↔
      Json.anyPayload j = .ok r.1 ∧ acceptsStructure version r.1.version = true ∧ r.2 = none := by
  obtain ⟨any, extra⟩ := r
  have hlt : ¬ version ≥ 5 := by omega
  simp only [payloadParam, hlt, ↓reduceIte]
  constructor
  · intro h
    obtain ⟨a, ha, h⟩ := bind_ok_iff.mp h
    -- A structure version that the method does not take fails with an invalid parameter.
    by_cases hs : acceptsStructure version a.version = true
    · simp only [hs, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ha, hs, rfl⟩
    · simp [hs, bind, Except.bind] at h
  · rintro ⟨ha, hs, rfl⟩
    simp [ha, hs, bind, Except.bind, pure, Except.pure]

/-- From version 5, the payload decodes exactly as a payload of version 4.

Its access list and its slot come with it. -/
theorem payloadParam_eq_ok_iff_of_le {version : Nat} {j : Lean.Json}
    {r : Json.AnyPayload × Option (ByteArray × UInt64)} (hv : 5 ≤ version) :
    payloadParam version j = .ok r ↔
      ∃ blockAccessList slotNumber, Json.payloadV4 j = .ok (r.1, blockAccessList, slotNumber) ∧
        r.2 = some (blockAccessList, slotNumber) := by
  obtain ⟨any, extra⟩ := r
  have hge : version ≥ 5 := hv
  simp only [payloadParam, hge, ↓reduceIte]
  constructor
  · intro h
    obtain ⟨⟨a, bal, slot⟩, ha, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨bal, slot, ha, rfl⟩
  · rintro ⟨bal, slot, ha, rfl⟩
    simp [ha, bind, Except.bind, pure, Except.pure]

/-- A list passes the check exactly when each request has more than one byte.

The first bytes of the requests must also be strictly increasing along the list.

So a list passes with types in any increasing order, gaps between them allowed. -/
theorem validRequests_iff : ∀ {requests : List ByteArray},
    validRequests requests = true ↔
      (∀ r ∈ requests, 1 < r.size) ∧ (requests.map fun r => r[0]!).Pairwise (· < ·)
  | [] => by simp [validRequests]
  | [r] => by simp [validRequests]
  | r :: s :: rest => by
    have ih := @validRequests_iff (s :: rest)
    -- A request of more than one byte has a first byte, its type.
    by_cases hr : 1 < r.size
    · by_cases hs : 1 < s.size
      · have hr0 : r[0]? = some r[0]! := by
          rw [getElem!_def, getElem?_pos r 0 (by omega)]
        have hs0 : s[0]? = some s[0]! := by
          rw [getElem!_def, getElem?_pos s 0 (by omega)]
        simp only [validRequests, hr0, hs0, hr, hs, decide_true, Bool.true_and,
          Bool.and_eq_true, decide_eq_true_eq, ih]
        simp only [List.forall_mem_cons, List.map_cons, List.pairwise_cons, List.mem_map,
          forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hr, hs, true_and]
        constructor
        · rintro ⟨hab, hSize, hTail, hPair⟩
          exact ⟨hSize, ⟨hab, fun t ht => UInt8.lt_trans hab (hTail t ht)⟩, hTail, hPair⟩
        · rintro ⟨hSize, ⟨hab, -⟩, hTail, hPair⟩
          exact ⟨hab, hSize, hTail, hPair⟩
      · simp only [validRequests]
        constructor
        · intro h
          split at h
          · simp [hs] at h
          · exact absurd h (by simp)
        · rintro ⟨hSize, -⟩
          exact absurd (hSize s (by simp)) hs
    · simp only [validRequests]
      constructor
      · intro h
        split at h
        · simp [hr] at h
        · exact absurd h (by simp)
      · rintro ⟨hSize, -⟩
        exact absurd (hSize r (by simp)) hr

/-- Request lists that pass the check have strictly increasing types. -/
theorem pairwise_of_validRequests {requests : List ByteArray}
    (h : validRequests requests = true) :
    requests.Pairwise fun r s => ∃ a b, r[0]? = some a ∧ s[0]? = some b ∧ a < b := by
  obtain ⟨hSize, hTypes⟩ := validRequests_iff.mp h
  rw [List.pairwise_map] at hTypes
  refine List.Pairwise.imp_of_mem (fun {r s} hr hs hlt => ⟨r[0]!, s[0]!, ?_, ?_, hlt⟩) hTypes
  · rw [getElem!_def, getElem?_pos r 0 (by have := hSize r hr; omega)]
  · rw [getElem!_def, getElem?_pos s 0 (by have := hSize s hs; omega)]

/-- Each request of a list that passes the check has more than one byte: its type and its data. -/
theorem size_of_validRequests {requests : List ByteArray} (h : validRequests requests = true) :
    ∀ r ∈ requests, 1 < r.size :=
  (validRequests_iff.mp h).1

/-- Request lists that pass the check have distinct types, their first bytes.

Each request has a first byte, so no type here is a default value. -/
theorem nodup_types_of_validRequests {requests : List ByteArray}
    (h : validRequests requests = true) : (requests.map fun r => r[0]!).Nodup :=
  (validRequests_iff.mp h).2.imp UInt8.ne_of_lt

/-! ## The parameters of the checks -/

/-- Without a JSON-RPC error, the parameters are an array of the values of the version.

None of them is null. -/
theorem params_of_checkNewPayload_ok {config : ChainConfig} {version : Nat} {params : Lean.Json}
    {r : Except (PayloadStatus × PayloadError) (CheckedBlock version)}
    (h : checkNewPayload config version params = .ok r) :
    ∃ items : Array Lean.Json, params = .arr items ∧ items.size = paramCount version ∧
      ∀ j ∈ items, j.isNull = false := by
  cases params with
  | arr items =>
    refine ⟨items, rfl, ?_⟩
    by_cases hc : (items.toList.length == paramCount version) = true ∧
        (items.toList.all fun x => !x.isNull) = true
    · simp only [List.all_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      exact ⟨by simpa using hc.1, fun j hj => hc.2 j (by simpa using hj)⟩
    · unfold checkNewPayload at h
      rw [bind_ok_iff] at h
      obtain ⟨l, hl, h⟩ := h
      cases hl
      -- Reduce without inlining the join points of the do block, so the check is the outer `if`.
      dsimp -zeta only at h
      rw [ite_eq_right hc, bind_ok_iff] at h
      -- A failed check is an error, never a result.
      obtain ⟨_, hInvalid, -⟩ := h
      cases hInvalid
  -- Any other JSON value is not an array, so the read fails at once.
  | _ => cases h

/-! ## A payload that fails the checks -/

/-- A payload that fails the checks has an invalid block hash for a wrong block hash at version 1.

Otherwise it is invalid.

Its latest valid hash is null. -/
private theorem status_cases_of_checkNewPayload {config : ChainConfig} {version : Nat}
    {params : Lean.Json} {status : PayloadStatus} {reason : PayloadError}
    (h : checkNewPayload config version params = .ok (.error (status, reason))) :
    status.latestValidHash = none ∧
      (status.status = .invalidBlockHash ∧
          (version = 1 ∧ ∃ expected computed, reason = .wrongBlockHash expected computed) ∨
        status.status = .invalid ∧
          ¬(version = 1 ∧ ∃ expected computed, reason = .wrongBlockHash expected computed)) := by
  cases params with
  | arr items =>
    unfold checkNewPayload at h
    rw [bind_ok_iff] at h
    obtain ⟨l, hl, h⟩ := h
    cases hl
    by_cases hc : (items.toList.length == paramCount version) = true ∧
        (items.toList.all fun x => !x.isNull) = true
    · dsimp only at h
      rw [ite_eq_left hc] at h
      -- Walk every step: a failing step contradicts the result, and each value read is kept.
      repeat' (first
        | (cases h; done)
        | (obtain ⟨_, step, h⟩ := bind_ok_iff.mp h
           first | cases step | obtain ⟨_, -, rfl⟩ := map_ok_iff.mp step | skip)
        | split at h)
      -- Only a wrong block hash at version 1 has that status; every other case is invalid.
      all_goals
        cases h
        first
          | exact ⟨rfl, .inl ⟨rfl, ‹version = 1›, _, _, rfl⟩⟩
          | (refine ⟨rfl, .inr ⟨rfl, ?_⟩⟩
             rintro ⟨hv, a, b, he⟩
             first
               | exact ‹¬version = 1› hv
               | solve_by_elim
               | (cases he; done))
          | ((by_cases hv : version = 1 <;> simp [hv]) <;> done)
    -- Parameters of the wrong shape fail with a JSON-RPC error, never with a status.
    · dsimp -zeta only at h
      rw [ite_eq_right hc, bind_ok_iff] at h
      obtain ⟨_, hInvalid, -⟩ := h
      cases hInvalid
  -- Any other JSON value is not an array, so the read fails at once.
  | _ => cases h

/-- A payload that fails the checks is invalid, or has an invalid block hash at version 1.

At any other version, its status is invalid.

Its latest valid hash is null. -/
theorem status_of_checkNewPayload {config : ChainConfig} {version : Nat} {params : Lean.Json}
    {status : PayloadStatus} {reason : PayloadError}
    (h : checkNewPayload config version params = .ok (.error (status, reason))) :
    status.latestValidHash = none ∧
      (status.status = .invalid ∨ status.status = .invalidBlockHash ∧ version = 1) := by
  obtain ⟨hn, ⟨hs, hv, -⟩ | ⟨hs, -⟩⟩ := status_cases_of_checkNewPayload h
  · exact ⟨hn, .inr ⟨hs, hv⟩⟩
  · exact ⟨hn, .inl hs⟩

/-- A failed check answers an invalid block hash exactly for a wrong block hash at version 1. -/
theorem invalidBlockHash_iff_of_checkNewPayload {config : ChainConfig} {version : Nat}
    {params : Lean.Json} {status : PayloadStatus} {reason : PayloadError}
    (h : checkNewPayload config version params = .ok (.error (status, reason))) :
    status.status = .invalidBlockHash ↔
      version = 1 ∧ ∃ expected computed, reason = .wrongBlockHash expected computed := by
  obtain ⟨-, ⟨hs, hw⟩ | ⟨hs, hw⟩⟩ := status_cases_of_checkNewPayload h
  · exact iff_of_true hs hw
  · rw [hs]
    exact iff_of_false (by simp) hw

/-- Without the parent's state, a payload is never valid, and its latest valid hash is null.

It is syncing with no reason when it passes the checks, and invalid with a reason otherwise.

The status of an invalid block hash comes only at version 1. -/
theorem status_of_newPayloadWithoutState {config : ChainConfig} {version : Nat}
    {params : Lean.Json} {status : PayloadStatus} {reason : Option PayloadError}
    (h : newPayloadWithoutState config version params = .ok (status, reason)) :
    status.latestValidHash = none ∧
      (status.status = .syncing ∧ reason = none ∨
        (status.status = .invalid ∨ status.status = .invalidBlockHash ∧ version = 1) ∧
          reason.isSome) := by
  unfold newPayloadWithoutState at h
  cases hc : checkNewPayload config version params with
  | error e => simp [hc, bind, Except.bind] at h
  | ok r =>
    cases r with
    | error p =>
      obtain ⟨st, re⟩ := p
      simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hn, hs⟩ := status_of_checkNewPayload hc
      exact ⟨hn, .inr ⟨hs, rfl⟩⟩
    | ok _ =>
      simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩

/-! ## The status on a chain that holds the parent -/

/-- A payload that gives back a block and a state is valid.

It passed the checks before execution, and its block passed the transition to that state. -/
theorem of_newPayloadOnChain_some {chain : BlockChain} {version : Nat} {params : Lean.Json}
    {status : PayloadStatus} {reason : Option PayloadError} {block : RecentBlock}
    {post : Execution.State.State}
    (h : newPayloadOnChain chain version params = .ok (status, reason, some (block, post))) :
    status.status = .valid ∧ ∃ checked, checkNewPayload chain.config version params =
      .ok (.ok checked) ∧ stateTransition chain checked.block false = .ok post ∧
        block = ⟨checked.fork, checked.block.header, []⟩ := by
  unfold newPayloadOnChain at h
  cases hC : checkNewPayload chain.config version params with
  | error e => simp [hC, bind, Except.bind] at h
  | ok r =>
    cases r with
    | error p => simp [hC, bind, Except.bind, pure, Except.pure] at h
    | ok checked =>
      simp only [hC, bind, Except.bind] at h
      split at h
      · split at h
        · split at h
          · rename_i post' hRun
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
            obtain ⟨rfl, -, rfl, rfl⟩ := h
            exact ⟨rfl, checked, rfl, hRun, rfl⟩
          · simp [pure, Except.pure] at h
          · simp [pure, Except.pure] at h
        · simp [pure, Except.pure] at h
      · simp [pure, Except.pure] at h

/-- A payload on a chain is valid exactly when a block and a state come back.

So a valid answer always comes from a block that passed the state transition. -/
theorem valid_iff_of_newPayloadOnChain {chain : BlockChain} {version : Nat} {params : Lean.Json}
    {status : PayloadStatus} {reason : Option PayloadError}
    {next : Option (RecentBlock × Execution.State.State)}
    (h : newPayloadOnChain chain version params = .ok (status, reason, next)) :
    status.status = .valid ↔ ∃ block post, next = some (block, post) := by
  constructor
  · intro hValid
    unfold newPayloadOnChain at h
    cases hC : checkNewPayload chain.config version params with
    | error e => simp [hC, bind, Except.bind] at h
    | ok r =>
      cases r with
      | error p =>
        -- A payload that fails the checks is invalid, never valid.
        obtain ⟨st, re⟩ := p
        simp only [hC, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        rcases (status_of_checkNewPayload hC).2 with hs | ⟨hs, -⟩ <;> rw [hs] at hValid <;>
          cases hValid
      | ok checked =>
        simp only [hC, bind, Except.bind] at h
        -- Every answer of the execution is syncing or invalid, except the one with a block.
        repeat' split at h
        all_goals simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        all_goals obtain ⟨rfl, -, rfl⟩ := h
        all_goals first | exact ⟨_, _, rfl⟩ | cases hValid
  · rintro ⟨block, post, rfl⟩
    exact (of_newPayloadOnChain_some h).1

/-- A payload that passes the checks before execution is syncing without its parent.

The chain lacks the parent when its last block is another block, or when it has no block. -/
theorem newPayloadOnChain_of_not_parent {chain : BlockChain} {version : Nat} {params : Lean.Json}
    {checked : CheckedBlock version}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (hParent : ∀ parent, chain.recent.getLast? = some parent →
      parent.header.hash ≠ .ok checked.block.header.parentHash) :
    newPayloadOnChain chain version params = .ok (⟨.syncing, none⟩, none, none) := by
  cases hLast : chain.recent.getLast? with
  | none => simp [newPayloadOnChain, hCheck, hLast, bind, Except.bind, pure, Except.pure]
  | some parent =>
    have hHash := hParent parent hLast
    cases hP : parent.header.hash <;>
      simp_all [newPayloadOnChain, bind, Except.bind, pure, Except.pure, Except.toOption]

/-- A payload that passes the checks on its parent, and whose block passes the transition, is valid.

Its latest valid hash is its own block hash. -/
theorem newPayloadOnChain_of_stateTransition_ok {chain : BlockChain} {version : Nat}
    {params : Lean.Json} {checked : CheckedBlock version} {parent : RecentBlock}
    {post : Execution.State.State}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (hParent : chain.recent.getLast? = some parent)
    (hHash : parent.header.hash = .ok checked.block.header.parentHash)
    (hRun : stateTransition chain checked.block false = .ok post) :
    newPayloadOnChain chain version params =
      .ok (⟨.valid, checked.block.header.hash.toOption⟩, none,
        some (⟨checked.fork, checked.block.header, []⟩, post)) := by
  simp [newPayloadOnChain, hCheck, hParent, hHash, hRun, bind, Except.bind, pure, Except.pure,
    Except.toOption]

/-- A payload that passes the checks on its parent is invalid when its block fails the transition.

The failure is not an abort, and the reason of the status carries its error.

Its latest valid hash is its parent's hash, or zero for a parent before Paris. -/
theorem newPayloadOnChain_of_stateTransition_error {chain : BlockChain} {version : Nat}
    {params : Lean.Json} {checked : CheckedBlock version} {parent : RecentBlock}
    {e : Execution.Blocks.BlockError}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (hParent : chain.recent.getLast? = some parent)
    (hHash : parent.header.hash = .ok checked.block.header.parentHash)
    (hRun : stateTransition chain checked.block false = .error e)
    (hAbort : ∀ cause, e ≠ .aborted cause) :
    newPayloadOnChain chain version params =
      .ok (⟨.invalid, some (if parent.fork < .paris then 0 else checked.block.header.parentHash)⟩,
        some (.invalidBlock e), none) := by
  cases e with
  | aborted cause => exact absurd rfl (hAbort cause)
  | _ =>
    simp [newPayloadOnChain, hCheck, hParent, hHash, hRun, bind, Except.bind, pure, Except.pure,
      Except.toOption]

end EthLib.Engine
