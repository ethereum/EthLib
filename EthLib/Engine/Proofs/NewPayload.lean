module

public import EthLib.Engine.NewPayload
public import EthLib.Engine.Proofs.Block
public import EthLib.Engine.Proofs.Json
import EthLib.Base.Proofs.Toolchain.JsonBasic
import EthLib.Execution.Proofs.Blocks.Transition
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: the checks of `engine_newPayload`

A fork has a version of the method exactly when it is from Paris on.

The decoders read back its parameters at a version that takes their fork, within their bounds.

Without its parent's state, a payload is never valid.

With it, a payload is valid exactly when the method gives back its block and the state after it.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (BlockChain RecentBlock stateTransition MAX_EXTRA_DATA_BYTES)
open EthLib.Serialization.JsonRpc (fields hasExactly)

/-- Two errors with one code come from one constructor. -/
theorem EngineError.code_injective (e₁ e₂ : EngineError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective EngineError.code

/-- Two reasons with one code come from one constructor. -/
theorem PayloadError.code_injective (e₁ e₂ : PayloadError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective PayloadError.code

/-- Some version of the method takes a fork exactly when the fork is from Paris on. -/
theorem exists_acceptsFork_iff (fork : Fork) :
    (∃ version, acceptsFork version fork = true) ↔ .paris ≤ fork := by
  constructor
  · rintro ⟨version, h⟩
    revert h
    unfold acceptsFork
    split <;> cases fork <;> decide
  · intro hLow
    cases fork <;> first
      | exact absurd hLow (by decide)
      | exact ⟨1, rfl⟩
      | exact ⟨2, rfl⟩
      | exact ⟨3, rfl⟩
      | exact ⟨4, rfl⟩
      | exact ⟨5, rfl⟩
      | exact ⟨6, rfl⟩

/-- Version 5 of the method takes exactly Glamsterdam. -/
theorem acceptsFork_five_iff (fork : Fork) : acceptsFork 5 fork = true ↔ fork = .glamsterdam := by
  simp [acceptsFork]

/-- Version 6 of the method takes exactly Hegotá. -/
theorem acceptsFork_six_iff (fork : Fork) : acceptsFork 6 fork = true ↔ fork = .hegota := by
  simp [acceptsFork]

/-- A version takes a fork exactly when its parameters are those of the fork.

Versions 3 to 6 start at the forks that add their parameters: Dencun to Hegotá.

Each ends where the next one starts, and version 6 takes Hegotá, the last fork.

Version 2 takes Paris and Shapella, and version 1 Paris alone. -/
theorem acceptsFork_eq_true_iff (version : Nat) (fork : Fork) :
    acceptsFork version fork = true ↔
      1 ≤ version ∧ version ≤ 6 ∧ .paris ≤ fork ∧
        (version = 1 → fork < .shapella) ∧ (3 ≤ version ↔ .dencun ≤ fork) ∧
        (4 ≤ version ↔ .pectra ≤ fork) ∧ (5 ≤ version ↔ .glamsterdam ≤ fork) ∧
        (6 ≤ version ↔ .hegota ≤ fork) := by
  match version with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => cases fork <;> decide
  | n + 7 => simp [acceptsFork]

/-- The payload decoder of version 5 rejects a payload without its block access list.

The error is an invalid parameter, as step 2 of `engine_newPayloadV5` asks. -/
theorem payloadParam_five_of_not_mem {j : Lean.Json} {fs : List (String × Lean.Json)}
    (hfs : fields "payload" j = .ok fs) (hmiss : "blockAccessList" ∉ fs.map Prod.fst) :
    payloadParam 5 j = .error (.invalidParams "payload: not the fields of version 4") := by
  -- No field has the name of the list, so the payload does not have the fields of version 4.
  have hany : (fs.any fun field => field.1 == "blockAccessList") = false := by
    rw [List.any_eq_false]
    intro field hmem heq
    exact hmiss (List.mem_map.mpr ⟨field, hmem, by simpa using heq⟩)
  have hfields : hasExactly fs Json.payloadFieldsV4 = false := by
    simp [hasExactly, Json.payloadFieldsV4, Json.amsterdamFields, hany]
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

/-- A list passes the check exactly when two conditions hold.

Each request has more than one byte, so its first byte is its type.

The types strictly increase along the list, with gaps between them allowed. -/
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

/-- Decoded parameters are an array of as many values as the version takes, none of them null. -/
private theorem params_of_newPayloadParams_ok {version : Nat} {params : Lean.Json}
    {x : Json.AnyPayload × Option (ByteArray × UInt64) × Option (List Hash32) × Option Hash32 ×
      Option (List ByteArray)}
    (h : newPayloadParams version params = .ok x) :
    ∃ items : Array Lean.Json, params = .arr items ∧ items.size = paramCount version ∧
      ∀ j ∈ items, j.isNull = false := by
  cases params with
  | arr items =>
    refine ⟨items, rfl, ?_⟩
    by_cases hc : (items.toList.length == paramCount version) = true ∧
        (items.toList.all fun x => !x.isNull) = true
    · simp only [List.all_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      exact ⟨by simpa using hc.1, fun j hj => hc.2 j (by simpa using hj)⟩
    · unfold newPayloadParams at h
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

/-- Without a JSON-RPC error, the parameters are an array of the values of the version.

None of them is null. -/
theorem params_of_checkNewPayload_ok {config : ChainConfig} {version : Nat} {params : Lean.Json}
    {r : Except (PayloadStatus × PayloadError) (CheckedBlock version)}
    (h : checkNewPayload config version params = .ok r) :
    ∃ items : Array Lean.Json, params = .arr items ∧ items.size = paramCount version ∧
      ∀ j ∈ items, j.isNull = false := by
  unfold checkNewPayload at h
  obtain ⟨_, hx, -⟩ := bind_ok_iff.mp h
  exact params_of_newPayloadParams_ok hx

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
  unfold checkNewPayload at h
  -- The decoded parameters stay free; each later check is walked step by step.
  obtain ⟨⟨any, amsterdam, hashes, beaconRoot, requests⟩, -, h⟩ := bind_ok_iff.mp h
  dsimp only at h
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
theorem of_newPayloadOnChain_some {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : BlockChain} {version : Nat} {params : Lean.Json}
    {status : PayloadStatus} {reason : Option PayloadError} {block : RecentBlock}
    {post : Execution.State.State}
    (h : newPayloadOnChain transition totalDifficulty chain version params =
      .ok (status, reason, some (block, post))) :
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
          · split at h
            · rename_i post' hRun
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
                Option.some.injEq] at h
              obtain ⟨rfl, -, rfl, rfl⟩ := h
              exact ⟨rfl, checked, rfl, hRun, rfl⟩
            · simp [pure, Except.pure] at h
            · simp [pure, Except.pure] at h
          · simp [pure, Except.pure] at h
        · simp [pure, Except.pure] at h
      · simp [pure, Except.pure] at h

/-- A payload that gives back a block and a state has a parent that passes the terminal check.

So a valid answer never follows a block of proof of work that is not terminal. -/
theorem passesTerminalCheck_of_newPayloadOnChain_some {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : BlockChain} {version : Nat} {params : Lean.Json}
    {status : PayloadStatus} {reason : Option PayloadError} {block : RecentBlock}
    {post : Execution.State.State}
    (h : newPayloadOnChain transition totalDifficulty chain version params =
      .ok (status, reason, some (block, post))) :
    ∃ parent, chain.recent.getLast? = some parent ∧
      passesTerminalCheck transition totalDifficulty parent = true := by
  unfold newPayloadOnChain at h
  cases hC : checkNewPayload chain.config version params with
  | error e => simp [hC, bind, Except.bind] at h
  | ok r =>
    cases r with
    | error p => simp [hC, bind, Except.bind, pure, Except.pure] at h
    | ok checked =>
      cases hL : chain.recent.getLast? with
      | none => simp [hC, hL, bind, Except.bind, pure, Except.pure] at h
      | some parent =>
        refine ⟨parent, rfl, ?_⟩
        cases hT : passesTerminalCheck transition totalDifficulty parent
        · simp only [hC, hL, hT, bind, Except.bind] at h
          split at h <;> simp [pure, Except.pure] at h
        · rfl

/-- A payload on a chain is valid exactly when a block and a state come back.

So a valid answer always comes from a block that passed the state transition. -/
theorem valid_iff_of_newPayloadOnChain {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : BlockChain} {version : Nat} {params : Lean.Json}
    {status : PayloadStatus} {reason : Option PayloadError}
    {next : Option (RecentBlock × Execution.State.State)}
    (h : newPayloadOnChain transition totalDifficulty chain version params =
      .ok (status, reason, next)) :
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
theorem newPayloadOnChain_of_not_parent {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : BlockChain} {version : Nat} {params : Lean.Json}
    {checked : CheckedBlock version}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (hParent : ∀ parent, chain.recent.getLast? = some parent →
      parent.header.hash ≠ .ok checked.block.header.parentHash) :
    newPayloadOnChain transition totalDifficulty chain version params =
      .ok (⟨.syncing, none⟩, none, none) := by
  cases hLast : chain.recent.getLast? with
  | none => simp [newPayloadOnChain, hCheck, hLast, bind, Except.bind, pure, Except.pure]
  | some parent =>
    have hHash := hParent parent hLast
    cases hP : parent.header.hash <;>
      simp_all [newPayloadOnChain, bind, Except.bind, pure, Except.pure, Except.toOption]

/-- A payload that passes the checks before execution is invalid on a parent that is not terminal.

The parent is a block of proof of work.

It fails the conditions of a terminal block, or has a total difficulty below its difficulty.

The latest valid hash is zero, as step 2 of payload validation requires. -/
theorem newPayloadOnChain_of_not_terminal {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : BlockChain} {version : Nat} {params : Lean.Json}
    {checked : CheckedBlock version} {parent : RecentBlock}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (hParent : chain.recent.getLast? = some parent)
    (hHash : parent.header.hash = .ok checked.block.header.parentHash)
    (hPow : parent.fork < .paris)
    (hTerminal : parent.header.difficulty ≤ totalDifficulty → isTerminalPowBlock transition
      totalDifficulty (totalDifficulty - parent.header.difficulty) = false) :
    newPayloadOnChain transition totalDifficulty chain version params =
      .ok (⟨.invalid, some 0⟩, some (.invalidTerminalBlock checked.block.header.parentHash),
        none) := by
  have hFail : passesTerminalCheck transition totalDifficulty parent = false := by
    have hp : decide (Fork.paris ≤ parent.fork) = false := decide_eq_false (Nat.not_le.mpr hPow)
    rw [passesTerminalCheck, hp, Bool.false_or]
    by_cases hd : parent.header.difficulty ≤ totalDifficulty
    · rw [hTerminal hd, Bool.and_false]
    · simp [hd]
  simp [newPayloadOnChain, hCheck, hParent, hHash, hFail, bind, Except.bind, pure, Except.pure,
    Except.toOption]

/-- A payload that passes the checks on its parent, and whose block passes the transition, is valid.

Its parent passes the terminal block check.

Its latest valid hash is its own block hash. -/
theorem newPayloadOnChain_of_stateTransition_ok {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : BlockChain} {version : Nat}
    {params : Lean.Json} {checked : CheckedBlock version} {parent : RecentBlock}
    {post : Execution.State.State}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (hParent : chain.recent.getLast? = some parent)
    (hHash : parent.header.hash = .ok checked.block.header.parentHash)
    (hTerminal : passesTerminalCheck transition totalDifficulty parent = true)
    (hRun : stateTransition chain checked.block false = .ok post) :
    newPayloadOnChain transition totalDifficulty chain version params =
      .ok (⟨.valid, checked.block.header.hash.toOption⟩, none,
        some (⟨checked.fork, checked.block.header, []⟩, post)) := by
  simp [newPayloadOnChain, hCheck, hParent, hHash, hTerminal, hRun, bind, Except.bind, pure,
    Except.pure, Except.toOption]

/-- A payload that passes the checks on its parent is invalid when its block fails the transition.

Its parent passes the terminal block check.

The failure is not an abort, and the reason of the status carries its error.

Its latest valid hash is its parent's hash, or zero for a parent before Paris. -/
theorem newPayloadOnChain_of_stateTransition_error {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : BlockChain} {version : Nat}
    {params : Lean.Json} {checked : CheckedBlock version} {parent : RecentBlock}
    {e : Execution.Blocks.BlockError}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (hParent : chain.recent.getLast? = some parent)
    (hHash : parent.header.hash = .ok checked.block.header.parentHash)
    (hTerminal : passesTerminalCheck transition totalDifficulty parent = true)
    (hRun : stateTransition chain checked.block false = .error e)
    (hAbort : ∀ cause, e ≠ .aborted cause) :
    newPayloadOnChain transition totalDifficulty chain version params =
      .ok (⟨.invalid, some (if parent.fork < .paris then 0 else checked.block.header.parentHash)⟩,
        some (.invalidBlock e), none) := by
  cases e with
  | aborted cause => exact absurd rfl (hAbort cause)
  | _ =>
    simp [newPayloadOnChain, hCheck, hParent, hHash, hTerminal, hRun, bind, Except.bind, pure,
      Except.pure, Except.toOption]

/-- No payload is valid at version 6 yet: the block of a Bogota payload does not run here.

Its state transition stops at Hegotá, so its answer is never valid, on any chain. -/
theorem newPayloadOnChain_six_ne_valid {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : BlockChain} {params : Lean.Json}
    {answer : PayloadStatus × Option PayloadError × Option (RecentBlock × Execution.State.State)}
    (h : newPayloadOnChain transition totalDifficulty chain 6 params = .ok answer) :
    answer.1.status ≠ .valid := by
  intro valid
  obtain ⟨status, reason, next⟩ := answer
  -- A valid answer comes from a block that passed the transition.
  obtain ⟨block, post, rfl⟩ := (valid_iff_of_newPayloadOnChain h).mp valid
  obtain ⟨-, checked, -, hRun, -⟩ := of_newPayloadOnChain_some h
  -- Version 6 takes Hegotá alone, where the transition stops.
  have hegota : checked.fork = .hegota := (acceptsFork_six_iff _).mp checked.accepted
  rw [Execution.Blocks.stateTransition_of_hegota_le (by rw [hegota]; decide)] at hRun
  cases hRun

/-! ## The writer of the parameters -/

open EthLib.Serialization.JsonRpc (listJson dataJson array fixed bytes array_listJson
  fixed_dataJson bytes_hexString) in
/-- The hashes, the root and the requests read back from their JSON. -/
private theorem params_read_back (hashes : List Hash32) (beaconRoot : Hash32)
    (requests : List ByteArray) :
    array "expectedBlobVersionedHashes" (fun j => fixed "versioned hash" 32 j)
        (listJson (dataJson ·.toList) hashes) = .ok hashes ∧
      fixed "parentBeaconBlockRoot" 32 (dataJson beaconRoot.toList) = .ok beaconRoot ∧
      array "executionRequests" (bytes "request")
        (listJson (dataJson ·.data.toList) requests) = .ok requests := by
  refine ⟨?_, fixed_dataJson _ beaconRoot false, ?_⟩
  · rw [array_listJson]
    simpa using mapM_eq_ok_map (g := id) fun x _ => fixed_dataJson "versioned hash" x false
  · rw [array_listJson]
    refine (mapM_eq_ok_map (g := id) fun r _ => ?_).trans (by simp)
    rw [dataJson, bytes_hexString]
    exact congrArg Except.ok (ByteArray.ext (Array.toList_inj.mp (by simp)))

open EthLib.Serialization.JsonRpc (listJson dataJson array fixed bytes array_listJson
  fixed_dataJson bytes_hexString) in
/-- The decoder reads back an array of a decodable payload, then the values of the version. -/
private theorem newPayloadParams_arr {version : Nat} {pj : Lean.Json} {any : Json.AnyPayload}
    {amsterdam : Option (ByteArray × UInt64)} (hv : 1 ≤ version ∧ version ≤ 5)
    (hnull : pj.isNull = false) (hp : payloadParam version pj = .ok (any, amsterdam))
    (hashes : List Hash32) (beaconRoot : Hash32) (requests : List ByteArray) :
    newPayloadParams version (.arr ([pj] ++
      (if 3 ≤ version then [listJson (dataJson ·.toList) hashes, dataJson beaconRoot.toList]
        else []) ++
      (if 4 ≤ version then [listJson (dataJson ·.data.toList) requests] else [])).toArray) =
      .ok (any, amsterdam, if 3 ≤ version then some hashes else none,
        if 3 ≤ version then some beaconRoot else none,
        if 4 ≤ version then some requests else none) := by
  -- Each value after the payload reads back, and none of them is null.
  obtain ⟨hh, hb, hr⟩ := params_read_back hashes beaconRoot requests
  have nh : (listJson (dataJson ·.toList) hashes).isNull = false := Base.Toolchain.Json.isNull_arr _
  have nr : (listJson (dataJson ·.data.toList) requests).isNull = false :=
    Base.Toolchain.Json.isNull_arr _
  have nb : (dataJson beaconRoot.toList).isNull = false := Base.Toolchain.Json.isNull_str _
  obtain rfl | rfl | rfl | rfl | rfl :
      version = 1 ∨ version = 2 ∨ version = 3 ∨ version = 4 ∨ version = 5 := by omega
  -- What is left binds values that already read back.
  all_goals
    simp [newPayloadParams, paramCount, hnull, hp, hh, hr, hb, nh, nr, nb]
    rfl

/-- A decoded payload that gives a payload at a fork has the structure version of that fork.

It is version 3 from Dencun, version 2 at Shapella, and version 1 before. -/
private theorem version_of_atFork {fork : Fork} {j : Lean.Json} {any : Json.AnyPayload}
    {p : ExecutionPayload fork} (hj : Json.anyPayload j = .ok any)
    (hat : any.atFork fork = .ok p) :
    any.version = if .dencun ≤ fork then 3 else if .shapella ≤ fork then 2 else 1 := by
  obtain ⟨hver, hw, hb, -⟩ := Json.shape_of_anyPayload hj
  simp only [Json.AnyPayload.atFork, bind_ok_iff] at hat
  obtain ⟨w, hw', b, hb', -⟩ := hat
  -- The fields present fix the version of the structure from the fork.
  have hw'' := Json.exists_since_iff.mp ⟨w, hw'⟩
  have hb'' := Json.exists_since_iff.mp ⟨b, hb'⟩
  rw [hw] at hw''
  rw [hb] at hb''
  rcases hver with h | h | h <;> rw [h] at hw'' hb'' ⊢ <;> cases fork <;>
    revert hw'' hb'' <;> decide

/-- The decoder of the parameters reads back their JSON when the version takes the structure.

The version must be one of 1 to 5.

Below version 5 it must take the structure version of the fork of the payload.

From version 5 that fork must be from Dencun on.

The extra data of the payload must hold at most 32 bytes.

The access list and the slot are given exactly from version 5.

The hashes and the root read back from version 3, and the requests from version 4.

The payload reads back as one whose form at its fork is the given payload. -/
theorem newPayloadParams_json_of_structure {fork : Fork} {version : Nat}
    (payload : ExecutionPayload fork) (amsterdam : Option (ByteArray × UInt64))
    (hashes : List Hash32) (beaconRoot : Hash32) (requests : List ByteArray)
    (hv : 1 ≤ version ∧ version ≤ 5)
    (layout : version < 5 → acceptsStructure version
      (if .dencun ≤ fork then 3 else if .shapella ≤ fork then 2 else 1) = true)
    (dencun : 5 ≤ version → .dencun ≤ fork)
    (extra : payload.extraData.size ≤ MAX_EXTRA_DATA_BYTES)
    (five : amsterdam.isSome ↔ 5 ≤ version) :
    ∃ any, newPayloadParams version
        (newPayloadParamsJson version payload amsterdam hashes beaconRoot requests) =
        .ok (any, amsterdam, if 3 ≤ version then some hashes else none,
          if 3 ≤ version then some beaconRoot else none,
          if 4 ≤ version then some requests else none) ∧
      any.atFork fork = .ok payload := by
  unfold newPayloadParamsJson
  cases amsterdam with
  | none =>
    -- Below version 5 the payload has the structure of its fork.
    have hlt : version < 5 := by simpa using five
    obtain ⟨any, hj, hat⟩ := Json.anyPayload_executionPayloadJson payload extra
    have hs : acceptsStructure version any.version = true := by
      rw [version_of_atFork hj hat]
      exact layout hlt
    have hp : payloadParam version (Json.executionPayloadJson payload) = .ok (any, none) :=
      (payloadParam_eq_ok_iff_of_lt hlt).mpr ⟨hj, hs, rfl⟩
    exact ⟨any,
      newPayloadParams_arr hv (Base.Toolchain.Json.isNull_mkObj _) hp hashes beaconRoot requests,
      hat⟩
  | some x =>
    -- Version 5 reads the structure of version 4, from Dencun on.
    obtain ⟨accessList, slot⟩ := x
    have h5 : 5 ≤ version := five.mp rfl
    obtain ⟨any, hj, hat⟩ :=
      Json.payloadV4_executionPayloadV4Json payload accessList slot (dencun h5) extra
    have hp : payloadParam version (Json.executionPayloadV4Json payload accessList slot) =
        .ok (any, some (accessList, slot)) :=
      (payloadParam_eq_ok_iff_of_le h5).mpr ⟨accessList, slot, hj, rfl⟩
    exact ⟨any,
      newPayloadParams_arr hv (Base.Toolchain.Json.isNull_mkObj _) hp hashes beaconRoot requests,
      hat⟩

/-- The decoder of the parameters reads back the JSON of the parameters of a version.

The version must take the fork of the payload, whose extra data holds at most 32 bytes.

It must come before version 6, whose parameters have their own writer.

The access list and the slot are given exactly from version 5.

The hashes and the root read back from version 3, and the requests from version 4.

The payload reads back as one whose form at its fork is the given payload. -/
theorem newPayloadParams_json {fork : Fork} {version : Nat} (payload : ExecutionPayload fork)
    (amsterdam : Option (ByteArray × UInt64)) (hashes : List Hash32) (beaconRoot : Hash32)
    (requests : List ByteArray) (accepts : acceptsFork version fork = true)
    (below : version < 6) (extra : payload.extraData.size ≤ MAX_EXTRA_DATA_BYTES)
    (five : amsterdam.isSome ↔ 5 ≤ version) :
    ∃ any, newPayloadParams version
        (newPayloadParamsJson version payload amsterdam hashes beaconRoot requests) =
        .ok (any, amsterdam, if 3 ≤ version then some hashes else none,
          if 3 ≤ version then some beaconRoot else none,
          if 4 ≤ version then some requests else none) ∧
      any.atFork fork = .ok payload := by
  -- A version that takes a fork is one of 1 to 5.
  have hv : 1 ≤ version ∧ version ≤ 5 := by
    unfold acceptsFork at accepts
    split at accepts <;> first | omega | simp at accepts
  -- The fork fixes the structure that the version takes, and version 5 takes Glamsterdam alone.
  refine newPayloadParams_json_of_structure payload amsterdam hashes beaconRoot requests hv
    (fun h => ?_) (fun h => ?_) extra five
  all_goals
    revert h
    obtain rfl | rfl | rfl | rfl | rfl :
        version = 1 ∨ version = 2 ∨ version = 3 ∨ version = 4 ∨ version = 5 := by omega
    all_goals (cases fork <;> revert accepts <;> decide)

open EthLib.Serialization.JsonRpc (listJson dataJson) in
/-- The decoder of version 6 reads back the JSON of its parameters, from Dencun on.

The writer gives the payload the structure of version 4, with its access list and its slot.

Its extra data must hold at most 32 bytes.

The first four values read back as those of version 5, and the fifth as the inclusion list.

The payload reads back as one whose form at its fork is the given payload. -/
theorem newPayloadV6Params_json {fork : Fork} (payload : ExecutionPayload fork)
    (amsterdam : ByteArray × UInt64) (hashes : List Hash32) (beaconRoot : Hash32)
    (requests : List ByteArray) (inclusionList : List ByteArray) (dencun : .dencun ≤ fork)
    (extra : payload.extraData.size ≤ MAX_EXTRA_DATA_BYTES) :
    ∃ any, newPayloadV6Params
        (newPayloadV6ParamsJson payload amsterdam hashes beaconRoot requests inclusionList) =
        .ok ((any, some amsterdam, some hashes, some beaconRoot, some requests), inclusionList) ∧
      any.atFork fork = .ok payload := by
  -- The payload has the structure of version 4, with its access list and its slot.
  obtain ⟨accessList, slot⟩ := amsterdam
  obtain ⟨any, hj, hat⟩ :=
    Json.payloadV4_executionPayloadV4Json payload accessList slot dencun extra
  have hp : payloadParam 6 (Json.executionPayloadV4Json payload accessList slot) =
      .ok (any, some (accessList, slot)) :=
    (payloadParam_eq_ok_iff_of_le (by decide)).mpr ⟨accessList, slot, hj, rfl⟩
  refine ⟨any, ?_, hat⟩
  -- Each later value reads back, and none of the five is null.
  obtain ⟨hh, hb, hr⟩ := params_read_back hashes beaconRoot requests
  have np : (Json.executionPayloadV4Json payload accessList slot).isNull = false :=
    Base.Toolchain.Json.isNull_mkObj _
  have nh : (listJson (dataJson ·.toList) hashes).isNull = false := Base.Toolchain.Json.isNull_arr _
  have nr : (listJson (dataJson ·.data.toList) requests).isNull = false :=
    Base.Toolchain.Json.isNull_arr _
  have nb : (dataJson beaconRoot.toList).isNull = false := Base.Toolchain.Json.isNull_str _
  have nl : (Json.inclusionListJson inclusionList).isNull = false :=
    Base.Toolchain.Json.isNull_arr _
  simp [newPayloadV6Params, newPayloadV6ParamsJson, newPayloadParamsJson, newPayloadParams,
    paramCount, hp, hh, hr, hb, np, nh, nr, nb, nl, Json.inclusionListOfJson_json]
  rfl

/-- Decoded parameters whose first value is a payload decode that payload. -/
private theorem payloadParam_of_newPayloadParams {version : Nat} {pj : Lean.Json}
    {rest : List Lean.Json}
    {x : Json.AnyPayload × Option (ByteArray × UInt64) × Option (List Hash32) × Option Hash32 ×
      Option (List ByteArray)}
    (h : newPayloadParams version (.arr (pj :: rest).toArray) = .ok x) :
    ∃ a, payloadParam version pj = .ok a := by
  unfold newPayloadParams at h
  obtain ⟨l, hl, h⟩ := bind_ok_iff.mp h
  cases hl
  dsimp only [List.getElem?_cons_zero] at h
  -- Walk every step: a failing step contradicts the result, and each value read is kept.
  repeat' (first
    | (cases h; done)
    | (obtain ⟨_, step, h⟩ := bind_ok_iff.mp h
       first | cases step | skip)
    | split at h)
  all_goals exact ⟨_, ‹payloadParam _ _ = _›⟩

/-- Decoded parameters written from a payload hold its extra data within 32 bytes.

The structure of version 4 must come exactly from version 5, and only from Dencun on. -/
theorem extraData_le_of_newPayloadParams_json {fork : Fork} {version : Nat}
    {payload : ExecutionPayload fork} {amsterdam : Option (ByteArray × UInt64)}
    {hashes : List Hash32} {beaconRoot : Hash32} {requests : List ByteArray}
    (five : amsterdam.isSome ↔ 5 ≤ version) (dencun : amsterdam.isSome → .dencun ≤ fork)
    {x : Json.AnyPayload × Option (ByteArray × UInt64) × Option (List Hash32) × Option Hash32 ×
      Option (List ByteArray)}
    (h : newPayloadParams version
      (newPayloadParamsJson version payload amsterdam hashes beaconRoot requests) = .ok x) :
    payload.extraData.size ≤ MAX_EXTRA_DATA_BYTES := by
  unfold newPayloadParamsJson at h
  obtain ⟨a, ha⟩ := payloadParam_of_newPayloadParams h
  cases amsterdam with
  | none =>
    -- Below version 5 the payload decodes as a structure of version 1, 2 or 3.
    have hlt : version < 5 := by simpa using five
    exact Json.extraData_le_of_anyPayload_executionPayloadJson
      ((payloadParam_eq_ok_iff_of_lt hlt).mp ha).1
  | some x =>
    -- From version 5 it decodes as a payload of version 4.
    obtain ⟨_, _, hj, -⟩ := (payloadParam_eq_ok_iff_of_le (five.mp rfl)).mp ha
    exact Json.extraData_le_of_payloadV4_executionPayloadV4Json (dencun rfl) hj

/-! ## The checks on decoded parameters -/

/-- A payload at a fork keeps the number, the timestamp and the extra data of its structure. -/
theorem Json.AnyPayload.atFork_common {any : Json.AnyPayload} {f : Fork}
    {q : ExecutionPayload f} (h : any.atFork f = .ok q) :
    q.blockNumber = any.common.blockNumber ∧ q.timestamp = any.common.timestamp ∧
      q.extraData = any.common.extraData := by
  simp only [Json.AnyPayload.atFork, bind_ok_iff] at h
  obtain ⟨_, _, _, _, _, _, result⟩ := h
  cases result
  exact ⟨rfl, rfl, rfl⟩

/-- Decoded parameters whose payload has a block at the active fork pass the checks.

The request lists must pass their check, and the version must take the fork.

The block comes from the payload at that fork, with the decoded root, requests, list and slot.

Its blob transactions must carry the decoded versioned hashes, when they are given. -/
theorem checkNewPayload_eq_ok {config : ChainConfig} {version : Nat}
    {params : Lean.Json} {any : Json.AnyPayload} {amsterdam : Option (ByteArray × UInt64)}
    {hashes : Option (List Hash32)} {beaconRoot : Option Hash32}
    {requests : Option (List ByteArray)}
    (hDecode : newPayloadParams version params =
      .ok (any, amsterdam, hashes, beaconRoot, requests))
    (hValid : ∀ rs, requests = some rs → validRequests rs = true) {f : Fork}
    (hActive : config.activeFork any.common.blockNumber.toNat any.common.timestamp.toNat = some f)
    (hAccepted : acceptsFork version f = true) {payload : ExecutionPayload f}
    {beacon : Since .dencun f Hash32} {lists : Since .pectra f (List ByteArray)}
    {accessList : Since .glamsterdam f ByteArray} {slot : Since .glamsterdam f UInt64}
    (hPayload : any.atFork f = .ok payload)
    (hBeacon : Json.since "parentBeaconBlockRoot" beaconRoot = .ok beacon)
    (hLists : Json.since "executionRequests" requests = .ok lists)
    (hAccess : Json.since "blockAccessList" (amsterdam.map (·.1)) = .ok accessList)
    (hSlot : Json.since "slotNumber" (amsterdam.map (·.2)) = .ok slot)
    {b : Execution.Blocks.Block f Execution.Transactions.Transaction}
    (hBlock : payload.toBlock beacon lists accessList slot = .ok b)
    (hHashes : ∀ hs, hashes = some hs →
      ExecutionPayload.blobVersionedHashes b.transactions = hs) :
    checkNewPayload config version params = .ok (.ok ⟨f, hAccepted, b⟩) := by
  unfold checkNewPayload
  rw [hDecode]
  dsimp only
  cases requests <;> cases hashes <;>
    simp [hValid, hActive, hAccepted, hPayload, hBeacon, hLists, hAccess, hSlot, hBlock,
      hHashes, bind, Except.bind, pure, Except.pure]

end EthLib.Engine
