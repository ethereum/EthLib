module

public import EthLib.Engine.NewPayload
public import EthLib.Engine.Proofs.Block

/-!
# Proofs: the checks of `engine_newPayload`

Each fork from Paris to BPO5 has a version of the method, and no other fork has one.

Request lists that pass the checks have distinct types, in increasing order.

The checks pass only for an array of the parameters of the version, none of them null.

If the last block of a chain is not the parent, a payload that passes the checks is syncing.

If it is the parent, a payload whose block passes the state transition is valid.

A block that fails it without an abort makes the payload invalid, with the block error.

A block and a state come back only for a valid payload.
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

/-- Some version of the method takes a fork exactly when the fork is from Paris to BPO5. -/
theorem exists_acceptsFork_iff (fork : Fork) :
    (∃ version, acceptsFork version fork = true) ↔ .paris ≤ fork ∧ fork < .glamsterdam := by
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

/-- Request lists that pass the check have strictly increasing types. -/
theorem pairwise_of_validRequests {requests : List ByteArray}
    (h : validRequests requests = true) :
    requests.Pairwise fun r s => ∃ a b, r[0]? = some a ∧ s[0]? = some b ∧ a < b := by
  induction requests with
  | nil => exact .nil
  | cons r rest ih =>
    match rest, h with
    | [], _ => exact List.pairwise_singleton _ r
    | s :: rest', h =>
      simp only [validRequests] at h
      split at h
      · rename_i a b hra hsb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨-, -⟩, hab⟩, hRest⟩ := h
        have hTail := ih hRest
        refine List.Pairwise.cons (fun t ht => ?_) hTail
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨a, b, hra, hsb, hab⟩
        · obtain ⟨b', c, hb', hc, hbc⟩ := List.rel_of_pairwise_cons hTail ht
          rw [hsb] at hb'
          cases hb'
          exact ⟨a, c, hra, hc, UInt8.lt_trans hab hbc⟩
      · exact absurd h (by simp)

/-- Request lists that pass the check have distinct types. -/
theorem nodup_types_of_validRequests {requests : List ByteArray}
    (h : validRequests requests = true) : (requests.map fun r => r[0]?).Nodup :=
  List.Pairwise.map _ (fun _ _ ⟨a, b, ha, hb, hlt⟩ => by
    rw [ha, hb]; exact fun e => UInt8.ne_of_lt hlt (Option.some.inj e))
    (pairwise_of_validRequests h)

/-! ## The parameters of the checks -/

/-- The checks pass only for an array with the parameters of the version, none of them null. -/
theorem params_of_checkNewPayload_ok {config : ChainConfig} {version : Nat} {params : Lean.Json}
    {r : Except (PayloadStatus × PayloadError) (CheckedBlock version)}
    (h : checkNewPayload config version params = .ok r) :
    ∃ items : Array Lean.Json, params = .arr items ∧ items.size = paramCount version ∧
      ∀ j ∈ items, j.isNull = false := by
  unfold checkNewPayload at h
  cases params with
  | arr items' =>
    refine ⟨items', rfl, ?_⟩
    by_cases hc : (items'.toList.length == paramCount version) = true ∧
        (items'.toList.all fun x => !x.isNull) = true
    · simp only [List.all_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      exact ⟨by simpa using hc.1, fun j hj => hc.2 j (by simpa using hj)⟩
    · exfalso
      simp (config := {maxSteps := 2000000}) only [hc, pure, Except.pure, ite_false,
        reduceCtorEq, Json.invalid, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | _ =>
    exfalso
    simp (config := {maxSteps := 2000000}) only [reduceCtorEq, Json.invalid, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw] at h

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
