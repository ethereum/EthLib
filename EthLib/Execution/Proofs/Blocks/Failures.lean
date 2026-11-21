module

public import EthLib.Execution.Proofs.Blocks.SystemCall
public import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: the errors with which a block fails

A result meets a property on its errors when each error that it fails with has the property.

A sequence, a map and a change of error keep that, so a proof follows the steps of a definition.

The body of a block meets a property when each of its leaves does, on states that keep invariants.

The checks of a block before its body fail with no abort and no error of the state.

Nor do they fail for a system call or for a transaction kept out of the block.

Nor do the recent hashes, the roots and the checks of its output.

So the transition of a block fails only with errors of a property when its body does.

The property must also hold for the other errors of the block, and for the abort from Hegotá on.

A failed system call can be left out of the property as well, since the checks never give one.

So can a transaction kept out of the block, for the same reason.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions (Transaction checkInclusion processTransaction)

variable {fork : Fork}

/-! ## Results whose errors meet a property -/

/-- Whether every failure of a result meets a property. -/
def ErrorsMeet {α : Type} (P : BlockError → Prop) (r : Except BlockError α) : Prop :=
  ∀ e, r = .error e → P e

/-- A success has no failure. -/
theorem ErrorsMeet.ok {α : Type} {P : BlockError → Prop} (a : α) :
    ErrorsMeet P (.ok a : Except BlockError α) :=
  fun _ h => by cases h

/-- A pure result has no failure. -/
theorem ErrorsMeet.pure {α : Type} {P : BlockError → Prop} (a : α) :
    ErrorsMeet P (Pure.pure a : Except BlockError α) :=
  fun _ h => by cases h

/-- A failure with an error that meets the property meets it. -/
theorem ErrorsMeet.error {α : Type} {P : BlockError → Prop} {e : BlockError} (h : P e) :
    ErrorsMeet P (.error e : Except BlockError α) :=
  fun _ he => by cases he; exact h

/-- A throw of an error that meets the property meets it. -/
theorem ErrorsMeet.throw {α : Type} {P : BlockError → Prop} {e : BlockError} (h : P e) :
    ErrorsMeet P (MonadExcept.throw e : Except BlockError α) :=
  fun _ he => by cases he; exact h

/-- A sequence meets the property when its first part does, and its rest after it. -/
theorem ErrorsMeet.bind {α β : Type} {P : BlockError → Prop} {x : Except BlockError α}
    {f : α → Except BlockError β} (hx : ErrorsMeet P x)
    (hf : ∀ a, x = .ok a → ErrorsMeet P (f a)) : ErrorsMeet P (x >>= f) := by
  intro e h
  rcases Base.bind_eq_error h with h | ⟨a, ha, h⟩
  · exact hx e h
  · exact hf a ha e h

/-- A map of a result that meets the property meets it. -/
theorem ErrorsMeet.map {α β : Type} {P : BlockError → Prop} {x : Except BlockError α}
    (f : α → β) (hx : ErrorsMeet P x) : ErrorsMeet P (f <$> x) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; cases h; exact hx e hx'
  | ok a => rw [hx'] at h; cases h

/-- A change of error meets the property when each changed failure does. -/
theorem ErrorsMeet.mapError {ε α : Type} {P : BlockError → Prop} {x : Except ε α}
    {f : ε → BlockError} (hf : ∀ e, x = .error e → P (f e)) : ErrorsMeet P (x.mapError f) := by
  intro e h
  cases hx : x with
  | error e' => rw [hx] at h; cases h; exact hf e' hx
  | ok a => rw [hx] at h; cases h

/-- An abort meets the property when each of its errors does, as an abort. -/
theorem ErrorsMeet.aborted {α : Type} {P : BlockError → Prop} {x : Except EvmError α}
    (h : ∀ e, x = .error e → P (.aborted e)) : ErrorsMeet P (x.mapError .aborted) :=
  ErrorsMeet.mapError h

/-- A step on a block state meets the property when each of its errors does, as a state error. -/
theorem ErrorsMeet.onBlock {P : BlockError → Prop} {block : BlockState}
    {step : TransactionState → Except State.StateError TransactionState}
    (h : ∀ e, step (.ofBlock block) = .error e → P (.state e)) :
    ErrorsMeet P (onBlock block step) :=
  ErrorsMeet.bind (ErrorsMeet.mapError h) fun _ _ => ErrorsMeet.pure _

/-- The first failure of a list of checks is one of their errors. -/
theorem errorsMeet_firstFailure {P : BlockError → Prop} :
    ∀ (l : List (Bool × BlockError)), (∀ x ∈ l, P x.2) → ErrorsMeet P (firstFailure l)
  | [], _ => ErrorsMeet.ok _
  | (b, e) :: rest, h => by
    unfold firstFailure
    split
    · exact errorsMeet_firstFailure rest fun x hx => h x (List.mem_cons_of_mem _ hx)
    · exact ErrorsMeet.error (h (b, e) List.mem_cons_self)

/-! ## The checks of a block -/

/-- Whether an error of a block is no abort, no state error and no failed system call.

Nor is it a transaction kept out of the block. -/
private def Plain (e : BlockError) : Prop :=
  (∀ error, e ≠ .aborted error) ∧ (∀ error, e ≠ .state error) ∧
    (∀ address error, e ≠ .systemCallFailed address error) ∧
    ∀ index error, e ≠ .invalidTransaction index error

/-- The checks of a header against its parent fail with no abort, state error or failed call.

Nor do they keep a transaction out. -/
private theorem plain_headerChecks {parentFork : Fork} (hFork : parentFork ≤ fork)
    (parent : Header parentFork) (header : Header fork)
    (schedule : Since .dencun fork BlobSchedule) :
    ∀ x ∈ headerChecks hFork parent header schedule, Plain x.2 := by
  unfold headerChecks
  dsimp only
  simp only [List.forall_mem_append, List.forall_mem_cons]
  and_intros
  all_goals repeat' split
  all_goals simp [Plain]

/-- A check of a header against its parent fails with no abort, state error or failed call.

Nor does it keep a transaction out. -/
private theorem plain_validateHeader {parentFork : Fork} (hFork : parentFork ≤ fork)
    (parent : Header parentFork) (header : Header fork)
    (schedule : Since .dencun fork BlobSchedule) :
    ErrorsMeet Plain (validateHeader hFork parent header schedule) := by
  unfold validateHeader
  refine ErrorsMeet.bind
    (errorsMeet_firstFailure _ (plain_headerChecks hFork parent header schedule)) fun _ _ => ?_
  split
  · exact ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩
  · exact ErrorsMeet.pure _

/-- The checks of a block before its body fail with no abort, state error or failed call.

Nor do they keep a transaction out. -/
private theorem plain_checkBlock {config : ChainConfig} {checkSeal : Bool}
    {recent : List RecentBlock} {block : Block fork Transaction} :
    ErrorsMeet Plain (checkBlock config checkSeal recent block) := by
  unfold checkBlock
  refine ErrorsMeet.bind ?_ fun items _ => ?_
  · unfold bodyItems
    exact ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩)
      fun _ _ => ErrorsMeet.pure _
  refine ErrorsMeet.bind ?_ fun _ _ => ?_
  · unfold validateBlockSize
    split
    · refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩)
        fun _ _ => errorsMeet_firstFailure _ ?_
      simp [Plain]
    · exact ErrorsMeet.ok _
  have ommers : ErrorsMeet Plain (if fork < .paris then
      (validateOmmers config checkSeal recent block.header block.ommers).mapError .ommers
    else if block.ommers.isEmpty = true then pure ()
    else throw (.ommersAfterParis block.ommers.length)) := by
    split
    · exact ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩
    · split
      · exact ErrorsMeet.pure _
      · exact ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩
  split
  · dsimp only
    split
    · split
      · refine ErrorsMeet.bind (plain_validateHeader _ _ _ _) fun _ _ => ?_
        split
        · exact ommers
        · exact ErrorsMeet.bind (ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩)
            fun _ _ => ommers
      · refine ErrorsMeet.bind (errorsMeet_firstFailure _ (plain_headerChecks _ _ _ _))
          fun _ _ => ?_
        split
        · exact ommers
        · exact ErrorsMeet.bind (ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩)
            fun _ _ => ommers
    · refine ErrorsMeet.bind (ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩) fun _ _ => ?_
      split
      · exact ommers
      · exact ErrorsMeet.bind (ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩)
          fun _ _ => ommers
  · exact ErrorsMeet.throw ⟨nofun, nofun, nofun, nofun⟩

/-- The checks of a block before its body never fail with an abort or an error of the state. -/
theorem checkBlock_eq_error {config : ChainConfig} {checkSeal : Bool} {recent : List RecentBlock}
    {block : Block fork Transaction} {e : BlockError}
    (h : checkBlock config checkSeal recent block = .error e) :
    (∀ error, e ≠ .aborted error) ∧ ∀ error, e ≠ .state error :=
  ⟨(plain_checkBlock e h).1, (plain_checkBlock e h).2.1⟩

/-! ## The body of a block -/

/-- The facts at the leaves of the body of a block that keep its errors in a property.

A first invariant holds on the block state before the withdrawals, and a second one after them.

A third one holds on the state that each call, transaction and withdrawal ends on.

Its join to the body then fails in the property.

Each step keeps its invariant, and the withdrawals pass from the first to the second.

An invariant that always holds needs no proof that the steps keep it. -/
structure BodyLeaves (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (P : BlockError → Prop) (Inv Inv' : BlockState → Prop)
    (Out : TransactionState → Prop) : Prop where
  /-- An error that is no abort, state error, failed call or excluded transaction meets it. -/
  plain : ∀ e, (∀ x, e ≠ .aborted x) → (∀ x, e ≠ .state x) →
    (∀ a x, e ≠ .systemCallFailed a x) → (∀ i x, e ≠ .invalidTransaction i x) → P e
  /-- The DAO transfer fails in the property. -/
  dao : ∀ s, Inv s → ∀ e, applyDaoFork fork (.ofBlock s) = .error e → P (.state e)
  /-- The DAO transfer keeps the first invariant. -/
  dao_inv : ∀ s s', Inv s → daoTransfer config fork block.header.number s = .ok s' → Inv s' := by
    intros; trivial
  /-- The system calls at the start fail in the property. -/
  start : ∀ b : BodyState, Inv b.block →
    ∀ e, startSystemCalls env block.header.parentHash b = .error e → P (.aborted e)
  /-- The system calls at the start keep the first invariant. -/
  start_inv : ∀ b b' : BodyState, Inv b.block →
    startSystemCalls env block.header.parentHash b = .ok b' → Inv b'.block := by
    intros; trivial
  /-- The inclusion check of a transaction fails in the property. -/
  inclusion : ∀ (before : BodyOutput fork) index tx, Inv before.block → ∀ e,
    checkInclusion env.chainId env before.gas (.ofBlock before.block) tx = .error e →
      P (.invalidTransaction index e)
  /-- A transaction that passes its inclusion check aborts in the property. -/
  process : ∀ (before : BodyOutput fork) tx included, Inv before.block →
    checkInclusion env.chainId env before.gas (.ofBlock before.block) tx = .ok included →
      ∀ e, processTransaction env before.block included tx = .error e → P (.aborted e)
  /-- A transaction that passes its inclusion check ends on a state of the third invariant. -/
  process_out : ∀ (before : BodyOutput fork) tx included out, Inv before.block →
    checkInclusion env.chainId env before.gas (.ofBlock before.block) tx = .ok included →
      processTransaction env before.block included tx = .ok out → Out out.state := by
    intros; trivial
  /-- A transaction keeps the first invariant. -/
  transaction_inv : ∀ (before after : BodyOutput fork) index tx, Inv before.block →
    applyTransaction env index before tx = .ok after → Inv after.block := by
    intros; trivial
  /-- The join of a state of the third invariant to the body fails in the property. -/
  join : ∀ (b : BodyState) tx, Out tx → ∀ e, b.join tx = .error e → P (.state e)
  /-- The withdrawals fail in the property. -/
  withdraw : ∀ (h : .shapella ≤ fork) s, Inv s →
    ∀ e, withdrawalState fork s (block.withdrawals h) = .error e → P (.state e)
  /-- The withdrawals end on a state of the third invariant. -/
  withdraw_out : ∀ (h : .shapella ≤ fork) s tx, Inv s →
    withdrawalState fork s (block.withdrawals h) = .ok tx → Out tx := by
    intros; trivial
  /-- The withdrawals, once they join the body, pass from the first invariant to the second. -/
  withdraw_inv : ∀ (h : .shapella ≤ fork) (b b' : BodyState) tx, Inv b.block →
    withdrawalState fork b.block (block.withdrawals h) = .ok tx → b.join tx = .ok b' →
      Inv' b'.block := by
    intros; trivial
  /-- With no withdrawals, the first invariant gives the second. -/
  skip_inv : ¬.shapella ≤ fork → ∀ s, Inv s → Inv' s := by
    intros; trivial
  /-- The read of the code of a request contract aborts in the property. -/
  code : ∀ s target, Inv' s → ∀ e, codeAt s target = .error e → P (.aborted e)
  /-- A call to a request contract aborts in the property. -/
  call : ∀ s target data, Inv' s →
    ∀ e, systemCall env s target data = .error e → P (.aborted e)
  /-- A call to a request contract that stops with an error fails in the property. -/
  call_failed : ∀ s target data out, Inv' s → systemCall env s target data = .ok out →
    ∀ e, out.error = some e → P (.systemCallFailed target e)
  /-- A call to a request contract ends on a state of the third invariant. -/
  call_out : ∀ s target data out, Inv' s → systemCall env s target data = .ok out →
    Out out.state := by
    intros; trivial
  /-- A call to a request contract, once it joins the body, keeps the second invariant. -/
  call_inv : ∀ (b b' : BodyState) target data out, Inv' b.block →
    systemCall env b.block target data = .ok out → b.join out.state = .ok b' → Inv' b'.block := by
    intros; trivial
  /-- The rewards fail in the property. -/
  rewards : ∀ s, Inv' s → ∀ e,
    payRewards fork (.ofBlock s) block.header.coinbase block.header.number
      (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)) = .error e →
      P (.state e)

namespace BodyLeaves

variable {config : ChainConfig} {env : BlockEnvironment fork} {block : Block fork Transaction}
  {P : BlockError → Prop} {Inv Inv' : BlockState → Prop} {Out : TransactionState → Prop}

/-- A step whose errors are no abort, no state error, no failed call and no excluded one. -/
private theorem plain_mapError {ε α : Type} (leaves : BodyLeaves config env block P Inv Inv' Out)
    {x : Except ε α} {f : ε → BlockError} (hf : ∀ e, (∀ y, f e ≠ .aborted y) ∧
      (∀ y, f e ≠ .state y) ∧ (∀ a y, f e ≠ .systemCallFailed a y) ∧
        ∀ i y, f e ≠ .invalidTransaction i y) :
    ErrorsMeet P (x.mapError f) :=
  ErrorsMeet.mapError fun e _ => leaves.plain _ (hf e).1 (hf e).2.1 (hf e).2.2.1 (hf e).2.2.2

/-- A join of a state of the third invariant meets the property. -/
private theorem errorsMeet_join (leaves : BodyLeaves config env block P Inv Inv' Out)
    (b : BodyState) {tx : TransactionState} (out : Out tx) :
    ErrorsMeet P ((b.join tx).mapError .state) :=
  ErrorsMeet.mapError (leaves.join b tx out)

/-- A transaction of the body meets the property. -/
private theorem errorsMeet_applyTransaction (leaves : BodyLeaves config env block P Inv Inv' Out)
    {index : Nat} {before : BodyOutput fork} (tx : Transaction) (inv : Inv before.block) :
    ErrorsMeet P (applyTransaction env index before tx) := by
  unfold applyTransaction
  refine ErrorsMeet.bind (ErrorsMeet.mapError (leaves.inclusion before index tx inv))
    fun included hincl => ?_
  refine ErrorsMeet.bind (ErrorsMeet.aborted
    (leaves.process before tx included inv (mapError_ok_iff.mp hincl))) fun out hout => ?_
  refine ErrorsMeet.bind (leaves.errorsMeet_join _
    (leaves.process_out before tx included out inv (mapError_ok_iff.mp hincl)
      (mapError_ok_iff.mp hout))) fun _ _ => ?_
  dsimp only
  split
  · exact ErrorsMeet.bind (ErrorsMeet.pure _) fun _ _ => ErrorsMeet.pure _
  · exact ErrorsMeet.bind (ErrorsMeet.map _ (leaves.plain_mapError fun _ =>
      ⟨nofun, nofun, nofun, nofun⟩)) fun _ _ => ErrorsMeet.pure _

/-- The transactions of the body meet the property. -/
private theorem errorsMeet_applyTransactions
    (leaves : BodyLeaves config env block P Inv Inv' Out) {body : BodyState}
    (transactions : List Transaction) (inv : Inv body.block) :
    ErrorsMeet P (applyTransactions env body transactions) := fun _ h =>
  foldlM_error_of_step (fun before : BodyOutput fork => Inv before.block) P
    (fun _ _ _ hb hstep => leaves.transaction_inv _ _ _ _ hb hstep)
    (fun _ _ e hb h => leaves.errorsMeet_applyTransaction _ hb e h)
    (b := ⟨body, .zero, 0, [], [], []⟩) inv h

/-- A checked call to a request contract meets the property. -/
private theorem errorsMeet_checkedSystemCall
    (leaves : BodyLeaves config env block P Inv Inv' Out) {s : BlockState} (target : Address)
    (data : ByteArray) (inv : Inv' s) :
    ErrorsMeet P (checkedSystemCall env s target data) := by
  unfold checkedSystemCall
  refine ErrorsMeet.bind (ErrorsMeet.aborted (leaves.code s target inv)) fun _ _ => ?_
  have rest : ErrorsMeet P (do
      let out ← (systemCall env s target data).mapError BlockError.aborted
      match out.error with
      | some error => throw (BlockError.systemCallFailed target error)
      | none => pure out) := by
    refine ErrorsMeet.bind (ErrorsMeet.aborted (leaves.call s target data inv)) fun out hout => ?_
    split
    · rename_i e he
      exact ErrorsMeet.throw
        (leaves.call_failed s target data out inv (mapError_ok_iff.mp hout) e he)
    · exact ErrorsMeet.pure _
  dsimp only
  split
  · exact ErrorsMeet.bind (ErrorsMeet.throw (leaves.plain _ nofun nofun nofun nofun))
      fun _ _ => rest
  · exact rest

/-- A read of a request contract keeps the second invariant. -/
private theorem readRequest_inv (leaves : BodyLeaves config env block P Inv Inv' Out)
    {state state' : BodyState × List ByteArray} {contract : UInt8 × Address}
    (inv : Inv' state.1.block) (h : readRequest env state contract = .ok state') :
    Inv' state'.1.block := by
  obtain ⟨out, hout, hjoin, -⟩ := readRequest_eq_ok h
  exact leaves.call_inv _ _ _ _ out inv (checkedSystemCall_ok hout).2.1 hjoin

/-- A read of a request contract meets the property. -/
private theorem errorsMeet_readRequest (leaves : BodyLeaves config env block P Inv Inv' Out)
    {state : BodyState × List ByteArray} (contract : UInt8 × Address) (inv : Inv' state.1.block) :
    ErrorsMeet P (readRequest env state contract) := by
  unfold readRequest
  refine ErrorsMeet.bind (leaves.errorsMeet_checkedSystemCall _ _ inv) fun out hout => ?_
  exact ErrorsMeet.bind (leaves.errorsMeet_join _
    (leaves.call_out _ _ _ out inv (checkedSystemCall_ok hout).2.1)) fun _ _ => ErrorsMeet.pure _

/-- The reads of the request contracts meet the property, and keep the second invariant. -/
private theorem errorsMeet_readRequests (leaves : BodyLeaves config env block P Inv Inv' Out)
    {body : BodyState} (inv : Inv' body.block) :
    ErrorsMeet P (readRequests env body) ∧
      ∀ result, readRequests env body = .ok result → Inv' result.1.block := by
  unfold readRequests
  split
  · exact ⟨fun _ h => foldlM_error_of_step (fun st : BodyState × List ByteArray => Inv' st.1.block)
      P (fun _ _ _ hb hstep => leaves.readRequest_inv hb hstep)
      (fun _ c e hb h => leaves.errorsMeet_readRequest c hb e h) inv h,
      fun _ h => foldlM_ok_invariant (fun st : BodyState × List ByteArray => Inv' st.1.block)
        (fun _ _ _ hb hstep => leaves.readRequest_inv hb hstep) inv h⟩
  · exact ⟨ErrorsMeet.ok _, fun _ h => by cases h; exact inv⟩

/-- The requests of the body meet the property, and keep the second invariant. -/
private theorem errorsMeet_blockRequests (leaves : BodyLeaves config env block P Inv Inv' Out)
    {depositContract : Address} {body : BodyState} (logs : List Log) (inv : Inv' body.block) :
    ErrorsMeet P (blockRequests depositContract env body logs) ∧
      ∀ result, blockRequests depositContract env body logs = .ok result →
        Inv' result.1.block := by
  have reads := leaves.errorsMeet_readRequests (env := env) inv
  unfold blockRequests
  split
  · refine ⟨ErrorsMeet.bind (leaves.plain_mapError fun _ => ⟨nofun, nofun, nofun, nofun⟩)
      fun _ _ => ErrorsMeet.bind reads.1 fun _ _ => ErrorsMeet.pure _, fun result h => ?_⟩
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨read, hread, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact reads.2 read hread
  · exact ⟨ErrorsMeet.pure _, fun result h => by cases h; exact inv⟩

/-- The hash of the block access list meets the property. -/
private theorem errorsMeet_accessListHashOf (leaves : BodyLeaves config env block P Inv Inv' Out)
    (body : BodyState) (gasLimit : Nat) : ErrorsMeet P (accessListHashOf fork body gasLimit) := by
  unfold accessListHashOf
  split
  · refine ErrorsMeet.bind (leaves.plain_mapError fun _ => ⟨nofun, nofun, nofun, nofun⟩)
      fun _ _ => ?_
    exact ErrorsMeet.map _ (leaves.plain_mapError fun _ => ⟨nofun, nofun, nofun, nofun⟩)
  · exact ErrorsMeet.pure _

/-- The body of a block fails only in the property, from a block state of the first invariant. -/
theorem errorsMeet_applyBody (leaves : BodyLeaves config env block P Inv Inv' Out)
    {start : BlockState} (inv : Inv start) : ErrorsMeet P (applyBody config env block start) := by
  unfold applyBody
  refine ErrorsMeet.bind ?_ fun state hstate => ?_
  · unfold daoTransfer
    split
    · exact ErrorsMeet.onBlock (leaves.dao start inv)
    · exact ErrorsMeet.pure _
  have i1 := leaves.dao_inv _ _ inv hstate
  refine ErrorsMeet.bind (ErrorsMeet.aborted (leaves.start (.init state) i1)) fun body hbody => ?_
  have i2 := leaves.start_inv _ _ i1 (mapError_ok_iff.mp hbody)
  refine ErrorsMeet.bind (leaves.errorsMeet_applyTransactions _ i2) fun output houtput => ?_
  have i3 : Inv output.block := foldlM_ok_invariant (fun before : BodyOutput fork =>
    Inv before.block) (fun _ _ _ hb hstep => leaves.transaction_inv _ _ _ _ hb hstep)
    (b := ⟨body, .zero, 0, [], [], []⟩) i2 houtput
  dsimp only
  have rest : ∀ b : BodyState, Inv' b.block → ErrorsMeet P (do
      let (body, requests) ← blockRequests config.depositContractAddress env b output.logs
      let ommers := block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)
      let state ← onBlock body.block fun tx =>
        payRewards fork tx block.header.coinbase block.header.number ommers
      let accessListHash ← accessListHashOf fork body block.header.gasLimit
      return ({ output with body := { body with block := state }, requests, accessListHash } :
        BlockOutput fork)) := by
    intro b hb
    have requests := leaves.errorsMeet_blockRequests (depositContract :=
      config.depositContractAddress) output.logs hb
    refine ErrorsMeet.bind requests.1 fun r hr => ?_
    have kept := requests.2 r hr
    obtain ⟨requested, requests⟩ := r
    refine ErrorsMeet.bind (ErrorsMeet.onBlock (leaves.rewards _ kept)) fun _ _ => ?_
    exact ErrorsMeet.bind (leaves.errorsMeet_accessListHashOf _ _) fun _ _ => ErrorsMeet.pure _
  split
  · rename_i hS
    refine ErrorsMeet.bind (ErrorsMeet.mapError (leaves.withdraw hS _ i3)) fun tx htx => ?_
    refine ErrorsMeet.bind (leaves.errorsMeet_join _
      (leaves.withdraw_out hS _ _ i3 (mapError_ok_iff.mp htx))) fun b hb => rest b ?_
    exact leaves.withdraw_inv hS (output.body.beginIndex _) _ _ i3 (mapError_ok_iff.mp htx)
      (mapError_ok_iff.mp hb)
  · rename_i hS
    exact ErrorsMeet.bind (ErrorsMeet.pure _) fun b hb => by
      cases hb
      exact rest _ (leaves.skip_inv hS _ i3)

end BodyLeaves

/-! ## The transition -/

/-- The transition of a block fails only with errors of a property when its body does.

The property must hold for every error that is no abort, no state error and no failed system call.

It need not hold for a failed system call or a transaction kept out of the block.

The checks never give one, so only the body must meet it there.

It must hold for the abort from Hegotá on, for a fork whose rules are not yet specified. -/
theorem errorsMeet_stateTransition_of_plain {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {P : BlockError → Prop}
    (plain : ∀ e, (∀ x, e ≠ .aborted x) → (∀ x, e ≠ .state x) →
      (∀ a x, e ≠ .systemCallFailed a x) → (∀ i x, e ≠ .invalidTransaction i x) → P e)
    (hegota : .hegota ≤ fork → P (.aborted (.forkNotYetSpecified fork)))
    (body : ∀ env, ErrorsMeet P (applyBody chain.config env block ⟨chain.state, ∅, ∅, ∅, ∅⟩)) :
    ErrorsMeet P (stateTransition chain block checkSeal) := by
  have other : ∀ {β : Type} {x : Except BlockError β}, ErrorsMeet Plain x → ErrorsMeet P x :=
    fun hx e h => plain e (hx e h).1 (hx e h).2.1 (hx e h).2.2.1 (hx e h).2.2.2
  have trie : ∀ {β : Type} (x : Except Trie.TrieError β), ErrorsMeet P (x.mapError .trie) :=
    fun _ => other (ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩)
  have rest : ErrorsMeet P (do
      checkBlock chain.config checkSeal chain.recent block
      let result ← runBody chain block
      firstFailure (outputChecks block.header result.output result.roots)
      pure result.post : Except BlockError State) := by
    refine ErrorsMeet.bind (other plain_checkBlock) fun _ _ => ?_
    refine ErrorsMeet.bind ?_ fun result _ => ?_
    · unfold runBody
      refine ErrorsMeet.bind ?_ fun hashes _ => ?_
      · unfold recentHashes
        dsimp only
        split
        · exact ErrorsMeet.pure _
        · exact ErrorsMeet.bind
            (other (ErrorsMeet.mapError fun _ _ => ⟨nofun, nofun, nofun, nofun⟩))
            fun _ _ => ErrorsMeet.pure _
      refine ErrorsMeet.bind (body _) fun output _ => ?_
      refine ErrorsMeet.bind ?_ fun _ _ => ErrorsMeet.pure _
      unfold outputRoots
      refine ErrorsMeet.bind (trie _) fun _ _ => ?_
      refine ErrorsMeet.bind (trie _) fun _ _ => ?_
      refine ErrorsMeet.bind (trie _) fun _ _ => ?_
      refine ErrorsMeet.bind ?_ fun _ _ => ErrorsMeet.pure _
      unfold withdrawalsRootOf
      split
      · exact ErrorsMeet.map _ (trie _)
      · exact ErrorsMeet.ok _
    refine ErrorsMeet.bind (other (errorsMeet_firstFailure _ ?_)) fun _ _ => ErrorsMeet.pure _
    unfold outputChecks
    dsimp only
    simp only [List.forall_mem_append, List.forall_mem_cons]
    and_intros
    all_goals repeat' split
    all_goals simp [Plain]
  unfold stateTransition
  dsimp only
  split
  · rename_i hle
    refine ErrorsMeet.bind (ErrorsMeet.throw (hegota hle)) fun _ _ => ?_
    split
    · exact rest
    · exact ErrorsMeet.bind (ErrorsMeet.throw (plain _ nofun nofun nofun nofun))
        fun _ _ => rest
  · split
    · exact rest
    · exact ErrorsMeet.bind (ErrorsMeet.throw (plain _ nofun nofun nofun nofun))
        fun _ _ => rest

/-- The transition of a block fails only with errors of a property when its body does.

The property must hold for every error that is neither an abort nor an error of the state.

It must hold for the abort from Hegotá on, for a fork whose rules are not yet specified. -/
theorem errorsMeet_stateTransition {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {P : BlockError → Prop}
    (plain : ∀ e, (∀ x, e ≠ .aborted x) → (∀ x, e ≠ .state x) → P e)
    (hegota : .hegota ≤ fork → P (.aborted (.forkNotYetSpecified fork)))
    (body : ∀ env, ErrorsMeet P (applyBody chain.config env block ⟨chain.state, ∅, ∅, ∅, ∅⟩)) :
    ErrorsMeet P (stateTransition chain block checkSeal) :=
  errorsMeet_stateTransition_of_plain (fun e ha hs _ _ => plain e ha hs) hegota body

end EthLib.Execution.Blocks
