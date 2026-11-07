module

public import EthLib.Execution.Proofs.Evm.Logic.Slots
public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Evm.Logic.Call

/-!
# Proofs: the effect of a message on storage and balances

A frame that knows a few slots of storage can send a message, and go on knowing them.

The effect of a message names the slots that it may touch, from the frame that sends it.

It also names the addresses whose balances it may move.

Outside those slots and addresses, the frame that ends the message agrees with the frame before it.

So every word reads as before there, and every slot is warm exactly when it was.

The words before the transaction, the codes and the block stay too.

Every account still exists exactly when it did, with its nonce and its code hash.

A message that fails touches no slot and moves no balance.

A message that succeeds also gives the facts of some slots, some balances, and a refund to add.

- A callee whose stopped frame agrees with the state of its caller, outside the change, has one.
- On success that stopped frame must give the facts, the balances and the refund of the effect.
- A failure rolls the state back, so the callee then touches nothing.
- A move of a value that is not 0 between two accounts that exist moves only their balances.
- It needs a sender with a nonce or a code, so that neither account ends empty.
- CALL and CALLCODE with no value, STATICCALL and DELEGATECALL send no value of their own.
- From Berlin to before Glamsterdam, such a call keeps each fact of a slot it does not touch.
- It needs an input range that a fact of memory holds, and an output range within memory.
- It also needs the gas of a call to a cold address.
- On success, the frame then knows the facts that the effect gives, and adds its refund.
- It also knows the bytes that the callee writes into the output range, which its assumption gives.
- On failure, it keeps every fact of a slot and the refund counter.
- Either way, it keeps each fact of memory apart from the output range.
- Either way, its base agrees with the base before the call outside the touched slots and the facts.
- From Berlin to before Glamsterdam, CALL with a value that is not 0 does the same.
- It needs a frame that may change the state, and an account that holds the value in the base.
- It also needs the gas of a cold call, of the value, and of a dead callee.
- On success, its new base also holds the balances that the effect gives.
- Its new base agrees with the old one outside the addresses whose balances the effect moves, too.

A callee may call its caller again, before it ends.

Then the code of the caller runs again, and its own specification says what that run does.

The runner of the interpreter meets the specifications of a family of codes that call each other.

Each specification may assume the specifications of the whole family on the messages it sends.

Each starts from the frame of its message, after the move of the value of the message, if any.

That holds by induction on the bound on the gas of messages, which each message is below.

An effect keeps the codes, the words before the transaction, and which accounts exist.

So it leaves out a callee that creates or deletes an account, or changes a code or a nonce.

The frame after a call says nothing of its return data.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 Address Bytes32 toAddressMasked)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-! ## Families of codes that call each other -/

/-- A runner that meets two assumptions meets both at once. -/
theorem Meets.and {Meter : Type} [GasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    {A B : Evm fork Meter → Message fork → Evm fork Meter → Prop}
    (ha : Meets A runChild) (hb : Meets B runChild) :
    Meets (fun caller message child => A caller message child ∧ B caller message child)
      runChild :=
  ⟨fun caller message lt child ran => ⟨ha.ok caller message lt child ran,
    hb.ok caller message lt child ran⟩, ha.aborts⟩

/-- The state and the substate that the frame of a message starts from, after those of its caller.

Before Paris, the target of the message is touched first.

A message that moves a value then moves it from its sender to its target.

From Glamsterdam, it also logs a move to another account, by EIP-7708.

Any other message starts from there with the substate of its caller. -/
def Entered (fork : Fork) (message : Message fork) (state : TransactionState)
    (substate : Substate) (entry : TransactionState) (entrySubstate : Substate) : Prop :=
  (¬(message.shouldTransferValue = true ∧ message.value ≠ 0) ∧
      entry = startState fork message state ∧ entrySubstate = substate) ∨
    ((message.shouldTransferValue = true ∧ message.value ≠ 0) ∧
      (startState fork message state).moveEther fork message.caller message.currentTarget
        message.value = .ok entry ∧
      entrySubstate = { substate with
        logs := pushTransferLog fork substate.logs message.caller message.currentTarget
          message.value })

/-- A message that moves no value starts from the start state and the substate of its caller. -/
theorem Entered.of_not_transfers {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate)
    (hno : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0)) :
    entry = startState fork message state ∧ entrySubstate = substate := by
  rcases h with ⟨-, h⟩ | ⟨ht, -⟩
  · exact h
  · exact absurd ht hno

/-- A message with code `code` runs as a specification of that code says.

The message has a target and runs no precompile, and `G` holds of it and of its caller.

It may move a value.

Then the frame that ends it is a stopped frame of `Q`.

That frame is the one that the callee stopped in, after the rollback of a failure. -/
def RunsFrom (code : ByteArray) (G : Message fork → TransactionState → Substate → Prop)
    (Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop)
    (caller : Evm fork Nat) (message : Message fork) (child : Evm fork Nat) : Prop :=
  message.code = code → message.target.isSome → precompileAddress fork message = none →
    G message caller.state caller.substate.child →
    ∃ stopped, Q message caller.state caller.substate.child stopped ∧
      child = rollbackOnError caller.state stopped

/-- Each code of a family runs as its specification says, on each message with that code. -/
def RunsAll {ι : Type} (code : ι → ByteArray)
    (G : ι → Message fork → TransactionState → Substate → Prop)
    (Q : ι → Message fork → TransactionState → Substate → Evm fork Nat → Prop)
    (caller : Evm fork Nat) (message : Message fork) (child : Evm fork Nat) : Prop :=
  ∀ i, RunsFrom (code i) (G i) (Q i) caller message child

/-- The runner of the interpreter meets the specifications of a family of codes.

Each specification holds of every message with its code and `G`, from the frame it starts.

That frame starts after the move of the value of the message, if it has one.

It is a triple under the assumption that the whole family runs as specified, together with `B`.

So a code may call another of the family, or itself, or a code that calls it back.

The runner of the interpreter must meet `B` for every bound on the gas of messages.

The proof is an induction on that bound, since each message has less gas than the bound. -/
theorem meets_runsAll {ι : Type} {code : ι → ByteArray}
    {G : ι → Message fork → TransactionState → Substate → Prop}
    {Q : ι → Message fork → TransactionState → Substate → Evm fork Nat → Prop}
    {B : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hB : ∀ bound, Meets B (processRunner fork bound))
    (hspec : ∀ i message state substate entry entrySubstate, message.code = code i →
      G i message state substate → Entered fork message state substate entry entrySubstate →
      SpecUnder fork (fun caller message child => RunsAll code G Q caller message child ∧
          B caller message child)
        (At (code i) message 0 [] .empty message.gas entry entrySubstate)
        (Q i message state substate))
    (bound : Nat) :
    Meets (fun caller message child => RunsAll code G Q caller message child ∧
      B caller message child) (processRunner fork bound) := by
  induction bound using Nat.strongRecOn with
  | _ bound ih =>
  refine ⟨fun caller message lt child ran => ⟨fun i hcode htarget noPrecompile hg => ?_,
    (hB bound).ok caller message lt child ran⟩, (meets_process fork bound).aborts⟩
  obtain ⟨target, ht⟩ := Option.isSome_iff_exists.mp htarget
  simp only [processRunner, ht] at ran
  by_cases transfers : message.shouldTransferValue = true ∧ message.value ≠ 0
  · obtain ⟨moved, hmoved⟩ := moveEther_of_processMessage_eq_ok transfers ran
    rcases (hspec i message caller.state caller.substate.child _ _ hcode hg
        (.inr ⟨transfers, hmoved, rfl⟩)).runFrame
        (ih message.gas lt) (at_startFrame hcode _ _) (Nat.le_refl _) with
      ⟨stopped, hrun, hq⟩ | ⟨e, hrun, -⟩
    · have h := processMessage_map_val_value (state := caller.state) transfers hmoved
        noPrecompile hrun
      rw [ran] at h
      exact ⟨stopped, hq, Except.ok.inj h⟩
    · have h := processMessage_map_val_value (state := caller.state) transfers hmoved
        noPrecompile hrun
      rw [ran] at h
      cases h
  · rcases (hspec i message caller.state caller.substate.child _ _ hcode hg
        (.inl ⟨transfers, rfl, rfl⟩)).runFrame
        (ih message.gas lt) (at_startFrame hcode _ _) (Nat.le_refl _) with
      ⟨stopped, hrun, hq⟩ | ⟨e, hrun, -⟩
    · have h := processMessage_map_val (state := caller.state) transfers noPrecompile hrun
      rw [ran] at h
      exact ⟨stopped, hq, Except.ok.inj h⟩
    · have h := processMessage_map_val (state := caller.state) transfers noPrecompile hrun
      rw [ran] at h
      cases h

/-- A message to an account that exists starts from the state of its caller. -/
theorem startState_of_isSome {message : Message fork} {state : TransactionState}
    (h : (state.getAccountOptional message.currentTarget).isSome = true) :
    startState fork message state = state := by
  have hex : state.accountExists message.currentTarget = true := by
    simpa [TransactionState.accountExists] using h
  unfold startState TransactionState.touchAccount
  simp [hex]

/-! ## The effect of a message -/

/-- What a message may change in storage and in balances, and what it gives when it succeeds. -/
structure Change where
  /-- The slots that the message may touch. -/
  touched : List (Address × U256)
  /-- The addresses whose balances the message may move. -/
  moved : List Address
  /-- The facts of slots that the message gives when it succeeds. -/
  after : List SlotFact
  /-- The balances that the message gives when it succeeds, each with its address. -/
  funds : List (Address × U256)
  /-- The refund that the message adds when it succeeds. -/
  gain : Int

/-- The effect of a message on storage, from the state and substate before it to those after it.

`ok` says whether the message ended with no error.

Outside the touched slots and the moved addresses of the change, the state after agrees with it.

A message that fails touches no slot and moves no balance.

A message that succeeds gives the facts and the balances of the change.

It also adds the refund of the change to the refund counter. -/
structure Effect (change : Change) (state : TransactionState) (substate : Substate) (ok : Bool)
    (state' : TransactionState) (substate' : Substate) : Prop where
  /-- Outside the touched slots and the moved addresses, the state agrees with the old one.

  On a failure it agrees everywhere. -/
  agrees : Agrees (if ok then change.touched else []) (if ok then change.moved else []) state
    substate.accessedStorageKeys state' substate'.accessedStorageKeys
  /-- A message that succeeds gives the facts of the change. -/
  holds : ok = true → ∀ fact ∈ change.after, fact.Holds state' substate'
  /-- A message that succeeds gives the balances of the change. -/
  funds : ok = true → ∀ fund ∈ change.funds, (state'.getAccount fund.1).balance = fund.2
  /-- A message that succeeds adds the refund of the change to the refund counter. -/
  refund : substate'.refundCounter = substate.refundCounter + if ok then change.gain else 0

/-- The assumption that the frame that ends a message has an effect, as its caller takes it in. -/
def Effects (change : Change) (caller child : Evm fork Nat) : Prop :=
  Effect change caller.state caller.substate child.error.isNone
    (incorporateChild fork caller child).state (incorporateChild fork caller child).substate

/-- A callee whose stopped frame agrees with its caller's state outside a change has its effect.

The frame that ends the message is the stopped frame, rolled back on a failure.

On success, the stopped frame gives the facts and the balances of the change, and holds its refund.

On a failure the rollback gives back the state of the caller, so nothing is touched. -/
theorem effects_rollbackOnError {change : Change} {caller stopped : Evm fork Nat}
    (hagree : Agrees change.touched change.moved caller.state caller.substate.accessedStorageKeys
      stopped.state stopped.substate.accessedStorageKeys)
    (hholds : stopped.error = none →
      ∀ fact ∈ change.after, fact.Holds stopped.state stopped.substate)
    (hfunds : stopped.error = none →
      ∀ fund ∈ change.funds, (stopped.state.getAccount fund.1).balance = fund.2)
    (hrefund : stopped.error = none → stopped.substate.refundCounter = change.gain) :
    Effects change caller (rollbackOnError caller.state stopped) := by
  unfold Effects
  cases herr : stopped.error with
  | none =>
    rw [rollbackOnError_of_error_eq_none herr]
    simp only [incorporateChild, herr, Option.isNone_none, ite_true]
    exact ⟨hagree, fun _ => hholds herr, fun _ => hfunds herr, by simp [hrefund herr]⟩
  | some e =>
    have hrb : rollbackOnError caller.state stopped =
        { stopped with
          state := stopped.state.restoreTxState caller.state
          gas := if stopped.error = some .revert then GasMeter.rollback stopped.gas
            else stopped.gas } := by
      simp [rollbackOnError, herr]
    rw [hrb]
    simp only [incorporateChild, herr, Option.isNone_some, Bool.false_eq_true, ite_false]
    have hparent : stopped.state.parent = caller.state.parent := hagree.parent
    refine ⟨⟨fun address key _ => TransactionState.getStorage_restoreTxState hparent address key,
      fun _ _ _ => .rfl, hagree.original,
      fun address _ => TransactionState.getAccountOptional_restoreTxState hparent address,
      fun address => by rw [TransactionState.getAccountOptional_restoreTxState hparent address],
      fun hash => TransactionState.getCode_restoreTxState hparent hash, hparent⟩,
      fun h => (Bool.false_ne_true h).elim, fun h => (Bool.false_ne_true h).elim, by simp⟩

/-! ## Moving ether -/

/-- A change of one account that keeps it alive, its nonce and its code changes only that account.

The account exists before the change. -/
private theorem agrees_modifyState {tx tx' : TransactionState} {address : Address}
    {f : State.Account → Except State.StateError State.Account} {account : State.Account}
    (keys : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32))
    (hf : f (tx.getAccount address) = .ok account)
    (hex : (tx.getAccountOptional address).isSome = true)
    (hshape : nonceAndCode account = nonceAndCode (tx.getAccount address))
    (hlive : ¬(account.nonce = 0 ∧ account.codeHash = State.EMPTY_CODE_HASH ∧ account.balance = 0))
    (h : tx.modifyState fork address f = .ok tx') :
    Agrees [] [address] tx keys tx' keys ∧ tx'.getAccount address = account := by
  obtain ⟨account', hf', rfl⟩ := TransactionState.modifyState_eq_ok_iff.mp h
  rw [hf, Except.ok.injEq] at hf'
  subst hf'
  have hempty : ((tx.recordAccountRead address).setAccount address
      (some account)).accountExistsAndIsEmpty address = false := by
    simp only [TransactionState.accountExistsAndIsEmpty,
      TransactionState.getAccountOptional_setAccount_self]
    simpa [and_assoc] using hlive
  simp only [hempty, Bool.and_false, Bool.false_eq_true, ite_false]
  obtain ⟨old, hold⟩ := Option.isSome_iff_exists.mp hex
  refine ⟨⟨fun _ _ _ => rfl, fun _ _ _ => .rfl, rfl, fun other hm => ?_, fun other => ?_,
    fun _ => rfl, rfl⟩, ?_⟩
  · exact TransactionState.getAccountOptional_setAccount_of_ne _ _ (by simpa using hm)
  · by_cases ho : other = address
    · subst ho
      rw [TransactionState.getAccountOptional_setAccount_self, hold]
      simp only [Option.map_some]
      rw [hshape, TransactionState.getAccount, hold]
      rfl
    · rw [TransactionState.getAccountOptional_setAccount_of_ne _ _ ho]
      rfl
  · simp [TransactionState.getAccount, TransactionState.getAccountOptional_setAccount_self]

/-- A move of a value that is not 0 between two accounts changes only their balances.

The sender and the recipient differ.

The two accounts exist, and the sender has a nonce or a code, so that neither ends empty.

Every word of storage, every slot that is warm, every other account and every code stays. -/
theorem agrees_moveEther {state moved : TransactionState} {sender recipient : Address}
    {amount : U256} (keys : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32))
    (h : state.moveEther fork sender recipient amount = .ok moved) (hne : sender ≠ recipient)
    (hamount : amount ≠ 0)
    (hsender : (state.getAccount sender).nonce ≠ 0 ∨
      (state.getAccount sender).codeHash ≠ State.EMPTY_CODE_HASH)
    (hrecipient : (state.getAccountOptional recipient).isSome = true) :
    Agrees [] [sender, recipient] state keys moved keys := by
  unfold TransactionState.moveEther at h
  rcases TransactionState.modifyState_debit fork state sender amount with
    ⟨-, hmid⟩ | ⟨hfunds, mid, hmid, -, -⟩
  · simp [hmid, bind, Except.bind] at h
  simp only [hmid, bind, Except.bind] at h
  have hexS : (state.getAccountOptional sender).isSome = true := by
    cases hs : state.getAccountOptional sender
    · simp [TransactionState.getAccount, hs, State.EMPTY_ACCOUNT] at hsender
    · rfl
  obtain ⟨h1, -⟩ := agrees_modifyState (account :=
      { state.getAccount sender with balance := (state.getAccount sender).balance - amount })
    keys (by simp [State.Account.debit, hfunds]) hexS rfl
    (fun ⟨hn, hc, _⟩ => hsender.elim (fun h => h hn) fun h => h hc) hmid
  have hexR : (mid.getAccountOptional recipient).isSome = true := by
    rw [h1.account recipient (by simpa using Ne.symm hne)]
    exact hrecipient
  obtain ⟨account, hf, -, -⟩ := TransactionState.modifyState_eq_ok h
  unfold State.Account.credit at hf
  split at hf
  · rename_i hfit
    rw [Except.ok.injEq] at hf
    subst hf
    have hpos : 0 < amount.toNat := by
      rcases Nat.eq_zero_or_pos amount.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hamount
      · exact h0
    obtain ⟨h2, -⟩ := agrees_modifyState (account :=
        { mid.getAccount recipient with balance := (mid.getAccount recipient).balance + amount })
      keys (by simp [State.Account.credit, hfit]) hexR rfl
      (fun ⟨_, _, hb⟩ => by
        have := congrArg BitVec.toNat hb
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt hfit] at this
        simp at this
        omega) h
    exact (h1.trans h2).mono (fun _ hs => by simp at hs) fun address hm => by
      simp only [List.mem_append, List.mem_singleton] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact hm.symm
  · cases hf

/-! ## A call from a frame that knows slots -/

variable {code : ByteArray} {message : Message fork} {pc : Nat} {size : Nat}
  {facts : List (Nat × ByteArray)} {gas : Nat} {slots : List SlotFact} {refund : Int}
  {base : TransactionState} {accessed : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)}

/-- The facts of slots outside a list of touched slots. -/
def keptFacts (touched : List (Address × U256)) (slots : List SlotFact) : List SlotFact :=
  slots.filter fun fact => fact.slot ∉ touched

/-- A fact whose slot is not touched names a slot outside the touched ones. -/
theorem untouched_of_not_mem {touched : List (Address × U256)} {fact : SlotFact}
    (h : fact.slot ∉ touched) :
    Untouched touched fact.address (U256.toBeBytes fact.key) := by
  intro slot hs
  by_cases ha : slot.1 = fact.address
  · refine .inr fun hk => h ?_
    have : slot = fact.slot := by
      obtain ⟨a, k⟩ := slot
      simp only at ha hk
      simp [SlotFact.slot, ha, toBeBytes_inj hk]
    rw [← this]
    exact hs
  · exact .inl ha

/-- A fact outside the touched slots holds after a state that agrees outside them. -/
theorem SlotFact.Holds.of_agrees {touched : List (Address × U256)} {moved : List Address}
    {fact : SlotFact} {state state' : TransactionState} {substate substate' : Substate}
    (hold : fact.Holds state substate)
    (h : Agrees touched moved state substate.accessedStorageKeys state'
      substate'.accessedStorageKeys)
    (hu : Untouched touched fact.address (U256.toBeBytes fact.key)) :
    fact.Holds state' substate' :=
  ⟨by rw [h.original]; exact hold.1, by rw [h.storage _ _ hu]; exact hold.2.1,
    by rw [← hold.2.2]; exact decide_eq_decide.mpr (h.warm _ _ hu)⟩

/-- The price of a call that sends `value` and grows no memory, from Berlin to before Glamsterdam.

The value may be 0.

It pays the access to the address, and `extra` for the value. -/
abbrev callCost (fork : Fork) (value asked : U256) (gas extra : Nat) (cold : Bool) : Nat :=
  (messageCallGas fork value asked.toNat gas 0 ((if cold then 2600 else 100) + extra)).cost

/-- The gas that a call that sends `value` and grows no memory passes on, from Berlin.

It holds until before Glamsterdam.

It counts the stipend when the value is not 0. -/
abbrev callGas (fork : Fork) (value asked : U256) (gas extra : Nat) (cold : Bool) : Nat :=
  (messageCallGas fork value asked.toNat gas 0 ((if cold then 2600 else 100) + extra)).subCall

/-- The message that a call of the kind `kind`, with no value of its own, sends from a frame.

It runs the code `code` of the address `to`, with the data `data` and the gas `gas`.

CALL and STATICCALL run it on `to`, and CALLCODE and DELEGATECALL on the current account.

DELEGATECALL keeps the sender and the value of the current message.

The others send from the current account, with no value.

The message is one deeper than the frame, and static for STATICCALL or when the frame is. -/
def CallMessage (kind : CallKind) (message : Message fork) (to : Address) (code data : ByteArray)
    (gas : Nat) (msg : Message fork) : Prop :=
  msg.gas = gas ∧
    msg.caller = (if kind = .delegatecall then message.caller else message.currentTarget) ∧
    msg.currentTarget = (if kind = .call ∨ kind = .staticcall then to
      else message.currentTarget) ∧
    msg.target = some (if kind = .call ∨ kind = .staticcall then to
      else message.currentTarget) ∧
    msg.codeAddress = some to ∧ msg.code = code ∧ msg.data = data ∧
    msg.value = (if kind = .delegatecall then message.value else 0) ∧
    msg.depth = message.depth + 1 ∧ msg.isStatic = (kind == .staticcall || message.isStatic)

/-- A frame of the call, after the message, with a flag, a gas, its facts, its refund and a base.

The call succeeded, or it failed and `sure` is false.

On success the new base holds the balances of the change.

Memory keeps the facts apart from the output range.

On success it also holds `output` at the start of that range. -/
def AfterCall (code : ByteArray) (message : Message fork) (pc : Nat) (rest : List U256)
    (size : Nat) (facts : List (Nat × ByteArray)) (outputStart outputSize : U256)
    (output : ByteArray) (gas : Nat) (value asked : U256) (extra : Nat) (slots : List SlotFact)
    (refund : Int)
    (base : TransactionState) (accessed : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32))
    (change : Change) (sure : Bool) (evm : Evm fork Nat) : Prop :=
  ∃ cold left base' accessed', left ≤ callGas fork value asked gas extra cold ∧
    Agrees (change.touched ++ slots.map SlotFact.slot) change.moved base accessed base'
      accessed' ∧
    (((∀ fund ∈ change.funds, (base'.getAccount fund.1).balance = fund.2) ∧
      Stored code message (pc + 1) (1 :: rest) size
        ((outputStart.toNat, output) :: facts.filter (Apart outputStart.toNat outputSize.toNat))
        (gas - callCost fork value asked gas extra cold + left)
        (change.after ++ keptFacts change.touched slots) (refund + change.gain) base' accessed'
        evm) ∨
      sure = false ∧ Stored code message (pc + 1) (0 :: rest) size
        (facts.filter (Apart outputStart.toNat outputSize.toNat))
        (gas - callCost fork value asked gas extra cold + left) slots refund base' accessed' evm)

/-- A call whose ranges lie in memory, with an input range of a fact, grows no memory. -/
private theorem extendMemory_call {memory data : ByteArray}
    {inputStart inputSize outputStart outputSize : U256} (hsize : memory.size = size)
    (hold : Holds memory inputStart.toNat data) (hlen : data.size = inputSize.toNat)
    (houtput : outputStart.toNat + outputSize.toNat ≤ size) :
    extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)] = ⟨0, 0⟩ :=
  extendMemory_eq_zero _ _ fun p hp => by
    refine .inr (ceil32_le (ceil32_mod _) (Nat.le_trans ?_ (le_ceil32 _)))
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [← hlen]
      exact hold.1
    · rw [List.mem_singleton.mp hp, hsize]
      exact houtput

/-- The frame of a call, once it has recorded its accesses, keeps the facts of its slots.

It also keeps the agreement with its base. -/
private theorem stored_recordAccountRead {evm caller : Evm fork Nat} {address : Address}
    (hslots : ∀ fact ∈ slots, fact.Holds evm.state evm.substate)
    (hagree : Agrees (slots.map SlotFact.slot) [] base accessed evm.state
      evm.substate.accessedStorageKeys)
    (hcs : caller.state =
      (evm.state.recordAccountRead address).recordAccountRead message.currentTarget)
    (hcss : caller.substate = { evm.substate with
      accessedAddresses := evm.substate.accessedAddresses.insert address }) :
    (∀ fact ∈ slots, fact.Holds caller.state caller.substate) ∧
      Agrees (slots.map SlotFact.slot) [] base accessed caller.state
        caller.substate.accessedStorageKeys := by
  rw [hcs, hcss]
  exact ⟨hslots, ⟨hagree.storage, hagree.warm, hagree.original, hagree.account, hagree.shape,
    hagree.code, hagree.parent⟩⟩

/-- The frame after a call, from the frame that the call resumes with the effect of its callee.

The callee left `child`, and the call wrote its output into the output range, within memory. -/
private theorem afterCall_of_at {evm caller child final : Evm fork Nat} {rest : List U256}
    {outputStart outputSize value asked : U256} {output : ByteArray} {extra : Nat} {cold : Bool}
    {change : Change} {sure : Bool} (hsize : evm.memory.size = size) (hmod : size % 32 = 0)
    (hall : HoldsAll evm.memory facts) (hrefund : evm.substate.refundCounter = refund)
    (houtput : outputStart.toNat + outputSize.toNat ≤ size)
    (hslots : ∀ fact ∈ slots, fact.Holds caller.state caller.substate)
    (hagree : Agrees (slots.map SlotFact.slot) [] base accessed caller.state
      caller.substate.accessedStorageKeys)
    (hcss : caller.substate.refundCounter = evm.substate.refundCounter)
    (hle : child.gas ≤ callGas fork value asked gas extra cold)
    (heff : Effects change caller child) (hsure : sure = true → child.error = none)
    (hout : child.error = none →
      child.output.extract 0 (min outputSize.toNat child.output.size) = output)
    (hat : At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
      (memoryWrite evm.memory outputStart.toNat
        (child.output.extract 0 (min outputSize.toNat child.output.size)))
      (gas - callCost fork value asked gas extra cold + child.gas)
      (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
      final) :
    AfterCall code message pc rest size facts outputStart outputSize output gas value asked extra
      slots refund base accessed change sure final := by
  have hfit : outputStart.toNat +
      (child.output.extract 0 (min outputSize.toNat child.output.size)).size ≤
        evm.memory.size := by
    rw [hsize]
    simp only [ByteArray.size_extract]
    omega
  have hk : Known code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) size
      ((outputStart.toNat, child.output.extract 0 (min outputSize.toNat child.output.size)) ::
        facts.filter (Apart outputStart.toNat outputSize.toNat))
      (gas - callCost fork value asked gas extra cold + child.gas)
      (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
      final := by
    have hm := hat.2.2.2.2.2.1
    refine ⟨by rw [hm]; exact hat, by rw [hm, size_memoryWrite hfit, hsize], hmod, ?_⟩
    rw [hm]
    refine fun fact hfact => holdsAll_memoryWrite hfit hall fact ?_
    rcases List.mem_cons.mp hfact with rfl | hfact
    · exact List.mem_cons_self ..
    · obtain ⟨hmem, hapart⟩ := List.mem_filter.mp hfact
      refine List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hmem, ?_⟩)
      simp only [Apart, Bool.or_eq_true, decide_eq_true_eq, ByteArray.size_extract] at hapart ⊢
      omega
  have hagree' := hagree.trans heff.agrees
  refine ⟨cold, child.gas, (incorporateChild fork caller child).state,
    (incorporateChild fork caller child).substate.accessedStorageKeys, hle, ?_, ?_⟩
  · cases hok : child.error.isNone
    · simp only [hok] at hagree'
      exact hagree'.mono (fun slot hs => List.mem_append_right _ (by simpa using hs))
        fun address hm => by simp at hm
    · simp only [hok, ite_true] at hagree'
      exact hagree'.mono (fun _ hs => hs) fun address hm => by simpa using hm
  · cases hok : child.error.isNone
    · simp only [hok, Bool.false_eq_true, ite_false] at hk
      refine .inr ⟨?_, stored_of_known (hk.mono fun fact hfact => List.mem_cons_of_mem _ hfact)
        ?_ ?_ (Agrees.refl _ _ _ _)⟩
      · cases sure
        · rfl
        · simp [hsure rfl] at hok
      · intro fact hfact
        exact (hslots fact hfact).of_agrees (touched := [])
          (by simpa [hok] using heff.agrees) fun _ hs => by cases hs
      · rw [heff.refund, hok, hcss]
        simp [hrefund]
    · have hnone : child.error = none := Option.isNone_iff_eq_none.mp hok
      rw [hout hnone] at hk
      refine .inl ⟨heff.funds hok,
        stored_of_known (by simpa [hok] using hk) ?_ ?_ (Agrees.refl _ _ _ _)⟩
      · intro fact hfact
        rcases List.mem_append.mp hfact with hfact | hfact
        · exact heff.holds hok fact hfact
        · obtain ⟨hmem, hnot⟩ := List.mem_filter.mp hfact
          exact (hslots fact hmem).of_agrees (by simpa [hok] using heff.agrees)
            (untouched_of_not_mem (by simpa using hnot))
      · rw [heff.refund, hok, hcss]
        simp [hrefund]

/-- From Berlin to before Glamsterdam, a call that sends no value of its own from a frame of slots.

The byte at `pc` runs the call of the kind `kind`, which sends a message.

The callee has an effect on storage.

The input range holds the bytes `data` of a fact of memory.

The output range lies within memory.

The callee runs the code of `to`, which the base state holds, and is no delegation.

Each frame that ends such a message from the frame has the effect, by the assumption `callee`.

The assumption also says what such a frame writes into the output range when it ends with no error.

That is the start of its output, at most as long as the range, and it must be `output`.

When `sure` is true, it says that such a frame ends with no error.

The frame needs the gas of a call to a cold address.

The frame then pushes 1 and knows the facts of the effect and of the slots it does not touch.

It adds the refund of the effect.

Its memory holds `output` at the start of the output range.

Or, only when `sure` is false, the call fails.

The frame then pushes 0 and keeps its facts of slots and its refund counter.

Either way, memory keeps the facts apart from the output range.

The frame gets back the gas that the callee leaves, at most the gas it passed on.

The new base agrees with the old one outside the touched slots and the slots of the facts. -/
theorem callKind_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {kind : CallKind}
    {byte : UInt8} {op : Op} {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {data output calleeCode : ByteArray} {change : Change} {sure : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.ofByte fork byte = some op) (hnone : instruction (Meter := Nat) fork op = none)
    (hrun : messageInstruction (Meter := Nat) fork op = some (callStep kind))
    (hinput : (inputStart.toNat, data) ∈ facts) (hlen : data.size = inputSize.toNat)
    (houtput : outputStart.toNat + outputSize.toNat ≤ size)
    (hcode : base.getCode (base.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) (hgas : 2600 ≤ gas)
    (heffect : ∀ caller msg child cold, callee caller msg child →
      CallMessage kind message (toAddressMasked to) calleeCode data
        (callGas fork 0 asked gas 0 cold) msg →
      (∀ fact ∈ slots, fact.Holds caller.state caller.substate) →
      Agrees (slots.map SlotFact.slot) [] base accessed caller.state
        caller.substate.accessedStorageKeys →
      Effects change caller child ∧ (sure = true → child.error = none) ∧
        (child.error = none →
          child.output.extract 0 (min outputSize.toNat child.output.size) = output)) :
    HoareUnder fork callee
      (Stored code message pc (asked :: to :: ((if kind.sendsValue then [0] else []) ++
          inputStart :: inputSize :: outputStart :: outputSize :: rest)) size facts gas
        slots refund base accessed)
      (AfterCall code message pc rest size facts outputStart outputSize output gas 0 asked 0
        slots refund base accessed change sure) := by
  intro bound runChild meets evm ⟨⟨hat, hsize, hmod, hall⟩, hslots, hrefund, hagree⟩ within
  have hold := hall _ hinput
  have hext := extendMemory_call hsize hold hlen houtput
  have hcode' : evm.state.getCode (evm.state.getAccount (toAddressMasked to)).codeHash =
      .ok calleeCode := by
    rw [hagree.code, TransactionState.getAccount, hagree.account _ (by simp)]
    exact hcode
  have hcall := callKindWith (callee := callee) (asked := asked) (inputStart := inputStart)
    (inputSize := inputSize) (outputStart := outputStart) (outputSize := outputSize)
    (rest := rest) (memory := evm.memory) (gas := gas) (state := evm.state)
    (substate := evm.substate) hfork hglam hlt hbyte decoded hnone hrun hcode' hdel hdepth rfl
    (by rw [hext]; split <;> simp only <;> omega)
  rw [hext] at hcall
  obtain ⟨final, hreach, hq | aborted⟩ := hcall bound runChild meets evm hat within
  · refine ⟨final, hreach, .inl ?_⟩
    obtain ⟨caller, msg, child, hc, hle, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv,
      hmdep, hmst, hat'⟩ := hq
    have hdata : msg.data = data := by
      rw [hmd, memoryExtend_zero, ← hlen, hold.2]
    obtain ⟨hpre_slots, hpre_agree⟩ := stored_recordAccountRead hslots hagree hcs hcss
    obtain ⟨heff, hsure, hout⟩ := heffect caller msg child
      (decide (toAddressMasked to ∉ evm.substate.accessedAddresses)) hc
      ⟨hmg, hmc, hmt, hmtg, hmca, hmcode, hdata, hmv, hmdep, hmst⟩ hpre_slots hpre_agree
    rw [memoryExtend_zero] at hat'
    exact afterCall_of_at hsize hmod hall hrefund houtput hpre_slots hpre_agree
      (by rw [hcss]) (le_of_le_of_eq hle hmg) heff hsure hout hat'
  · exact ⟨final, hreach, .inr aborted⟩

/-- From Berlin to before Glamsterdam, CALL with no value from a frame that knows slots.

The callee runs the code of `to` on `to`, from the current account.

The rest is as for every call that sends no value of its own. -/
theorem call_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {data output calleeCode : ByteArray} {change : Change} {sure : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hinput : (inputStart.toNat, data) ∈ facts) (hlen : data.size = inputSize.toNat)
    (houtput : outputStart.toNat + outputSize.toNat ≤ size)
    (hcode : base.getCode (base.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) (hgas : 2600 ≤ gas)
    (heffect : ∀ caller msg child cold, callee caller msg child →
      CallMessage .call message (toAddressMasked to) calleeCode data
        (callGas fork 0 asked gas 0 cold) msg →
      (∀ fact ∈ slots, fact.Holds caller.state caller.substate) →
      Agrees (slots.map SlotFact.slot) [] base accessed caller.state
        caller.substate.accessedStorageKeys →
      Effects change caller child ∧ (sure = true → child.error = none) ∧
        (child.error = none →
          child.output.extract 0 (min outputSize.toNat child.output.size) = output)) :
    HoareUnder fork callee
      (Stored code message pc
        (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: outputSize :: rest) size
        facts gas slots refund base accessed)
      (AfterCall code message pc rest size facts outputStart outputSize output gas 0 asked 0
        slots refund base accessed change sure) :=
  callKind_stored (kind := .call) hfork hglam hlt hbyte
    (ofByte_of_decode (op := .call) rfl (Fork.frontier_le _)) instruction_call
    messageInstruction_call hinput hlen houtput hcode hdel hdepth hgas heffect

/-- From Berlin to before Glamsterdam, STATICCALL from a frame that knows slots.

The callee runs the code of `to` on `to`, from the current account, and its message is static.

The rest is as for every call that sends no value of its own. -/
theorem staticcall_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {data output calleeCode : ByteArray} {change : Change} {sure : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    (hinput : (inputStart.toNat, data) ∈ facts) (hlen : data.size = inputSize.toNat)
    (houtput : outputStart.toNat + outputSize.toNat ≤ size)
    (hcode : base.getCode (base.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) (hgas : 2600 ≤ gas)
    (heffect : ∀ caller msg child cold, callee caller msg child →
      CallMessage .staticcall message (toAddressMasked to) calleeCode data
        (callGas fork 0 asked gas 0 cold) msg →
      (∀ fact ∈ slots, fact.Holds caller.state caller.substate) →
      Agrees (slots.map SlotFact.slot) [] base accessed caller.state
        caller.substate.accessedStorageKeys →
      Effects change caller child ∧ (sure = true → child.error = none) ∧
        (child.error = none →
          child.output.extract 0 (min outputSize.toNat child.output.size) = output)) :
    HoareUnder fork callee
      (Stored code message pc
        (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest) size facts gas
        slots refund base accessed)
      (AfterCall code message pc rest size facts outputStart outputSize output gas 0 asked 0
        slots refund base accessed change sure) :=
  callKind_stored (kind := .staticcall) hfork hglam hlt hbyte
    (ofByte_of_decode rfl (Nat.le_trans (by decide) hfork)) instruction_staticcall
    (messageInstruction_staticcall (Nat.le_trans (by decide) hfork)) hinput hlen houtput hcode hdel
    hdepth hgas heffect

/-- From Berlin to before Glamsterdam, DELEGATECALL from a frame that knows slots.

The callee runs the code of `to` on the current account.

It keeps the sender and the value of the current message.

The rest is as for every call that sends no value of its own. -/
theorem delegatecall_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {data output calleeCode : ByteArray} {change : Change} {sure : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf4)
    (hinput : (inputStart.toNat, data) ∈ facts) (hlen : data.size = inputSize.toNat)
    (houtput : outputStart.toNat + outputSize.toNat ≤ size)
    (hcode : base.getCode (base.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) (hgas : 2600 ≤ gas)
    (heffect : ∀ caller msg child cold, callee caller msg child →
      CallMessage .delegatecall message (toAddressMasked to) calleeCode data
        (callGas fork 0 asked gas 0 cold) msg →
      (∀ fact ∈ slots, fact.Holds caller.state caller.substate) →
      Agrees (slots.map SlotFact.slot) [] base accessed caller.state
        caller.substate.accessedStorageKeys →
      Effects change caller child ∧ (sure = true → child.error = none) ∧
        (child.error = none →
          child.output.extract 0 (min outputSize.toNat child.output.size) = output)) :
    HoareUnder fork callee
      (Stored code message pc
        (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest) size facts gas
        slots refund base accessed)
      (AfterCall code message pc rest size facts outputStart outputSize output gas 0 asked 0
        slots refund base accessed change sure) :=
  callKind_stored (kind := .delegatecall) hfork hglam hlt hbyte
    (ofByte_of_decode rfl (Nat.le_trans (by decide) hfork)) instruction_delegatecall
    (messageInstruction_delegatecall (Nat.le_trans (by decide) hfork)) hinput hlen houtput hcode
    hdel hdepth hgas heffect

/-- From Berlin to before Glamsterdam, CALLCODE with no value from a frame that knows slots.

The callee runs the code of `to` on the current account, from the current account.

The rest is as for every call that sends no value of its own. -/
theorem callcode_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {data output calleeCode : ByteArray} {change : Change} {sure : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf2)
    (hinput : (inputStart.toNat, data) ∈ facts) (hlen : data.size = inputSize.toNat)
    (houtput : outputStart.toNat + outputSize.toNat ≤ size)
    (hcode : base.getCode (base.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) (hgas : 2600 ≤ gas)
    (heffect : ∀ caller msg child cold, callee caller msg child →
      CallMessage .callcode message (toAddressMasked to) calleeCode data
        (callGas fork 0 asked gas 0 cold) msg →
      (∀ fact ∈ slots, fact.Holds caller.state caller.substate) →
      Agrees (slots.map SlotFact.slot) [] base accessed caller.state
        caller.substate.accessedStorageKeys →
      Effects change caller child ∧ (sure = true → child.error = none) ∧
        (child.error = none →
          child.output.extract 0 (min outputSize.toNat child.output.size) = output)) :
    HoareUnder fork callee
      (Stored code message pc
        (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: outputSize :: rest) size
        facts gas slots refund base accessed)
      (AfterCall code message pc rest size facts outputStart outputSize output gas 0 asked 0
        slots refund base accessed change sure) :=
  callKind_stored (kind := .callcode) hfork hglam hlt hbyte
    (ofByte_of_decode (op := .callcode) rfl (Fork.frontier_le _)) instruction_callcode
    messageInstruction_callcode hinput hlen houtput hcode hdel hdepth hgas heffect

/-- The message that CALL with a value sends from a frame, to the code of an address.

It runs the code `code` of the address `to` on `to`, with the data `data` and the gas `gas`.

It sends from the current account, carries the value `value`, and moves it.

The message is one deeper than the frame, and not static. -/
def ValueMessage (message : Message fork) (to : Address) (code data : ByteArray) (value : U256)
    (gas : Nat) (msg : Message fork) : Prop :=
  msg.gas = gas ∧ msg.caller = message.currentTarget ∧ msg.currentTarget = to ∧
    msg.target = some to ∧ msg.codeAddress = some to ∧ msg.code = code ∧ msg.data = data ∧
    msg.value = value ∧ msg.shouldTransferValue = true ∧ msg.depth = message.depth + 1 ∧
    msg.isStatic = false

/-- From Berlin to before Glamsterdam, CALL with a value `v`, not 0, from a frame that knows slots.

The frame may change the state, and its account holds at least `v` in the base state.

The callee has an effect on storage and on balances.

The input range holds the bytes `data` of a fact of memory.

The output range lies within memory.

The callee runs the code of `to`, which the base state holds, and is no delegation.

Each frame that ends such a message from the frame has the effect, by the assumption `callee`.

The assumption also says what such a frame writes into the output range when it ends with no error.

That is the start of its output, at most as long as the range, and it must be `output`.

When `sure` is true, it says that such a frame ends with no error.

The frame needs 2600 for a cold access and 9000 for the value.

It also needs 25000 when the callee is dead in the base state, by EIP-161.

The frame then pushes 1 and knows the facts of the effect and of the slots it does not touch.

It adds the refund of the effect, and the new base holds the balances of the effect.

Its memory holds `output` at the start of the output range.

Or, only when `sure` is false, the call fails.

The frame then pushes 0 and keeps its facts of slots and its refund counter.

Either way, memory keeps the facts apart from the output range.

The frame gets back the gas that the callee leaves, at most the gas it passed on with the stipend.

The new base agrees with the old one outside the touched slots and the slots of the facts.

It also agrees outside the addresses whose balances the effect moves. -/
theorem callValue_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to v inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {data output calleeCode : ByteArray} {change : Change} {sure : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) (hv : v ≠ 0)
    (hstatic : message.isStatic = false)
    (hbal : v ≤ (base.getAccount message.currentTarget).balance)
    (hinput : (inputStart.toNat, data) ∈ facts) (hlen : data.size = inputSize.toNat)
    (houtput : outputStart.toNat + outputSize.toNat ≤ size)
    (hcode : base.getCode (base.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : 2600 + (callNewAccountCost fork base (toAddressMasked to) v + callValueCost fork v) ≤
      gas)
    (heffect : ∀ caller msg child cold, callee caller msg child →
      ValueMessage message (toAddressMasked to) calleeCode data v
        (callGas fork v asked gas
          (callNewAccountCost fork base (toAddressMasked to) v + callValueCost fork v) cold) msg →
      (∀ fact ∈ slots, fact.Holds caller.state caller.substate) →
      Agrees (slots.map SlotFact.slot) [] base accessed caller.state
        caller.substate.accessedStorageKeys →
      Effects change caller child ∧ (sure = true → child.error = none) ∧
        (child.error = none →
          child.output.extract 0 (min outputSize.toNat child.output.size) = output)) :
    HoareUnder fork callee
      (Stored code message pc
        (asked :: to :: v :: inputStart :: inputSize :: outputStart :: outputSize :: rest) size
        facts gas slots refund base accessed)
      (AfterCall code message pc rest size facts outputStart outputSize output gas v asked
        (callNewAccountCost fork base (toAddressMasked to) v + callValueCost fork v) slots refund
        base accessed change sure) := by
  intro bound runChild meets evm ⟨⟨hat, hsize, hmod, hall⟩, hslots, hrefund, hagree⟩ within
  have hold := hall _ hinput
  have hext := extendMemory_call hsize hold hlen houtput
  have hacc : ∀ address, evm.state.getAccountOptional address = base.getAccountOptional address :=
    fun address => hagree.account address (by simp)
  have hcode' : evm.state.getCode (evm.state.getAccount (toAddressMasked to)).codeHash =
      .ok calleeCode := by
    rw [hagree.code, TransactionState.getAccount, hacc]
    exact hcode
  have hbal' : v ≤ (evm.state.getAccount message.currentTarget).balance := by
    rw [TransactionState.getAccount, hacc]
    exact hbal
  have hnew : callNewAccountCost fork evm.state (toAddressMasked to) v =
      callNewAccountCost fork base (toAddressMasked to) v := by
    unfold callNewAccountCost TransactionState.isAccountAlive TransactionState.accountExists
    rw [hacc]
  have hcost := callBaseCost_of_berlin hfork hglam
    (decide (toAddressMasked to ∉ evm.substate.accessedAddresses))
  have hcall := callValue (callee := callee) (asked := asked) (inputStart := inputStart)
    (inputSize := inputSize) (outputStart := outputStart) (outputSize := outputSize)
    (rest := rest) (memory := evm.memory) (gas := gas) (state := evm.state)
    (substate := evm.substate) hfork hglam hlt hbyte hv hstatic hbal' hcode' hdel hdepth rfl
    (by rw [hext, hcost, hnew]; split <;> simp only <;> omega)
  rw [hext, hcost, hnew, Nat.add_assoc] at hcall
  obtain ⟨final, hreach, hq | aborted⟩ := hcall bound runChild meets evm hat within
  · refine ⟨final, hreach, .inl ?_⟩
    obtain ⟨caller, msg, child, hc, hle, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv,
      hmtr, hmdep, hmst, hat'⟩ := hq
    have hdata : msg.data = data := by
      rw [hmd, memoryExtend_zero, ← hlen, hold.2]
    obtain ⟨hpre_slots, hpre_agree⟩ := stored_recordAccountRead hslots hagree hcs hcss
    obtain ⟨heff, hsure, hout⟩ := heffect caller msg child
      (decide (toAddressMasked to ∉ evm.substate.accessedAddresses)) hc
      ⟨hmg, hmc, hmt, hmtg, hmca, hmcode, hdata, hmv, hmtr, hmdep, hmst⟩ hpre_slots hpre_agree
    rw [memoryExtend_zero] at hat'
    exact afterCall_of_at hsize hmod hall hrefund houtput hpre_slots hpre_agree
      (by rw [hcss]) (le_of_le_of_eq hle hmg) heff hsure hout hat'
  · exact ⟨final, hreach, .inr aborted⟩

end EthLib.Execution.Evm.Logic
