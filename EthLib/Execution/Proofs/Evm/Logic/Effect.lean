module

public import EthLib.Execution.Proofs.Evm.Logic.Slots
public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Evm.Logic.Call

/-!
# Proofs: the effect of a message on the slots of storage

A frame that knows a few slots of storage can send a message, and go on knowing them.

The effect of a message names the slots that it may touch, from the frame that sends it.

Outside those slots, the frame that ends the message agrees with the frame before it.

So every word reads as before there, and every slot is warm exactly when it was.

The words before the transaction, the accounts, the codes and the block stay too.

A message that fails touches no slot at all.

A message that succeeds also gives the facts of some slots, and a refund to add.

- A callee whose stopped frame agrees with the state it started from, outside some slots, has one.
- On success that stopped frame must give the facts and the refund of the effect.
- A failure rolls the state back, so the callee then touches no slot.
- From Berlin to before Glamsterdam, CALL with no value keeps each fact of a slot it does not touch.
- It needs an input range that a fact of memory holds, and an empty output range.
- It also needs the gas of a call to a cold address.
- On success, the frame then knows the facts that the effect gives, and adds its refund.
- On failure, it keeps every fact and the refund counter.
- Either way, its base agrees with the base before the call outside the touched slots and the facts.

A callee may call its caller again, before it ends.

Then the code of the caller runs again, and its own specification says what that run does.

The runner of the interpreter meets the specifications of a family of codes that call each other.

Each specification may assume the specifications of the whole family on the messages it sends.

That holds by induction on the bound on the gas of messages, which each message is below.

An effect keeps the accounts, the codes and the words before the transaction.

So it leaves out a callee that moves ether, creates an account or changes a code.
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

/-- Each code of a family runs as its specification says, on each message with that code. -/
def RunsAll {ι : Type} (code : ι → ByteArray)
    (G : ι → Message fork → TransactionState → Substate → Prop)
    (Q : ι → Message fork → TransactionState → Substate → Evm fork Nat → Prop)
    (caller : Evm fork Nat) (message : Message fork) (child : Evm fork Nat) : Prop :=
  ∀ i, RunsAs (code i) (G i) (Q i) caller message child

/-- The runner of the interpreter meets the specifications of a family of codes.

Each specification holds of every message with its code and `G`, from the frame it starts.

It is a triple under the assumption that the whole family runs as specified, together with `B`.

So a code may call another of the family, or itself, or a code that calls it back.

The runner of the interpreter must meet `B` for every bound on the gas of messages.

The proof is an induction on that bound, since each message has less gas than the bound. -/
theorem meets_runsAll {ι : Type} {code : ι → ByteArray}
    {G : ι → Message fork → TransactionState → Substate → Prop}
    {Q : ι → Message fork → TransactionState → Substate → Evm fork Nat → Prop}
    {B : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hB : ∀ bound, Meets B (processRunner fork bound))
    (hspec : ∀ i message state substate, message.code = code i → G i message state substate →
      SpecUnder fork (fun caller message child => RunsAll code G Q caller message child ∧
          B caller message child)
        (At (code i) message 0 [] .empty message.gas (startState fork message state) substate)
        (Q i message state substate))
    (bound : Nat) :
    Meets (fun caller message child => RunsAll code G Q caller message child ∧
      B caller message child) (processRunner fork bound) := by
  induction bound using Nat.strongRecOn with
  | _ bound ih =>
  refine ⟨fun caller message lt child ran => ⟨fun i hcode htarget noValue noPrecompile hg => ?_,
    (hB bound).ok caller message lt child ran⟩, (meets_process fork bound).aborts⟩
  obtain ⟨target, ht⟩ := Option.isSome_iff_exists.mp htarget
  simp only [processRunner, ht] at ran
  rcases (hspec i message caller.state caller.substate.child hcode hg).runFrame
      (ih message.gas lt) (at_startFrame hcode _ _) (Nat.le_refl _) with
    ⟨stopped, hrun, hq⟩ | ⟨e, hrun, -⟩
  · have h := processMessage_map_val (state := caller.state) noValue noPrecompile hrun
    rw [ran] at h
    exact ⟨stopped, hq, Except.ok.inj h⟩
  · have h := processMessage_map_val (state := caller.state) noValue noPrecompile hrun
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

/-- The effect of a message on storage, from the state and substate before it to those after it.

`ok` says whether the message ended with no error.

Outside the slots of `touched`, the state after agrees with the state before.

A message that fails touches no slot.

A message that succeeds gives the facts of `after`, and adds `gain` to the refund counter. -/
structure Effect (touched : List (Address × U256)) (after : List SlotFact) (gain : Int)
    (state : TransactionState) (substate : Substate) (ok : Bool) (state' : TransactionState)
    (substate' : Substate) : Prop where
  /-- Outside the touched slots, or at all slots on a failure, the state agrees with the old one. -/
  agrees : Agrees (if ok then touched else []) state substate.accessedStorageKeys state'
    substate'.accessedStorageKeys
  /-- A message that succeeds gives the facts of `after`. -/
  holds : ok = true → ∀ fact ∈ after, fact.Holds state' substate'
  /-- A message that succeeds adds `gain` to the refund counter. -/
  refund : substate'.refundCounter = substate.refundCounter + if ok then gain else 0

/-- The assumption that the frame that ends a message has an effect, as its caller takes it in. -/
def Effects (touched : List (Address × U256)) (after : List SlotFact) (gain : Int)
    (caller child : Evm fork Nat) : Prop :=
  Effect touched after gain caller.state caller.substate child.error.isNone
    (incorporateChild fork caller child).state (incorporateChild fork caller child).substate

/-- A callee that stops in a frame that agrees with its start, outside some slots, has an effect.

The frame that ends the message is the stopped frame, rolled back on a failure.

On success, the stopped frame gives the facts of `after` and holds the refund `gain`.

On a failure the rollback gives back the state of the caller, so no slot is touched. -/
theorem effects_rollbackOnError {touched : List (Address × U256)} {after : List SlotFact}
    {gain : Int} {caller stopped : Evm fork Nat}
    (hagree : Agrees touched caller.state caller.substate.accessedStorageKeys stopped.state
      stopped.substate.accessedStorageKeys)
    (hholds : stopped.error = none → ∀ fact ∈ after, fact.Holds stopped.state stopped.substate)
    (hrefund : stopped.error = none → stopped.substate.refundCounter = gain) :
    Effects touched after gain caller (rollbackOnError caller.state stopped) := by
  unfold Effects
  cases herr : stopped.error with
  | none =>
    rw [rollbackOnError_of_error_eq_none herr]
    simp only [incorporateChild, herr, Option.isNone_none, ite_true]
    exact ⟨hagree, fun _ => hholds herr, by simp [hrefund herr]⟩
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
      fun address => TransactionState.getAccountOptional_restoreTxState hparent address,
      fun hash => TransactionState.getCode_restoreTxState hparent hash, hparent⟩,
      fun h => (Bool.false_ne_true h).elim, by simp⟩

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
theorem SlotFact.Holds.of_agrees {touched : List (Address × U256)} {fact : SlotFact}
    {state state' : TransactionState} {substate substate' : Substate}
    (hold : fact.Holds state substate)
    (h : Agrees touched state substate.accessedStorageKeys state' substate'.accessedStorageKeys)
    (hu : Untouched touched fact.address (U256.toBeBytes fact.key)) :
    fact.Holds state' substate' :=
  ⟨by rw [h.original]; exact hold.1, by rw [h.storage _ _ hu]; exact hold.2.1,
    by rw [← hold.2.2]; exact decide_eq_decide.mpr (h.warm _ _ hu)⟩

/-- The price of CALL with no value and no growth of memory, from Berlin. -/
abbrev callCost (fork : Fork) (asked : U256) (gas : Nat) (cold : Bool) : Nat :=
  (messageCallGas fork 0 asked.toNat gas 0 (if cold then 2600 else 100)).cost

/-- The gas that CALL with no value and no growth of memory passes on, from Berlin. -/
abbrev callGas (fork : Fork) (asked : U256) (gas : Nat) (cold : Bool) : Nat :=
  (messageCallGas fork 0 asked.toNat gas 0 (if cold then 2600 else 100)).subCall

/-- A frame of the call, after the message, with a flag, a gas, its facts, its refund and a base.

The call succeeded, or it failed and `sure` is false. -/
def AfterCall (code : ByteArray) (message : Message fork) (pc : Nat) (rest : List U256)
    (size : Nat) (facts : List (Nat × ByteArray)) (gas : Nat) (asked : U256) (slots : List SlotFact)
    (refund : Int) (base : TransactionState)
    (accessed : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32))
    (touched : List (Address × U256)) (after : List SlotFact) (gain : Int) (sure : Bool)
    (evm : Evm fork Nat) : Prop :=
  ∃ cold left base' accessed', left ≤ callGas fork asked gas cold ∧
    Agrees (touched ++ slots.map SlotFact.slot) base accessed base' accessed' ∧
    (Stored code message (pc + 1) (1 :: rest) size facts (gas - callCost fork asked gas cold + left)
        (after ++ keptFacts touched slots) (refund + gain) base' accessed' evm ∨
      sure = false ∧ Stored code message (pc + 1) (0 :: rest) size facts
        (gas - callCost fork asked gas cold + left) slots refund base' accessed' evm)

/-- From Berlin to before Glamsterdam, CALL with no value from a frame that knows slots.

The callee has an effect on storage.

The input range holds the bytes `data` of a fact of memory, and the output range is empty.

The callee runs the code of `to`, which the base state holds, and is no delegation.

Each frame that ends such a message from the frame has the effect, by the assumption `callee`.

When `sure` is true, the assumption also says that such a frame ends with no error.

The frame needs the gas of a call to a cold address.

The frame then pushes 1 and knows the facts of the effect and of the slots it does not touch.

It adds the refund of the effect.

Or, only when `sure` is false, the call fails.

The frame then pushes 0 and keeps its facts and its refund counter.

Either way, it gets back the gas that the callee leaves, at most the gas it passed on.

The new base agrees with the old one outside the touched slots and the slots of the facts. -/
theorem call_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart : U256} {rest : List U256}
    {data calleeCode : ByteArray} {touched : List (Address × U256)} {after : List SlotFact}
    {gain : Int} {sure : Bool} (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hinput : (inputStart.toNat, data) ∈ facts) (hlen : data.size = inputSize.toNat)
    (hcode : base.getCode (base.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) (hgas : 2600 ≤ gas)
    (heffect : ∀ caller msg child cold, callee caller msg child →
      msg.code = calleeCode → msg.currentTarget = toAddressMasked to →
      msg.target = some (toAddressMasked to) → msg.codeAddress = some (toAddressMasked to) →
      msg.caller = message.currentTarget → msg.value = 0 → msg.data = data →
      msg.depth = message.depth + 1 → msg.isStatic = message.isStatic →
      msg.gas = callGas fork asked gas cold →
      (∀ fact ∈ slots, fact.Holds caller.state caller.substate) →
      Agrees (slots.map SlotFact.slot) base accessed caller.state
        caller.substate.accessedStorageKeys →
      Effects touched after gain caller child ∧ (sure = true → child.error = none)) :
    HoareUnder fork callee
      (Stored code message pc
        (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: 0 :: rest) size facts gas
        slots refund base accessed)
      (AfterCall code message pc rest size facts gas asked slots refund base accessed touched after
        gain sure) := by
  intro bound runChild meets evm ⟨⟨hat, hsize, hmod, hall⟩, hslots, hrefund, hagree⟩ within
  have hold := hall _ hinput
  have hext : extendMemory evm.memory.size [(inputStart, inputSize), (outputStart, 0)] = ⟨0, 0⟩ :=
    extendMemory_eq_zero _ _ fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · refine .inr (ceil32_le (ceil32_mod _) (Nat.le_trans ?_ (le_ceil32 _)))
        rw [← hlen]
        exact hold.1
      · rw [List.mem_singleton.mp hp]
        exact .inl rfl
  have hcode' : evm.state.getCode (evm.state.getAccount (toAddressMasked to)).codeHash =
      .ok calleeCode := by
    rw [hagree.code, TransactionState.getAccount, hagree.account]
    exact hcode
  have hcall := callWith (callee := callee) (asked := asked) (inputStart := inputStart)
    (inputSize := inputSize) (outputStart := outputStart) (outputSize := 0) (rest := rest)
    (memory := evm.memory) (gas := gas) (state := evm.state) (substate := evm.substate)
    hfork hglam hlt hbyte hcode' hdel hdepth rfl
    (by rw [hext]; split <;> simp only <;> omega)
  rw [hext] at hcall
  obtain ⟨final, hreach, hq | aborted⟩ := hcall bound runChild meets evm hat within
  · refine ⟨final, hreach, .inl ?_⟩
    obtain ⟨caller, msg, child, hc, hle, hcs, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv,
      hmdep, hmst, hat'⟩ := hq
    have hdata : msg.data = data := by
      rw [hmd, memoryExtend_zero, ← hlen, hold.2]
    have hpre_slots : ∀ fact ∈ slots, fact.Holds caller.state caller.substate := by
      intro fact hfact
      rw [hcs, hcss]
      exact hslots fact hfact
    have hpre_agree : Agrees (slots.map SlotFact.slot) base accessed caller.state
        caller.substate.accessedStorageKeys := by
      rw [hcs, hcss]
      exact ⟨hagree.storage, hagree.warm, hagree.original, hagree.account, hagree.code,
        hagree.parent⟩
    obtain ⟨heff, hsure⟩ := heffect caller msg child
      (decide (toAddressMasked to ∉ evm.substate.accessedAddresses)) hc hmcode hmt hmtg hmca hmc
      hmv hdata hmdep hmst hmg hpre_slots hpre_agree
    have hmem : memoryWrite (memoryExtend evm.memory 0) outputStart.toNat
        (child.output.extract 0 (min (0 : U256).toNat child.output.size)) = evm.memory := by
      simp [memoryExtend_zero, memoryWrite]
    rw [hmem] at hat'
    have hk : Known code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) size facts
        (gas - (callCost fork asked gas
          (decide (toAddressMasked to ∉ evm.substate.accessedAddresses)) + 0) + child.gas)
        (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
        final :=
      ⟨by rw [hat'.2.2.2.2.2.1]; exact hat', by rw [hat'.2.2.2.2.2.1]; exact hsize, hmod,
        by rw [hat'.2.2.2.2.2.1]; exact hall⟩
    rw [Nat.add_zero] at hk
    have hagree' := hpre_agree.trans heff.agrees
    refine ⟨decide (toAddressMasked to ∉ evm.substate.accessedAddresses), child.gas,
      (incorporateChild fork caller child).state,
      (incorporateChild fork caller child).substate.accessedStorageKeys, le_of_le_of_eq hle hmg, ?_,
      ?_⟩
    · cases hok : child.error.isNone
      · simp only [hok] at hagree'
        exact hagree'.mono fun slot hs => List.mem_append_right _ (by simpa using hs)
      · simp only [hok, ite_true] at hagree'
        exact hagree'
    · cases hok : child.error.isNone
      · refine .inr ⟨?_, stored_of_known (by simpa [hok] using hk) ?_ ?_ (Agrees.refl _ _ _)⟩
        · cases sure
          · rfl
          · simp [hsure rfl] at hok
        · intro fact hfact
          exact (hpre_slots fact hfact).of_agrees (touched := [])
            (by simpa [hok] using heff.agrees) fun _ hs => by cases hs
        · rw [heff.refund, hok, hcss]
          simp [hrefund]
      · refine .inl (stored_of_known (by simpa [hok] using hk) ?_ ?_ (Agrees.refl _ _ _))
        · intro fact hfact
          rcases List.mem_append.mp hfact with hfact | hfact
          · exact heff.holds hok fact hfact
          · obtain ⟨hmem, hnot⟩ := List.mem_filter.mp hfact
            exact (hpre_slots fact hmem).of_agrees (by simpa [hok] using heff.agrees)
              (untouched_of_not_mem (by simpa using hnot))
        · rw [heff.refund, hok, hcss]
          simp [hrefund]
  · exact ⟨final, hreach, .inr aborted⟩

end EthLib.Execution.Evm.Logic
