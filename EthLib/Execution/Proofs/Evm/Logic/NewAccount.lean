module

public import EthLib.Execution.Proofs.Evm.Logic.Effect
public import EthLib.Execution.Proofs.Evm.Logic.Create

/-!
# Proofs: creations from frames that know slots

A frame that knows a few slots of storage can create an account, and go on knowing them.

The rules here hold from Berlin to the fork before Glamsterdam, with one counter of gas.

The init code is the bytes of a fact of memory, so the creation grows no memory.

The creator pays 32000, and from Shanghai 2 gas per word of init code, by EIP-3860.

CREATE2 also pays 6 gas per word to hash the init code, by EIP-1014.

The new address is the one that the specification derives from the base state.

It must hold no code and a nonce of 0 in the base state, as EIP-684 asks.

The nonce of the creator grows by one, whatever the creation does.

The creation passes on all but one 64th of the gas left, by EIP-150.

The init code is arbitrary, so the rule takes an effect of the frame that ends the creation.

That effect may remake accounts, such as the new one, and give facts of accounts.

- On success the frame pushes the new address and knows the facts that the effect gives.
- It adds the refund of the effect, and the new base holds the balances and the accounts of it.
- Its return data is then empty.
- The new base gives the creator the grown nonce, unless the effect remakes the creator.
- On failure the frame pushes 0, and keeps its facts of slots and its refund counter.
- The new base then gives the creator the grown nonce.
- Either way, memory keeps every fact.
- Either way, the new base agrees with the old one outside the touched slots and those of the facts.
- It also agrees outside the addresses that the effect moves or remakes, and the creator.

Out of scope: a creation that runs no message or runs in a static frame.

The rule says nothing of the return data after a failure.

Sources: EIP-150, EIP-684, EIP-1014, EIP-2929 and EIP-3860.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 Address Bytes32)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- The nonce of an account that has the nonce and the code hash of an account that exists. -/
theorem nonce_of_shape {state state' : TransactionState} {address : Address}
    {account : State.Account}
    (h : (state'.getAccountOptional address).map nonceAndCode =
      (state.getAccountOptional address).map nonceAndCode)
    (hsome : state.getAccountOptional address = some account) :
    (state'.getAccount address).nonce = account.nonce := by
  rw [hsome] at h
  cases hs : state'.getAccountOptional address with
  | none => simp [hs] at h
  | some account' =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq, nonceAndCode, Prod.mk.injEq] at h
    simp [TransactionState.getAccount, hs, h.1]

/-- The message that a creation sends from a frame, to run the init code `init` at `address`.

It sends from the current account with the value `value` and the gas `gas`.

It has no target and no data, and it is one deeper than the frame and not static. -/
def CreateMessage (message : Message fork) (address : Address) (init : ByteArray) (value : U256)
    (gas : Nat) (msg : Message fork) : Prop :=
  msg.gas = gas ∧ msg.caller = message.currentTarget ∧ msg.target = none ∧
    msg.currentTarget = address ∧ msg.codeAddress = none ∧ msg.code = init ∧
    msg.data = .empty ∧ msg.value = value ∧ msg.depth = message.depth + 1 ∧
    msg.isStatic = false

/-- A frame of a creation that paid `cost`, after its message, with a gas, its facts and a base.

The creator had the nonce `nonce` in the old base.

The creation succeeded, or it failed and `sure` is false.

On success the frame pushes `address`, knows the facts of the effect, and adds its refund.

The new base then holds the balances and the accounts of the change.

It also gives the creator the grown nonce, unless the change remakes the creator.

The return data is then empty.

On failure the frame pushes 0 and keeps its facts of slots and its refund counter.

The new base then gives the creator the grown nonce.

Memory keeps every fact. -/
def AfterCreate (code : ByteArray) (message : Message fork) (pc : Nat) (rest : List U256)
    (size : Nat) (facts : List (Nat × ByteArray)) (gas cost : Nat) (address : Address)
    (nonce : Nat) (slots : List SlotFact) (refund : Int) (base : TransactionState)
    (accessed : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)) (change : Change) (sure : Bool)
    (evm : Evm fork Nat) : Prop :=
  ∃ left base' accessed', left ≤ createMessageGas fork (gas - cost) ∧
    Agrees (change.touched ++ slots.map SlotFact.slot) change.moved
      (change.remade ++ [message.currentTarget]) base accessed base' accessed' ∧
    (((∀ fund ∈ change.funds, (base'.getAccount fund.1).balance = fund.2) ∧
      (∀ fact ∈ change.accounts, fact.Holds base') ∧
      (message.currentTarget ∉ change.remade →
        (base'.getAccount message.currentTarget).nonce = nonce + 1) ∧ evm.returnData = .empty ∧
      Stored code message (pc + 1) (address.toU256 :: rest) size facts
        (gas - cost - createMessageGas fork (gas - cost) + left)
        (change.after ++ keptFacts change.touched slots) (refund + change.gain) base' accessed'
        evm) ∨
      sure = false ∧ (base'.getAccount message.currentTarget).nonce = nonce + 1 ∧
        Stored code message (pc + 1) (0 :: rest) size facts
          (gas - cost - createMessageGas fork (gas - cost) + left) slots refund base' accessed'
          evm)

variable {code : ByteArray} {message : Message fork} {pc : Nat} {size : Nat}
  {facts : List (Nat × ByteArray)} {gas : Nat} {slots : List SlotFact} {refund : Int}
  {base : TransactionState} {accessed : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)}

/-- Once the nonce of the creator grows, the state agrees with the one before outside the creator.

The creator then has its account from before, with the grown nonce.

The reads of the creator and of the new address change nothing that agreement sees. -/
private theorem agrees_incrementNonce {state caller : TransactionState} {address : Address}
    (keys : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32))
    (hinc : ((state.recordAccountRead message.currentTarget).recordAccountRead
      address).incrementNonce fork message.currentTarget = .ok caller) :
    Agrees [] [] [message.currentTarget] state keys caller keys ∧
      caller.getAccountOptional message.currentTarget =
        some { state.getAccount message.currentTarget with
          nonce := (state.getAccount message.currentTarget).nonce + 1 } := by
  have hread : Agrees [] [] [] state keys
      ((state.recordAccountRead message.currentTarget).recordAccountRead address) keys :=
    ⟨fun _ _ _ => rfl, fun _ _ _ => .rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      rfl⟩
  obtain ⟨h, hself, -⟩ := agrees_modifyState keys (account :=
      { state.getAccount message.currentTarget with
        nonce := (state.getAccount message.currentTarget).nonce + 1 })
    rfl (fun ⟨hn, _⟩ => by simp at hn) hinc
  exact ⟨(hread.trans h).mono (fun _ hs => by simp at hs) (fun _ hm => by simp at hm)
    fun _ hm => by simpa using hm, hself⟩

/-- The frame after a creation, from the frame that it resumes with the effect of its callee. -/
private theorem afterCreate_of_at {evm caller child final : Evm fork Nat} {rest : List U256}
    {cost : Nat} {address : Address} {change : Change} {sure : Bool}
    (hsize : evm.memory.size = size) (hmod : size % 32 = 0) (hall : HoldsAll evm.memory facts)
    (hrefund : evm.substate.refundCounter = refund)
    (hslots : ∀ fact ∈ slots, fact.Holds caller.state caller.substate)
    (hagree : Agrees (slots.map SlotFact.slot) [] [message.currentTarget] base accessed
      caller.state caller.substate.accessedStorageKeys)
    (hself : caller.state.getAccountOptional message.currentTarget =
      some { base.getAccount message.currentTarget with
        nonce := (base.getAccount message.currentTarget).nonce + 1 })
    (hcss : caller.substate.refundCounter = evm.substate.refundCounter)
    (hle : child.gas ≤ createMessageGas fork (gas - cost))
    (heff : Effects change caller child) (hsure : sure = true → child.error = none)
    (hat : At code message (pc + 1)
      ((if child.error.isNone then address.toU256 else 0) :: rest) evm.memory
      (gas - cost - createMessageGas fork (gas - cost) + child.gas)
      (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
      final ∧ final.returnData = if child.error.isNone then .empty else child.output) :
    AfterCreate code message pc rest size facts gas cost address
      (base.getAccount message.currentTarget).nonce slots refund base accessed change sure
      final := by
  have hm := hat.1.2.2.2.2.2.1
  have hk : Known code message (pc + 1)
      ((if child.error.isNone then address.toU256 else 0) :: rest) size facts
      (gas - cost - createMessageGas fork (gas - cost) + child.gas)
      (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
      final := ⟨by rw [hm]; exact hat.1, by rw [hm, hsize], hmod, by rw [hm]; exact hall⟩
  have hagree' := hagree.trans heff.agrees
  have hnonce : message.currentTarget ∉ (if child.error.isNone then change.remade else []) →
      ((incorporateChild fork caller child).state.getAccount message.currentTarget).nonce =
        (base.getAccount message.currentTarget).nonce + 1 :=
    fun hr => nonce_of_shape (heff.agrees.shape _ hr) hself
  refine ⟨child.gas, (incorporateChild fork caller child).state,
    (incorporateChild fork caller child).substate.accessedStorageKeys, hle, ?_, ?_⟩
  · cases hok : child.error.isNone
    · simp only [hok, Bool.false_eq_true, ite_false] at hagree'
      exact hagree'.mono (fun slot hs => List.mem_append_right _ (by simpa using hs))
        (fun address hm => by simp at hm) fun address hm => by simp_all
    · simp only [hok, ite_true] at hagree'
      exact hagree'.mono (fun _ hs => hs) (fun address hm => by simpa using hm)
        fun address hm => hm
  · cases hok : child.error.isNone
    · simp only [hok, Bool.false_eq_true, ite_false] at hk hnonce
      refine .inr ⟨?_, hnonce List.not_mem_nil, stored_of_known hk ?_ ?_ (Agrees.refl _ _ _ _ _)⟩
      · cases sure
        · rfl
        · simp [hsure rfl] at hok
      · intro fact hfact
        exact (hslots fact hfact).of_agrees (touched := [])
          (by simpa [hok] using heff.agrees) fun _ hs => by cases hs
      · rw [heff.refund, hok, hcss]
        simp [hrefund]
    · simp only [hok, ite_true] at hk hnonce
      refine .inl ⟨heff.funds hok, heff.accounts hok, hnonce, by simp [hat.2, hok],
        stored_of_known hk ?_ ?_ (Agrees.refl _ _ _ _ _)⟩
      · intro fact hfact
        rcases List.mem_append.mp hfact with hfact | hfact
        · exact heff.holds hok fact hfact
        · obtain ⟨hmem, hnot⟩ := List.mem_filter.mp hfact
          exact (hslots fact hmem).of_agrees (by simpa [hok] using heff.agrees)
            (untouched_of_not_mem (by simpa using hnot))
      · rw [heff.refund, hok, hcss]
        simp [hrefund]

/-- From Berlin to before Glamsterdam, CREATE, or CREATE2 with a salt, from a frame of slots.

The byte at `pc` runs the creation, which sends a message.

The frame may change the state, and its account holds the value in the base state.

Its nonce in the base state is not the greatest, and its depth leaves room for one more frame.

The init code is the bytes `init` of a fact of memory, of the size on the stack.

From Shanghai, it is at most the greatest size, by EIP-3860.

The new address is the one that the specification derives from the base state.

It holds no code and a nonce of 0 in the base state.

The frame needs the price of the creation.

Each frame that ends the message has the effect, by the assumption `callee`.

The assumption may use the facts of the slots and the agreement of the creator with the base.

It may also use the account of the creator, which is that of the base with the grown nonce.

When `sure` is true, it says that such a frame ends with no error.

The frame after the creation is then one of `AfterCreate`, with the gas that the callee leaves. -/
theorem createKind_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {create2 : Bool} {byte : UInt8} {op : Op}
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {value start len salt : U256} {rest : List U256} {init : ByteArray} {address : Address}
    {change : Change} {sure : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hnone : instruction (Meter := Nat) fork op = none)
    (hrun : messageInstruction (Meter := Nat) fork op = some (createStep create2))
    (hstatic : message.isStatic = false)
    (hinput : (start.toNat, init) ∈ facts) (hlen : init.size = len.toNat)
    (hinit : .shapella ≤ fork → len.toNat ≤ maxInitCodeSize fork)
    (hbal : value ≤ (base.getAccount message.currentTarget).balance)
    (hnonce : (base.getAccount message.currentTarget).nonce ≠ MAX_NONCE)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (haddr : creationAddress message.currentTarget (base.getAccount message.currentTarget).nonce
      (if create2 then some salt else none) init = .ok address)
    (hdeploy : base.accountDeployable address = true)
    (hgas : createBaseCost fork +
        (if create2 then OPCODE_KECCAK256_PER_WORD * wordCount len.toNat else 0) +
        (if fork ≥ .shapella then initCodeCost len.toNat else 0) ≤ gas)
    (heffect : ∀ caller msg child, callee caller msg child →
      CreateMessage message address init value (createMessageGas fork (gas -
        (createBaseCost fork +
          (if create2 then OPCODE_KECCAK256_PER_WORD * wordCount len.toNat else 0) +
          (if fork ≥ .shapella then initCodeCost len.toNat else 0)))) msg →
      (∀ fact ∈ slots, fact.Holds caller.state caller.substate) →
      Agrees (slots.map SlotFact.slot) [] [message.currentTarget] base accessed caller.state
        caller.substate.accessedStorageKeys →
      caller.state.getAccountOptional message.currentTarget =
        some { base.getAccount message.currentTarget with
          nonce := (base.getAccount message.currentTarget).nonce + 1 } →
      Effects change caller child ∧ (sure = true → child.error = none)) :
    HoareUnder fork callee
      (Stored code message pc (value :: start :: len :: ((if create2 then [salt] else []) ++ rest))
        size facts gas slots refund base accessed)
      (AfterCreate code message pc rest size facts gas
        (createBaseCost fork +
          (if create2 then OPCODE_KECCAK256_PER_WORD * wordCount len.toNat else 0) +
          (if fork ≥ .shapella then initCodeCost len.toNat else 0))
        address (base.getAccount message.currentTarget).nonce slots refund base accessed change
        sure) := by
  intro bound runChild meets evm ⟨⟨hat, hsize, hmod, hall⟩, hslots, hrefund, hagree⟩ within
  have hold := hall _ hinput
  have hext : extendMemory evm.memory.size [(start, len)] = ⟨0, 0⟩ :=
    extendMemory_eq_zero _ _ fun p hp => by
      rw [List.mem_singleton.mp hp]
      refine .inr (ceil32_le (ceil32_mod _) (Nat.le_trans ?_ (le_ceil32 _)))
      rw [← hlen]
      exact hold.1
  have hread : memoryReadBytes (memoryExtend evm.memory
      (extendMemory evm.memory.size [(start, len)]).expandBy) start.toNat len.toNat = init := by
    rw [hext, memoryExtend_zero, ← hlen, hold.2]
  have hget : ∀ a, evm.state.getAccount a = base.getAccount a :=
    fun a => hagree.getAccount List.not_mem_nil List.not_mem_nil
  have hdeploy' : evm.state.accountDeployable address = true := by
    unfold TransactionState.accountDeployable
    rw [hget]
    exact hdeploy
  have hcreate := createKindWith (callee := callee) (create2 := create2) (value := value)
    (start := start) (size := len) (salt := salt) (rest := rest) (address := address)
    (memory := evm.memory) (gas := gas) (state := evm.state) (substate := evm.substate)
    hfork hglam hlt hbyte decoded hnone hrun hstatic hinit (by rw [hget]; exact hbal)
    (by rw [hget]; exact hnonce) hdepth (by rw [hread, hget]; exact haddr) hdeploy'
    (by rw [hext]; exact hgas)
  rw [hread, hext, memoryExtend_zero] at hcreate
  dsimp only [Nat.add_zero] at hcreate
  obtain ⟨final, hreach, hq | aborted⟩ := hcreate bound runChild meets evm hat within
  · refine ⟨final, hreach, .inl ?_⟩
    obtain ⟨caller, msg, child, hc, hle, hinc, hcss, hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv,
      hmdep, hmst, hat'⟩ := hq
    obtain ⟨hstate, hself⟩ := agrees_incrementNonce evm.substate.accessedStorageKeys hinc
    rw [hget] at hself
    have hsame : Agrees [] [] [message.currentTarget] evm.state
        evm.substate.accessedStorageKeys caller.state caller.substate.accessedStorageKeys := by
      rw [hcss]
      exact hstate
    have hpre_agree : Agrees (slots.map SlotFact.slot) [] [message.currentTarget] base accessed
        caller.state caller.substate.accessedStorageKeys :=
      (hagree.trans hsame).mono (fun _ hs => by simpa using hs) (fun _ hm => by simp at hm)
        fun _ hm => by simpa using hm
    have hpre_slots : ∀ fact ∈ slots, fact.Holds caller.state caller.substate :=
      fun fact hfact => (hslots fact hfact).of_agrees hsame fun _ hs => by cases hs
    obtain ⟨heff, hsure⟩ := heffect caller msg child hc
      ⟨hmg, hmc, hmt, hmtg, hmca, hmcode, hmd, hmv, hmdep, hmst⟩ hpre_slots hpre_agree hself
    exact afterCreate_of_at hsize hmod hall hrefund hpre_slots hpre_agree hself
      (by rw [hcss]) (le_of_le_of_eq hle hmg) heff hsure hat'
  · exact ⟨final, hreach, .inr aborted⟩

/-- From Berlin to before Glamsterdam, CREATE of the init code in a fact, from a frame of slots.

The new address is the one that the specification derives from the creator and its nonce.

The rest is as for every creation. -/
theorem create_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {value start len : U256} {rest : List U256} {init : ByteArray} {address : Address}
    {change : Change} {sure : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf0)
    (hstatic : message.isStatic = false)
    (hinput : (start.toNat, init) ∈ facts) (hlen : init.size = len.toNat)
    (hinit : .shapella ≤ fork → len.toNat ≤ maxInitCodeSize fork)
    (hbal : value ≤ (base.getAccount message.currentTarget).balance)
    (hnonce : (base.getAccount message.currentTarget).nonce ≠ MAX_NONCE)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (haddr : creationAddress message.currentTarget (base.getAccount message.currentTarget).nonce
      none init = .ok address)
    (hdeploy : base.accountDeployable address = true)
    (hgas : createBaseCost fork + (if fork ≥ .shapella then initCodeCost len.toNat else 0) ≤ gas)
    (heffect : ∀ caller msg child, callee caller msg child →
      CreateMessage message address init value (createMessageGas fork (gas -
        (createBaseCost fork + (if fork ≥ .shapella then initCodeCost len.toNat else 0)))) msg →
      (∀ fact ∈ slots, fact.Holds caller.state caller.substate) →
      Agrees (slots.map SlotFact.slot) [] [message.currentTarget] base accessed caller.state
        caller.substate.accessedStorageKeys →
      caller.state.getAccountOptional message.currentTarget =
        some { base.getAccount message.currentTarget with
          nonce := (base.getAccount message.currentTarget).nonce + 1 } →
      Effects change caller child ∧ (sure = true → child.error = none)) :
    HoareUnder fork callee
      (Stored code message pc (value :: start :: len :: rest) size facts gas slots refund base
        accessed)
      (AfterCreate code message pc rest size facts gas
        (createBaseCost fork + (if fork ≥ .shapella then initCodeCost len.toNat else 0))
        address (base.getAccount message.currentTarget).nonce slots refund base accessed change
        sure) :=
  createKind_stored (create2 := false) (salt := 0) hfork hglam hlt hbyte
    (ofByte_of_decode (op := .create) rfl (Fork.frontier_le _)) instruction_create
    messageInstruction_create hstatic hinput hlen hinit hbal hnonce hdepth haddr hdeploy hgas
    heffect

/-- From Berlin to before Glamsterdam, CREATE2 with the salt `salt`, from a frame of slots.

The init code is the bytes of a fact of memory.

The new address is the one that the specification derives from the creator, the salt and the code.

The rest is as for every creation. -/
theorem create2_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {value start len salt : U256} {rest : List U256} {init : ByteArray} {address : Address}
    {change : Change} {sure : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf5)
    (hstatic : message.isStatic = false)
    (hinput : (start.toNat, init) ∈ facts) (hlen : init.size = len.toNat)
    (hinit : .shapella ≤ fork → len.toNat ≤ maxInitCodeSize fork)
    (hbal : value ≤ (base.getAccount message.currentTarget).balance)
    (hnonce : (base.getAccount message.currentTarget).nonce ≠ MAX_NONCE)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (haddr : creationAddress message.currentTarget (base.getAccount message.currentTarget).nonce
      (some salt) init = .ok address)
    (hdeploy : base.accountDeployable address = true)
    (hgas : createBaseCost fork + OPCODE_KECCAK256_PER_WORD * wordCount len.toNat +
        (if fork ≥ .shapella then initCodeCost len.toNat else 0) ≤ gas)
    (heffect : ∀ caller msg child, callee caller msg child →
      CreateMessage message address init value (createMessageGas fork (gas -
        (createBaseCost fork + OPCODE_KECCAK256_PER_WORD * wordCount len.toNat +
          (if fork ≥ .shapella then initCodeCost len.toNat else 0)))) msg →
      (∀ fact ∈ slots, fact.Holds caller.state caller.substate) →
      Agrees (slots.map SlotFact.slot) [] [message.currentTarget] base accessed caller.state
        caller.substate.accessedStorageKeys →
      caller.state.getAccountOptional message.currentTarget =
        some { base.getAccount message.currentTarget with
          nonce := (base.getAccount message.currentTarget).nonce + 1 } →
      Effects change caller child ∧ (sure = true → child.error = none)) :
    HoareUnder fork callee
      (Stored code message pc (value :: start :: len :: salt :: rest) size facts gas slots refund
        base accessed)
      (AfterCreate code message pc rest size facts gas
        (createBaseCost fork + OPCODE_KECCAK256_PER_WORD * wordCount len.toNat +
          (if fork ≥ .shapella then initCodeCost len.toNat else 0))
        address (base.getAccount message.currentTarget).nonce slots refund base accessed change
        sure) :=
  createKind_stored (create2 := true) hfork hglam hlt hbyte
    (ofByte_of_decode (op := .create2) rfl (Nat.le_trans (by decide) hfork)) instruction_create2
    (messageInstruction_create2 (Nat.le_trans (by decide) hfork)) hstatic hinput hlen hinit hbal
    hnonce hdepth haddr hdeploy hgas heffect

end EthLib.Execution.Evm.Logic
