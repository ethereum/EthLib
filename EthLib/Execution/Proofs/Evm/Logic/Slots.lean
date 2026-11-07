module

public import EthLib.Execution.Proofs.Evm.Logic.Known
public import EthLib.Execution.Proofs.Evm.Logic.Copy
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: frames that know a few slots of storage

A specification often cares about a few slots of storage, not about the rest.

A fact of a slot gives its account, its key, its word before the transaction, and its word now.

It also says whether the slot is warm.

A slot is warm when the transaction has accessed it, by EIP-2929.

A frame of this kind knows ranges of memory, the facts of some slots, and the refund counter.

It agrees with a base state and a base set of accessed keys at every slot that no fact names.

There it reads the words of the base state, and it is warm exactly when the base set holds it.

It also has the words before the transaction, the accounts, the codes and the block of the base.

Agreement in general may leave out the accounts of some addresses, whose balances may move.

Each of those still exists exactly when it does in the base, with its nonce and its code hash.

It may also leave out the accounts of other addresses, which may change in every way.

Every other account still exists exactly when it does in the base, with its nonce and its code.

- A rule that keeps the state and the substate, for every state and substate, keeps every fact.
- From Berlin, SLOAD of the key of a fact of the account of the frame pushes its word now.
- It makes the slot warm, and pays 2100 for a cold slot and 100 for a warm one.
- From Berlin to before Glamsterdam, SSTORE to the key of such a fact writes it and makes it warm.
- It needs a frame that may change the state, more than 2300 gas, and its account in the base state.
- It pays the price of EIP-2200 with the prices of EIP-2929, from the facts of the slot.
- It adds the refund of the write, from the same facts, to the refund counter.
- From Byzantium, RETURNDATASIZE of a frame that holds some return data pushes its size.
- RETURNDATACOPY of a range within that return data writes its bytes as a fact of memory.
- Both keep the return data and every fact of a slot.
- A rule that halts and keeps the state and the substate keeps every fact in the halted frame.

These frames say nothing of the logs, the accessed addresses and the other fields of the substate.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 Address Bytes32 Hash32)
open EthLib.Execution.State (TransactionState Account)
open GasCosts

variable {fork : Fork}

/-- What a frame knows of one slot of storage. -/
structure SlotFact where
  /-- The account of the slot. -/
  address : Address
  /-- The key of the slot. -/
  key : U256
  /-- The word of the slot before the transaction. -/
  original : U256
  /-- The word of the slot now. -/
  current : U256
  /-- Whether the transaction has accessed the slot. -/
  warm : Bool

/-- The account and the key of the slot of a fact. -/
def SlotFact.slot (fact : SlotFact) : Address × U256 := (fact.address, fact.key)

/-- The state and the substate agree with a fact of a slot. -/
def SlotFact.Holds (fact : SlotFact) (state : TransactionState) (substate : Substate) : Prop :=
  state.getStorageOriginal fact.address (U256.toBeBytes fact.key) = fact.original ∧
    state.getStorage fact.address (U256.toBeBytes fact.key) = fact.current ∧
    decide (U256.toBeBytes fact.key ∈ substate.accessedStorageKeys.getD fact.address ∅) =
      fact.warm

/-- No slot of the list is the slot at `key` of `address`. -/
def Untouched (touched : List (Address × U256)) (address : Address) (key : Bytes32) : Prop :=
  ∀ slot ∈ touched, slot.1 ≠ address ∨ U256.toBeBytes slot.2 ≠ key

/-- The nonce and the code hash of an account, which are all of it but its balance. -/
def nonceAndCode (account : Account) : Nat × Hash32 := (account.nonce, account.codeHash)

/-- A state and its accessed keys agree with a base state and base keys outside some slots.

Outside the slots of `touched`, each word reads as in `base`, and is warm when `accessed` holds it.

Outside the addresses of `moved` and of `remade`, each account is that of `base`.

Outside the addresses of `remade`, the account exists exactly when it does in `base`.

There it has the nonce and the code hash of `base`, and the code of `base`.

The words before the transaction and the block are those of `base`. -/
structure Agrees (touched : List (Address × U256)) (moved remade : List Address)
    (base : TransactionState) (accessed : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32))
    (state : TransactionState) (keys : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)) :
    Prop where
  /-- Each word outside the slots reads as in the base state. -/
  storage : ∀ address key, Untouched touched address key →
    state.getStorage address key = base.getStorage address key
  /-- Each slot outside the slots is warm when the base keys hold it. -/
  warm : ∀ address key, Untouched touched address key →
    (key ∈ keys.getD address ∅ ↔ key ∈ accessed.getD address ∅)
  /-- The words before the transaction are those of the base state. -/
  original : state.getStorageOriginal = base.getStorageOriginal
  /-- The accounts outside the moved and the remade addresses are those of the base state. -/
  account : ∀ address, address ∉ moved → address ∉ remade →
    state.getAccountOptional address = base.getAccountOptional address
  /-- Outside the remade addresses, an account has the nonce and the code hash of the base.

  Or it is missing in both. -/
  shape : ∀ address, address ∉ remade → (state.getAccountOptional address).map nonceAndCode =
    (base.getAccountOptional address).map nonceAndCode
  /-- Outside the remade addresses, an account has the code of the base state. -/
  code : ∀ address, address ∉ remade → state.getCode (state.getAccount address).codeHash =
    base.getCode (base.getAccount address).codeHash
  /-- The block is that of the base state. -/
  parent : state.parent = base.parent

namespace Agrees

variable {touched touched' : List (Address × U256)} {moved moved' remade remade' : List Address}
  {base state state' : TransactionState}
  {accessed keys keys' : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)}

/-- A state agrees with itself outside every list of slots and of addresses. -/
theorem refl (touched : List (Address × U256)) (moved remade : List Address)
    (state : TransactionState) (keys : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)) :
    Agrees touched moved remade state keys state keys :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => .rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    rfl⟩

/-- Agreement holds outside lists that contain the first ones. -/
theorem mono (h : Agrees touched moved remade base accessed state keys)
    (sub : ∀ slot ∈ touched, slot ∈ touched') (subMoved : ∀ address ∈ moved, address ∈ moved')
    (subRemade : ∀ address ∈ remade, address ∈ remade') :
    Agrees touched' moved' remade' base accessed state keys :=
  ⟨fun address key hu => h.storage address key fun slot hs => hu slot (sub slot hs),
    fun address key hu => h.warm address key fun slot hs => hu slot (sub slot hs),
    h.original,
    fun address hm hr => h.account address (fun hm' => hm (subMoved address hm'))
      fun hr' => hr (subRemade address hr'),
    fun address hr => h.shape address fun hr' => hr (subRemade address hr'),
    fun address hr => h.code address fun hr' => hr (subRemade address hr'), h.parent⟩

/-- Agreement composes, outside both lists of slots and both lists of addresses of each kind. -/
theorem trans (h : Agrees touched moved remade base accessed state keys)
    (h' : Agrees touched' moved' remade' state keys state' keys') :
    Agrees (touched' ++ touched) (moved' ++ moved) (remade' ++ remade) base accessed state'
      keys' := by
  have left : ∀ {address key}, Untouched (touched' ++ touched) address key →
      Untouched touched' address key := fun hu slot hs => hu slot (List.mem_append_left _ hs)
  have right : ∀ {address key}, Untouched (touched' ++ touched) address key →
      Untouched touched address key := fun hu slot hs => hu slot (List.mem_append_right _ hs)
  exact ⟨fun address key hu => (h'.storage address key (left hu)).trans
      (h.storage address key (right hu)),
    fun address key hu => (h'.warm address key (left hu)).trans (h.warm address key (right hu)),
    h'.original.trans h.original,
    fun address hm hr => (h'.account address (fun hm' => hm (List.mem_append_left _ hm'))
        fun hr' => hr (List.mem_append_left _ hr')).trans
      (h.account address (fun hm' => hm (List.mem_append_right _ hm'))
        fun hr' => hr (List.mem_append_right _ hr')),
    fun address hr => (h'.shape address fun hr' => hr (List.mem_append_left _ hr')).trans
      (h.shape address fun hr' => hr (List.mem_append_right _ hr')),
    fun address hr => (h'.code address fun hr' => hr (List.mem_append_left _ hr')).trans
      (h.code address fun hr' => hr (List.mem_append_right _ hr')),
    h'.parent.trans h.parent⟩

/-- Outside the remade addresses, an account exists exactly when it does in the base state. -/
theorem isSome (h : Agrees touched moved remade base accessed state keys) {address : Address}
    (hr : address ∉ remade) :
    (state.getAccountOptional address).isSome = (base.getAccountOptional address).isSome := by
  have := congrArg Option.isSome (h.shape address hr)
  simpa using this

/-- Outside the remade addresses, an account has the code hash of the base state. -/
theorem codeHash (h : Agrees touched moved remade base accessed state keys) {address : Address}
    (hr : address ∉ remade) :
    (state.getAccount address).codeHash = (base.getAccount address).codeHash := by
  have := h.shape address hr
  unfold TransactionState.getAccount
  cases hs : state.getAccountOptional address <;> cases hb : base.getAccountOptional address <;>
    simp_all [nonceAndCode]

/-- Outside the moved and the remade addresses, an account is that of the base state. -/
theorem getAccount (h : Agrees touched moved remade base accessed state keys) {address : Address}
    (hm : address ∉ moved) (hr : address ∉ remade) :
    state.getAccount address = base.getAccount address := by
  rw [TransactionState.getAccount, h.account address hm hr, TransactionState.getAccount]

end Agrees

/-- A frame that knows ranges of memory, the facts of some slots and the refund counter.

Outside the slots of the facts, it agrees with the base state `base` and the keys `accessed`. -/
def Stored (code : ByteArray) (message : Message fork) (pc : Nat) (stack : List U256)
    (size : Nat) (facts : List (Nat × ByteArray)) (gas : Nat) (slots : List SlotFact)
    (refund : Int) (base : TransactionState)
    (accessed : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)) (evm : Evm fork Nat) : Prop :=
  Known code message pc stack size facts gas evm.state evm.substate evm ∧
    (∀ fact ∈ slots, fact.Holds evm.state evm.substate) ∧
    evm.substate.refundCounter = refund ∧
    Agrees (slots.map SlotFact.slot) [] [] base accessed evm.state
      evm.substate.accessedStorageKeys

variable {code : ByteArray} {message : Message fork} {pc pc' : Nat} {stack stack' : List U256}
  {size size' : Nat} {facts facts' : List (Nat × ByteArray)} {gas gas' : Nat}
  {slots : List SlotFact} {refund : Int} {base : TransactionState}
  {accessed : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)}

/-- A frame that is known, with the facts of its slots, the refund counter and the agreement. -/
theorem stored_of_known {evm : Evm fork Nat} {state : TransactionState} {substate : Substate}
    (h : Known code message pc stack size facts gas state substate evm)
    (hslots : ∀ fact ∈ slots, fact.Holds state substate)
    (hrefund : substate.refundCounter = refund)
    (hagree : Agrees (slots.map SlotFact.slot) [] [] base accessed state
      substate.accessedStorageKeys) :
    Stored code message pc stack size facts gas slots refund base accessed evm := by
  have hs : evm.state = state := h.1.2.2.2.2.2.2.2.2.2.2.1
  have hss : evm.substate = substate := h.1.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨by rw [hs, hss]; exact h, by rw [hs, hss]; exact hslots, by rw [hss]; exact hrefund,
    by rw [hs, hss]; exact hagree⟩

/-- A rule that keeps the state and the substate, for every state and substate, keeps every fact. -/
theorem Stored.of_known
    (h : ∀ state substate, Hoare fork (Known code message pc stack size facts gas state substate)
      (Known code message pc' stack' size' facts' gas' state substate)) :
    Hoare fork (Stored code message pc stack size facts gas slots refund base accessed)
      (Stored code message pc' stack' size' facts' gas' slots refund base accessed) := by
  rintro evm ⟨hk, hslots, hrefund, hagree⟩
  obtain ⟨after, hreach, hk'⟩ := h evm.state evm.substate evm hk
  exact ⟨after, hreach, stored_of_known hk' hslots hrefund hagree⟩

/-- A rule that keeps memory, the state and the substate, for every one, keeps every fact. -/
theorem Stored.of_at
    (h : ∀ memory state substate, Hoare fork (At code message pc stack memory gas state substate)
      (At code message pc' stack' memory gas' state substate)) :
    Hoare fork (Stored code message pc stack size facts gas slots refund base accessed)
      (Stored code message pc' stack' size facts gas' slots refund base accessed) :=
  Stored.of_known fun state substate => Known.of_at fun memory => h memory state substate

/-- Two words with the same bytes are the same word. -/
theorem toBeBytes_inj {a b : U256} (h : U256.toBeBytes a = U256.toBeBytes b) : a = b := by
  rw [← U256.fromBeBytes_toBeBytes a, h, U256.fromBeBytes_toBeBytes]

/-- After the access of a slot of an address, a slot is accessed when it was, or is that one. -/
theorem mem_getD_insert (keys : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32))
    (address other : Address) (key slot : Bytes32) :
    slot ∈ (keys.insert address ((keys.getD address ∅).insert key)).getD other ∅ ↔
      (other = address ∧ slot = key) ∨ slot ∈ keys.getD other ∅ := by
  by_cases h : other = address
  · subst h
    simp only [Std.ExtTreeMap.getD_insert_self, Std.ExtTreeSet.mem_insert, true_and]
    constructor
    · rintro (h | h)
      · exact .inl (by simp_all)
      · exact .inr h
    · rintro (rfl | h)
      · exact .inl (by simp)
      · exact .inr h
  · simp [Std.ExtTreeMap.getD_insert, h, Ne.symm h]

/-- The facts of the slots after an access to one slot, whose fact becomes `fact'`.

The facts of the other slots stay. -/
def touch (fact' : SlotFact) (slots : List SlotFact) : List SlotFact :=
  fact' :: slots.filter fun fact => fact.slot ≠ fact'.slot

/-- Two facts of different slots name different accounts or different bytes of keys. -/
theorem SlotFact.ne_of_slot_ne {fact fact' : SlotFact} (h : fact.slot ≠ fact'.slot) :
    fact.address ≠ fact'.address ∨ U256.toBeBytes fact.key ≠ U256.toBeBytes fact'.key := by
  by_cases ha : fact.address = fact'.address
  · refine .inr fun hk => h ?_
    simp [SlotFact.slot, ha, toBeBytes_inj hk]
  · exact .inl ha

/-- After an access to the slot of `fact'`, the facts of the slots hold of the new state.

The new fact holds, and each fact of another slot that held before still holds. -/
theorem holds_touch {fact' : SlotFact} {state state' : TransactionState}
    {substate substate' : Substate} (hslots : ∀ fact ∈ slots, fact.Holds state substate)
    (hnew : fact'.Holds state' substate')
    (hother : ∀ fact ∈ slots, fact.slot ≠ fact'.slot → fact.Holds state substate →
      fact.Holds state' substate') :
    ∀ fact ∈ touch fact' slots, fact.Holds state' substate' := by
  intro fact hfact
  rcases List.mem_cons.mp hfact with rfl | hfact
  · exact hnew
  · obtain ⟨hmem, hne⟩ := List.mem_filter.mp hfact
    exact hother fact hmem (by simpa using hne) (hslots fact hmem)

/-- A slot outside the slots of the facts after an access is outside those before it.

It is not the slot of the access either. -/
theorem untouched_of_touch {fact' : SlotFact} {address : Address} {key : Bytes32}
    (h : Untouched ((touch fact' slots).map SlotFact.slot) address key) :
    (fact'.address ≠ address ∨ U256.toBeBytes fact'.key ≠ key) ∧
      Untouched (slots.map SlotFact.slot) address key := by
  have hhead := h fact'.slot (List.mem_map_of_mem (List.mem_cons_self ..))
  refine ⟨hhead, fun slot hs => ?_⟩
  obtain ⟨fact, hfact, rfl⟩ := List.mem_map.mp hs
  by_cases heq : fact.slot = fact'.slot
  · rw [heq]
    exact hhead
  · exact h fact.slot (List.mem_map_of_mem
      (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hfact, by simpa using heq⟩)))

/-- After an access to the slot of `fact'`, the state still agrees with the base.

The access changes only the word and the warmth of that slot. -/
theorem Agrees.touch {fact' : SlotFact} {moved remade : List Address}
    {state state' : TransactionState} {keys keys' : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)}
    (h : Agrees (slots.map SlotFact.slot) moved remade base accessed state keys)
    (hread : ∀ address key, fact'.address ≠ address ∨ U256.toBeBytes fact'.key ≠ key →
      state'.getStorage address key = state.getStorage address key)
    (hwarm : ∀ address key, fact'.address ≠ address ∨ U256.toBeBytes fact'.key ≠ key →
      (key ∈ keys'.getD address ∅ ↔ key ∈ keys.getD address ∅))
    (horiginal : state'.getStorageOriginal = state.getStorageOriginal)
    (haccount : ∀ address, state'.getAccountOptional address = state.getAccountOptional address)
    (hcode : ∀ hash, state'.getCode hash = state.getCode hash)
    (hparent : state'.parent = state.parent) :
    Agrees ((touch fact' slots).map SlotFact.slot) moved remade base accessed state' keys' :=
  ⟨fun address key hu => by
      obtain ⟨hhead, hrest⟩ := untouched_of_touch hu
      rw [hread address key hhead]
      exact h.storage address key hrest,
    fun address key hu => by
      obtain ⟨hhead, hrest⟩ := untouched_of_touch hu
      exact (hwarm address key hhead).trans (h.warm address key hrest),
    horiginal.trans h.original,
    fun address hm hr => (haccount address).trans (h.account address hm hr),
    fun address hr => by rw [haccount]; exact h.shape address hr,
    fun address hr => by
      rw [TransactionState.getAccount, haccount, hcode]
      exact h.code address hr,
    hparent.trans h.parent⟩

/-- From Berlin, SLOAD of the key of a fact of the account of the frame pushes its word now.

It makes the slot warm, and pays 2100 for a cold slot and 100 for a warm one, by EIP-2929. -/
theorem sload_stored (hfork : .berlin ≤ fork) {fact : SlotFact} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x54) (hfact : fact ∈ slots)
    (haddress : fact.address = message.currentTarget)
    (hgas : (if fact.warm then 100 else 2100) ≤ gas) :
    Hoare fork (Stored code message pc (fact.key :: rest) size facts gas slots refund base accessed)
      (Stored code message (pc + 1) (fact.current :: rest) size facts
        (gas - if fact.warm then 100 else 2100) (touch { fact with warm := true } slots) refund
        base accessed) := by
  rintro evm ⟨⟨hat, hsize, hmod, hall⟩, hslots, hrefund, hagree⟩
  obtain ⟨ho, hc, hw⟩ := hslots fact hfact
  rw [haddress] at ho hc hw
  have hprice : (if (!fact.warm) = true then 2100 else 100) = if fact.warm then 100 else 2100 := by
    cases fact.warm <;> rfl
  have hcold : decide (U256.toBeBytes fact.key ∉
      evm.substate.accessedStorageKeys.getD message.currentTarget ∅) = !fact.warm := by
    rw [← hw]
    simp
  obtain ⟨after, hreach, hat'⟩ :=
    sload hfork hlt hbyte hcold (by rw [hprice]; exact hgas) evm hat
  rw [hc, hprice] at hat'
  have hm := hat'.2.2.2.2.2.1
  refine ⟨after, hreach, stored_of_known
    (state := evm.state.recordStorageRead message.currentTarget (U256.toBeBytes fact.key))
    (substate := { evm.substate with
      accessedStorageKeys := evm.substate.accessedStorageKeys.insert message.currentTarget
        ((evm.substate.accessedStorageKeys.getD message.currentTarget ∅).insert
          (U256.toBeBytes fact.key)) })
    ⟨by rw [hm]; exact hat', by rw [hm]; exact hsize, hmod, by rw [hm]; exact hall⟩
    (holds_touch hslots ⟨by rw [haddress]; exact ho, by rw [haddress]; exact hc,
        by simp [haddress]⟩
      fun other _ hne hold => ⟨hold.1, hold.2.1, by
          rw [← hold.2.2]
          refine decide_eq_decide.mpr
            (mem_insert_getD_of_ne evm.substate (Or.imp Ne.symm Ne.symm ?_))
          rcases SlotFact.ne_of_slot_ne hne with h | h
          · exact .inl (by rw [← haddress]; exact Ne.symm h)
          · exact .inr (Ne.symm h)⟩) hrefund
    (hagree.touch (fun _ _ _ => rfl)
      (fun _ _ h => mem_insert_getD_of_ne evm.substate
        ((by rw [← haddress]; exact h : _ ∨ _).imp Ne.symm Ne.symm)) rfl (fun _ => rfl)
      (fun _ => rfl) rfl)⟩

/-- From Berlin to before Glamsterdam, SSTORE to the key of a fact of the account writes it.

It makes the slot warm.

The frame may change the state, and holds more than the stipend of 2300 gas, by EIP-2200.

The account of the frame exists in the base state.

It pays the price of the write from the facts of the slot, by EIP-2200 with the prices of EIP-2929.

It adds the refund of the write, from the same facts, to the refund counter. -/
theorem sstore_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {fact : SlotFact}
    {new : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x55)
    (hstatic : message.isStatic = false) (hfact : fact ∈ slots)
    (haddress : fact.address = message.currentTarget)
    (hbase : (base.getAccountOptional message.currentTarget).isSome = true)
    (hstipend : CALL_STIPEND < gas)
    (hgas : sstoreCost fork fact.original fact.current new (!fact.warm) ≤ gas) :
    Hoare fork
      (Stored code message pc (fact.key :: new :: rest) size facts gas slots refund base accessed)
      (Stored code message (pc + 1) rest size facts
        (gas - sstoreCost fork fact.original fact.current new (!fact.warm))
        (touch { fact with current := new, warm := true } slots)
        (refund + sstoreRefund fork fact.original fact.current new) base accessed) := by
  rintro evm ⟨⟨hat, hsize, hmod, hall⟩, hslots, hrefund, hagree⟩
  obtain ⟨ho, hc, hw⟩ := hslots fact hfact
  rw [haddress] at ho hc hw
  have hcold : decide (U256.toBeBytes fact.key ∉
      evm.substate.accessedStorageKeys.getD message.currentTarget ∅) = !fact.warm := by
    rw [← hw]
    simp
  have hacc : (evm.state.getAccountOptional message.currentTarget).isSome = true := by
    rw [hagree.isSome (List.not_mem_nil)]; exact hbase
  obtain ⟨state', hnew, hothers, horig, haccount, hcode, hparent, hrule⟩ := sstore_of_account
    hfork hglam hlt hbyte hstatic hcold hstipend (by rw [ho, hc]; exact hgas) hacc
  obtain ⟨after, hreach, hat'⟩ := hrule evm hat
  rw [ho, hc] at hat'
  have hm := hat'.2.2.2.2.2.1
  refine ⟨after, hreach, stored_of_known (state := state')
    (substate := { evm.substate with
      accessedStorageKeys := evm.substate.accessedStorageKeys.insert message.currentTarget
        ((evm.substate.accessedStorageKeys.getD message.currentTarget ∅).insert
          (U256.toBeBytes fact.key))
      refundCounter := evm.substate.refundCounter +
        sstoreRefund fork fact.original fact.current new })
    ⟨by rw [hm]; exact hat', by rw [hm]; exact hsize, hmod, by rw [hm]; exact hall⟩
    (holds_touch hslots ⟨by rw [haddress, horig]; exact ho, by rw [haddress]; exact hnew,
        by simp [haddress]⟩
      fun other _ hne hold => by
        have hne' : message.currentTarget ≠ other.address ∨
            U256.toBeBytes fact.key ≠ U256.toBeBytes other.key := by
          rcases SlotFact.ne_of_slot_ne hne with h | h
          · exact .inl (by rw [← haddress]; exact Ne.symm h)
          · exact .inr (Ne.symm h)
        refine ⟨by rw [horig]; exact hold.1, ?_, ?_⟩
        · rw [hothers _ _ (hne'.imp Ne.symm Ne.symm)]
          exact hold.2.1
        · rw [← hold.2.2]
          exact decide_eq_decide.mpr
            (mem_insert_getD_of_ne evm.substate (hne'.imp Ne.symm Ne.symm)))
    (by rw [← hrefund])
    (hagree.touch (fun address key h => hothers address key (by
        rw [← haddress]; exact h.imp Ne.symm Ne.symm))
      (fun _ _ h => mem_insert_getD_of_ne evm.substate
        ((by rw [← haddress]; exact h : _ ∨ _).imp Ne.symm Ne.symm))
      horig haccount hcode hparent)⟩

/-- From Byzantium, RETURNDATASIZE pushes the size of the return data `data`, for 2 gas.

The frame keeps the return data and every fact. -/
theorem returndatasize_stored (hfork : .byzantium ≤ fork) {data : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3d) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork
      (fun evm => Stored code message pc stack size facts gas slots refund base accessed evm ∧
        evm.returnData = data)
      (fun evm => Stored code message (pc + 1) (BitVec.ofNat 256 data.size :: stack) size facts
        (gas - 2) slots refund base accessed evm ∧ evm.returnData = data) := by
  rintro evm ⟨⟨⟨hat, hsize, hmod, hall⟩, hslots, hrefund, hagree⟩, hrd⟩
  obtain ⟨after, hreach, hat', hrd'⟩ := returndatasize hfork hlt hbyte hgas hstack evm ⟨hat, hrd⟩
  have hm := hat'.2.2.2.2.2.1
  exact ⟨after, hreach, stored_of_known
    ⟨by rw [hm]; exact hat', by rw [hm]; exact hsize, hmod, by rw [hm]; exact hall⟩
    hslots hrefund hagree, hrd'⟩

/-- From Byzantium, RETURNDATACOPY of a range of the return data `data` writes a fact.

The range ends within the return data.

It keeps the facts of memory apart from the range, the return data and every fact of a slot.

It pays 3, 3 gas a word and the growth of memory, which depends on its size. -/
theorem returndatacopy_stored (hfork : .byzantium ≤ fork) {data : ByteArray}
    {start offset length : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x3e) (hz : length ≠ 0) (fit : offset.toNat + length.toNat ≤ data.size)
    (hgas : 3 + 3 * wordCount length.toNat + (extendMemory size [(start, length)]).cost ≤ gas) :
    Hoare fork
      (fun evm => Stored code message pc (start :: offset :: length :: rest) size facts gas slots
        refund base accessed evm ∧ evm.returnData = data)
      (fun evm => Stored code message (pc + 1) rest
        (size + (extendMemory size [(start, length)]).expandBy)
        ((start.toNat, memoryReadBytes data offset.toNat length.toNat) ::
          facts.filter (Apart start.toNat length.toNat))
        (gas - (3 + 3 * wordCount length.toNat + (extendMemory size [(start, length)]).cost))
        slots refund base accessed evm ∧ evm.returnData = data) := by
  rintro evm ⟨⟨hk, hslots, hrefund, hagree⟩, hrd⟩
  obtain ⟨after, hreach, hk', hrd'⟩ :=
    returndatacopy_known hfork hlt hbyte hz fit hgas evm ⟨hk, hrd⟩
  exact ⟨after, hreach, stored_of_known hk' hslots hrefund hagree, hrd'⟩

/-- A halted frame with its error, output and gas, and the facts of its slots.

It also holds the refund counter, and agrees with the base outside the slots of its facts. -/
def StoppedStored (reverted : Bool) (output : ByteArray) (gas : Nat) (slots : List SlotFact)
    (refund : Int) (base : TransactionState)
    (accessed : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)) (evm : Evm fork Nat) : Prop :=
  evm.running = false ∧ evm.error = (if reverted then some .revert else none) ∧
    evm.output = output ∧ evm.gas = gas ∧
    (∀ fact ∈ slots, fact.Holds evm.state evm.substate) ∧
    evm.substate.refundCounter = refund ∧
    Agrees (slots.map SlotFact.slot) [] [] base accessed evm.state
      evm.substate.accessedStorageKeys

/-- A rule that halts and keeps the state and the substate, for every one, keeps every fact. -/
theorem StoppedStored.of_known {reverted : Bool} {output : ByteArray}
    (h : ∀ state substate, Spec fork (Known code message pc stack size facts gas state substate)
      (Halted reverted output gas' state substate)) :
    Spec fork (Stored code message pc stack size facts gas slots refund base accessed)
      (StoppedStored reverted output gas' slots refund base accessed) := by
  rintro evm ⟨hk, hslots, hrefund, hagree⟩
  obtain ⟨after, hreach, -, hrun, herr, hout, hg, hs, hss⟩ := h evm.state evm.substate evm hk
  exact ⟨after, hreach, hrun, hrun, herr, hout, hg, by rw [hs, hss]; exact hslots,
    by rw [hss]; exact hrefund, by rw [hs, hss]; exact hagree⟩

/-- STOP stops the frame with no error and an empty output, at no price, and keeps every fact. -/
theorem stop_stored (hlt : pc < code.size) (hbyte : code[pc] = 0x00) :
    Spec fork (Stored code message pc stack size facts gas slots refund base accessed)
      (StoppedStored false .empty gas slots refund base accessed) :=
  StoppedStored.of_known fun _ _ evm hk => stop hlt hbyte evm hk.1

end EthLib.Execution.Evm.Logic
