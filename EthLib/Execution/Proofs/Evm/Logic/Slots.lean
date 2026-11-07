module

public import EthLib.Execution.Proofs.Evm.Logic.Known
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: frames that know a few slots of storage

A specification often cares about a few slots of the storage of its account, not about the rest.

A fact of a slot gives its key, its word before the transaction, and its word now.

It also says whether the slot is warm.

A slot is warm when the transaction has accessed it, by EIP-2929.

A frame of this kind knows ranges of memory, the facts of some slots, and the refund counter.

It also keeps every other slot, and every account, as a base state holds them.

- A rule that keeps the state and the substate, for every state and substate, keeps every fact.
- From Berlin, SLOAD of the key of a fact pushes its word now, and makes the slot warm.
- It pays 2100 for a cold slot and 100 for a warm one.
- From Berlin to before Glamsterdam, SSTORE to the key of a fact writes the slot and makes it warm.
- It needs a frame that may change the state, more than 2300 gas, and its account in the base state.
- It pays the price of EIP-2200 with the prices of EIP-2929, from the facts of the slot.
- It adds the refund of the write, from the same facts, to the refund counter.

These frames say nothing of the logs, the accessed addresses and the other fields of the substate.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 Address Bytes32)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- What a frame knows of one slot of the storage of its account. -/
structure SlotFact where
  /-- The key of the slot. -/
  key : U256
  /-- The word of the slot before the transaction. -/
  original : U256
  /-- The word of the slot now. -/
  current : U256
  /-- Whether the transaction has accessed the slot. -/
  warm : Bool

/-- The state and the substate agree with a fact of a slot of the account `target`. -/
def SlotFact.Holds (fact : SlotFact) (target : Address) (state : TransactionState)
    (substate : Substate) : Prop :=
  state.getStorageOriginal target (U256.toBeBytes fact.key) = fact.original ∧
    state.getStorage target (U256.toBeBytes fact.key) = fact.current ∧
    decide (U256.toBeBytes fact.key ∈ substate.accessedStorageKeys.getD target ∅) = fact.warm

/-- The state reads as `base` at every slot that no fact names, and has the accounts of `base`. -/
def KeepsOthers (base state : TransactionState) (target : Address) (slots : List SlotFact) :
    Prop :=
  (∀ other key, (other ≠ target ∨ ∀ fact ∈ slots, key ≠ U256.toBeBytes fact.key) →
    state.getStorage other key = base.getStorage other key) ∧
    ∀ other, state.getAccountOptional other = base.getAccountOptional other

/-- A frame that knows ranges of memory, the facts of some slots and the refund counter.

Every other slot of every account reads as in `base`, and the accounts are those of `base`. -/
def Stored (code : ByteArray) (message : Message fork) (pc : Nat) (stack : List U256)
    (size : Nat) (facts : List (Nat × ByteArray)) (gas : Nat) (slots : List SlotFact)
    (refund : Int) (base : TransactionState) (evm : Evm fork Nat) : Prop :=
  Known code message pc stack size facts gas evm.state evm.substate evm ∧
    (∀ fact ∈ slots, fact.Holds message.currentTarget evm.state evm.substate) ∧
    evm.substate.refundCounter = refund ∧ KeepsOthers base evm.state message.currentTarget slots

variable {code : ByteArray} {message : Message fork} {pc pc' : Nat} {stack stack' : List U256}
  {size size' : Nat} {facts facts' : List (Nat × ByteArray)} {gas gas' : Nat}
  {slots : List SlotFact} {refund : Int} {base : TransactionState}

/-- A frame that is known, with the facts of its slots, the refund counter and the base state. -/
theorem stored_of_known {evm : Evm fork Nat} {state : TransactionState} {substate : Substate}
    (h : Known code message pc stack size facts gas state substate evm)
    (hslots : ∀ fact ∈ slots, fact.Holds message.currentTarget state substate)
    (hrefund : substate.refundCounter = refund)
    (hkeep : KeepsOthers base state message.currentTarget slots) :
    Stored code message pc stack size facts gas slots refund base evm := by
  have hs : evm.state = state := h.1.2.2.2.2.2.2.2.2.2.2.1
  have hss : evm.substate = substate := h.1.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨by rw [hs, hss]; exact h, by rw [hs, hss]; exact hslots, by rw [hss]; exact hrefund,
    by rw [hs]; exact hkeep⟩

/-- A rule that keeps the state and the substate, for every state and substate, keeps every fact. -/
theorem Stored.of_known
    (h : ∀ state substate, Hoare fork (Known code message pc stack size facts gas state substate)
      (Known code message pc' stack' size' facts' gas' state substate)) :
    Hoare fork (Stored code message pc stack size facts gas slots refund base)
      (Stored code message pc' stack' size' facts' gas' slots refund base) := by
  rintro evm ⟨hk, hslots, hrefund, hkeep⟩
  obtain ⟨after, hreach, hk'⟩ := h evm.state evm.substate evm hk
  exact ⟨after, hreach, stored_of_known hk' hslots hrefund hkeep⟩

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

/-- The facts of the slots after an access to the slot of `fact`, which becomes `fact'`.

The facts of the other keys stay. -/
def touch (fact' : SlotFact) (slots : List SlotFact) : List SlotFact :=
  fact' :: slots.filter fun fact => fact.key ≠ fact'.key

/-- After an access to the slot of `fact'`, the facts of the slots hold of the new state.

The new fact holds, and each fact of another key that held before still holds. -/
theorem holds_touch {fact' : SlotFact} {target : Address} {state state' : TransactionState}
    {substate substate' : Substate} (hslots : ∀ fact ∈ slots, fact.Holds target state substate)
    (hnew : fact'.Holds target state' substate')
    (hother : ∀ fact ∈ slots, fact.key ≠ fact'.key → fact.Holds target state substate →
      fact.Holds target state' substate') :
    ∀ fact ∈ touch fact' slots, fact.Holds target state' substate' := by
  intro fact hfact
  rcases List.mem_cons.mp hfact with rfl | hfact
  · exact hnew
  · obtain ⟨hmem, hne⟩ := List.mem_filter.mp hfact
    exact hother fact hmem (by simpa using hne) (hslots fact hmem)

/-- After an access to the slot of `fact'`, the state still keeps the other slots of `base`.

The access may change only that slot, and keeps the accounts. -/
theorem KeepsOthers.touch {fact' : SlotFact} {target : Address} {state state' : TransactionState}
    (h : KeepsOthers base state target slots)
    (hread : ∀ other key, (other ≠ target ∨ key ≠ U256.toBeBytes fact'.key) →
      state'.getStorage other key = state.getStorage other key)
    (haccount : ∀ other, state'.getAccountOptional other = state.getAccountOptional other) :
    KeepsOthers base state' target (touch fact' slots) := by
  refine ⟨fun other key hne => ?_, fun other => by rw [haccount, h.2]⟩
  have hhead : other ≠ target ∨ key ≠ U256.toBeBytes fact'.key := by
    rcases hne with hne | hne
    · exact .inl hne
    · exact .inr (hne fact' (List.mem_cons_self ..))
  rw [hread other key hhead]
  refine h.1 other key ?_
  rcases hne with hne | hne
  · exact .inl hne
  · refine .inr fun fact hfact => ?_
    by_cases hkey : fact.key = fact'.key
    · rw [hkey]
      exact hne fact' (List.mem_cons_self ..)
    · exact hne fact
        (List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hfact, by simpa using hkey⟩))

/-- The accessed slots after an access keep the warmth of every other key. -/
theorem warm_of_ne {keys : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)} {target : Address}
    {key other : U256} (hne : other ≠ key) :
    decide (U256.toBeBytes other ∈ (keys.insert target ((keys.getD target ∅).insert
      (U256.toBeBytes key))).getD target ∅) =
      decide (U256.toBeBytes other ∈ keys.getD target ∅) := by
  have hb : U256.toBeBytes other ≠ U256.toBeBytes key := fun h => hne (toBeBytes_inj h)
  simp only [mem_getD_insert, true_and, hb, false_or]

/-- The accessed slots after an access hold the key accessed. -/
theorem warm_self {keys : Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32)} {target : Address}
    {key : U256} :
    decide (U256.toBeBytes key ∈ (keys.insert target ((keys.getD target ∅).insert
      (U256.toBeBytes key))).getD target ∅) = true := by
  simp only [mem_getD_insert, true_and, true_or, decide_true]

/-- From Berlin, SLOAD of the key of a fact pushes the word of the slot now, and makes it warm.

It pays 2100 for a cold slot and 100 for a warm one, by EIP-2929. -/
theorem sload_stored (hfork : .berlin ≤ fork) {fact : SlotFact} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x54) (hfact : fact ∈ slots)
    (hgas : (if fact.warm then 100 else 2100) ≤ gas) :
    Hoare fork (Stored code message pc (fact.key :: rest) size facts gas slots refund base)
      (Stored code message (pc + 1) (fact.current :: rest) size facts
        (gas - if fact.warm then 100 else 2100) (touch { fact with warm := true } slots) refund
        base) := by
  rintro evm ⟨⟨hat, hsize, hmod, hall⟩, hslots, hrefund, hkeep⟩
  obtain ⟨ho, hc, hw⟩ := hslots fact hfact
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
    (holds_touch hslots ⟨ho, hc, warm_self⟩ fun other _ hne hold =>
      ⟨hold.1, hold.2.1, by rw [warm_of_ne hne]; exact hold.2.2⟩) hrefund
    (hkeep.touch (fun _ _ _ => rfl) fun _ => rfl)⟩

/-- From Berlin to before Glamsterdam, SSTORE to the key of a fact writes it, and makes it warm.

The frame may change the state, and holds more than the stipend of 2300 gas, by EIP-2200.

The account of the frame exists in the base state.

It pays the price of the write from the facts of the slot, by EIP-2200 with the prices of EIP-2929.

It adds the refund of the write, from the same facts, to the refund counter. -/
theorem sstore_stored (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {fact : SlotFact}
    {new : U256} {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x55)
    (hstatic : message.isStatic = false) (hfact : fact ∈ slots)
    (hbase : (base.getAccountOptional message.currentTarget).isSome = true)
    (hstipend : CALL_STIPEND < gas)
    (hgas : sstoreCost fork fact.original fact.current new (!fact.warm) ≤ gas) :
    Hoare fork (Stored code message pc (fact.key :: new :: rest) size facts gas slots refund base)
      (Stored code message (pc + 1) rest size facts
        (gas - sstoreCost fork fact.original fact.current new (!fact.warm))
        (touch { fact with current := new, warm := true } slots)
        (refund + sstoreRefund fork fact.original fact.current new) base) := by
  rintro evm ⟨⟨hat, hsize, hmod, hall⟩, hslots, hrefund, hkeep⟩
  obtain ⟨ho, hc, hw⟩ := hslots fact hfact
  have hcold : decide (U256.toBeBytes fact.key ∉
      evm.substate.accessedStorageKeys.getD message.currentTarget ∅) = !fact.warm := by
    rw [← hw]
    simp
  obtain ⟨state', hnew, hothers, horig, haccount, hrule⟩ := sstore_of_account hfork hglam hlt
    hbyte hstatic hcold hstipend (by rw [ho, hc]; exact hgas) (by rw [hkeep.2]; exact hbase)
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
    (holds_touch hslots ⟨by rw [horig]; exact ho, hnew, warm_self⟩ fun other _ hne hold =>
      ⟨by rw [horig]; exact hold.1,
        by rw [hothers _ _ (.inr fun h => hne (toBeBytes_inj h))]; exact hold.2.1,
        by rw [warm_of_ne hne]; exact hold.2.2⟩)
    (by rw [← hrefund]) (hkeep.touch (fun other key h => hothers other key h) haccount)⟩

/-- A stopped frame with its error, output and gas, and the facts of its slots.

It also holds the refund counter `refund`, and the other slots and the accounts of `base`. -/
def StoppedStored (reverted : Bool) (output : ByteArray) (gas : Nat) (target : Address)
    (slots : List SlotFact) (refund : Int) (base : TransactionState) (evm : Evm fork Nat) : Prop :=
  evm.running = false ∧ evm.error = (if reverted then some .revert else none) ∧
    evm.output = output ∧ evm.gas = gas ∧
    (∀ fact ∈ slots, fact.Holds target evm.state evm.substate) ∧
    evm.substate.refundCounter = refund ∧ KeepsOthers base evm.state target slots

/-- STOP stops the frame with no error and an empty output, at no price, and keeps every fact. -/
theorem stop_stored (hlt : pc < code.size) (hbyte : code[pc] = 0x00) :
    Spec fork (Stored code message pc stack size facts gas slots refund base)
      (StoppedStored false .empty gas message.currentTarget slots refund base) := by
  rintro evm ⟨hk, hslots, hrefund, hkeep⟩
  obtain ⟨after, hreach, -, hrun, herr, hout, hg, hs, hss⟩ := stop hlt hbyte evm hk.1
  exact ⟨after, hreach, hrun, hrun, herr, hout, hg, by rw [hs, hss]; exact hslots,
    by rw [hss]; exact hrefund, by rw [hs]; exact hkeep⟩

end EthLib.Execution.Evm.Logic
