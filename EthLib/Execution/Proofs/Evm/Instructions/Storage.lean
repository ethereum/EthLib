module

public import EthLib.Execution.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.Instructions.Storage`

From Istanbul to BPO5, a write that a second write undoes costs, net of refunds, two reads.

A cold first access adds its price on top.

A write that leaves the slot as it is costs one read and changes no refund.

From Glamsterdam, a write that a second write undoes costs two accesses, net of refunds.

The first may be cold, and the state gas of a new slot comes back.

A write that leaves the slot as it is costs one access, and no state gas.

Only a write that sets a zero slot charges state gas, and only a reset to zero refills it.

From Berlin, an access to a slot is cold exactly when the transaction has not accessed it.

SSTORE never completes in a static frame, and from Istanbul fails with 2300 gas or less.

From Glamsterdam, SSTORE in a static frame fails before it reads the stack.

SLOAD accesses the slot of the current account and pays the cold or warm price of the fork.

Then it puts the word of the slot in place of the key.

SLOAD and SSTORE keep memory.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type}

/-- From Istanbul, a write of the current value changes no refund. -/
theorem sstoreRefund_noop (h : fork ≥ .istanbul) (original current : U256) :
    sstoreRefund fork original current current = 0 := by
  simp [sstoreRefund, h]

/-- From Istanbul to BPO5, a write of the current value costs a read, and the cold surcharge. -/
theorem sstoreCost_noop (h : fork ≥ .istanbul) (hlt : fork < .glamsterdam)
    (original current : U256) (cold : Bool) :
    sstoreCost fork original current current cold =
      (if cold then COLD_STORAGE_ACCESS else 0) + sstoreReadCost fork := by
  have hg : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hlt
  simp [sstoreCost, h, hg]

/-- From Glamsterdam, a write of the current value costs one access, and no state gas. -/
theorem sstore_noop_of_glamsterdam (h : fork ≥ .glamsterdam) (original current : U256)
    (cold : Bool) :
    sstoreCost fork original current current cold =
        (if cold then COLD_STORAGE_ACCESS else WARM_ACCESS) ∧
      sstoreStateGas fork original current current = 0 ∧
      sstoreStateRefill fork original current current = 0 := by
  refine ⟨by simp [sstoreCost, h], ?_, ?_⟩ <;>
    simp only [sstoreStateGas, sstoreStateRefill] <;> split <;> simp_all

/-- From Istanbul to BPO5, a write and the write that restores the original value cost two reads.

That is net of refunds, and a cold first access adds its price. -/
theorem sstore_restore (h : fork ≥ .istanbul) (hlt : fork < .glamsterdam) (original new : U256)
    (cold : Bool) :
    ((sstoreCost fork original original new cold + sstoreCost fork original new original false :
      Nat) : Int) -
      (sstoreRefund fork original original new + sstoreRefund fork original new original) =
      (if cold then COLD_STORAGE_ACCESS else 0) + 2 * sstoreReadCost fork := by
  by_cases hne : original = new
  · subst hne
    rw [sstoreCost_noop h hlt, sstoreCost_noop h hlt, sstoreRefund_noop h]
    cases cold <;> simp <;> omega
  have hne : original ≠ new := hne
  have hne' : new ≠ original := Ne.symm hne
  have hg : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hlt
  unfold sstoreCost sstoreRefund sstoreResetCost sstoreReadCost
  simp only [hg, ite_false]
  by_cases hb : fork ≥ .berlin <;> by_cases h0 : original = 0 <;> by_cases h1 : new = 0 <;>
    cases cold <;> simp [h, hb, h0, h1, hne, hne'] <;> simp_all <;> omega

/-- From Berlin to BPO5, a write costs at most a cold access and the price to fill a slot. -/
theorem sstoreCost_le (h : fork ≥ .berlin) (hlt : fork < .glamsterdam)
    (original current new : U256) (cold : Bool) :
    sstoreCost fork original current new cold ≤ COLD_STORAGE_ACCESS + STORAGE_SET := by
  have hg : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hlt
  have hi : fork ≥ .istanbul := Nat.le_trans (by decide) h
  unfold sstoreCost sstoreResetCost sstoreReadCost
  simp only [hg, hi, h, ite_false, ite_true]
  cases cold <;> simp only [ite_true, Bool.false_eq_true, ite_false, COLD_STORAGE_ACCESS,
    STORAGE_SET, COLD_STORAGE_WRITE, WARM_ACCESS] <;> split <;> (try split) <;> omega

/-- The charge of a storage write when one counter pays both execution gas and state gas. -/
def sstoreTotalCost (fork : Fork) (original current new : U256) (cold : Bool) : Nat :=
  sstoreCost fork original current new cold + sstoreStateGas fork original current new

/-- Before Glamsterdam, a write charges no state gas, so its total charge is its price. -/
theorem sstoreTotalCost_of_lt (hlt : fork < .glamsterdam) (original current new : U256)
    (cold : Bool) :
    sstoreTotalCost fork original current new cold = sstoreCost fork original current new cold := by
  have hg : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hlt
  simp [sstoreTotalCost, sstoreStateGas, hg]

/-- A factor for one-counter gas budgets: 1 before Glamsterdam, and 5 from Glamsterdam.

It is a loose bound chosen for proofs, not a value of the protocol.

From Glamsterdam, 5 times 22,100 covers the 12,100 execution gas and 97,920 state gas of a write. -/
def storageGasScale (fork : Fork) : Nat := if fork ≥ .glamsterdam then 5 else 1

/-- The factor is at least 1, so scaling never lowers a gas budget. -/
theorem one_le_storageGasScale (fork : Fork) : 1 ≤ storageGasScale fork := by
  unfold storageGasScale
  split <;> decide

/-- The factor is at most 5. -/
theorem storageGasScale_le (fork : Fork) : storageGasScale fork ≤ 5 := by
  unfold storageGasScale
  split <;> decide

/-- Before Glamsterdam, the factor is 1. -/
theorem storageGasScale_of_lt (h : fork < .glamsterdam) : storageGasScale fork = 1 := by
  have hn : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [storageGasScale, hn, ↓reduceIte]

/-- From Berlin, the total charge of a write is at most 22,100 gas times the factor. -/
theorem sstoreTotalCost_le (hfork : fork ≥ .berlin) (original current new : U256) (cold : Bool) :
    sstoreTotalCost fork original current new cold ≤ 22100 * storageGasScale fork := by
  by_cases hglam : fork ≥ .glamsterdam
  · have he : sstoreCost fork original current new cold ≤ 12100 := by
      rw [sstoreCost, ite_eq_left hglam]
      have hw : (if original = current ∧ current ≠ new then STORAGE_WRITE else 0) ≤ 10000 := by
        split <;> decide
      cases cold <;> simp only [Bool.false_eq_true, ↓reduceIte, COLD_STORAGE_ACCESS,
        WARM_ACCESS] <;> omega
    have hs : sstoreStateGas fork original current new ≤ 97920 := by
      unfold sstoreStateGas
      split <;> decide
    simp only [sstoreTotalCost, storageGasScale, hglam, ↓reduceIte, Nat.reduceMul]
    omega
  · have hlt := Nat.lt_of_not_ge hglam
    rw [sstoreTotalCost_of_lt hlt, storageGasScale_of_lt hlt]
    have hcost := sstoreCost_le hfork hlt original current new cold
    simp only [COLD_STORAGE_ACCESS, STORAGE_SET] at hcost
    omega

/-- From Glamsterdam, a write and the write that restores the original value cost two accesses.

That is net of refunds: the second write gives back the write price of the first.

The first access may be cold, and the second is warm.

The state gas that the first write charges, the second refills. -/
theorem sstore_restore_of_glamsterdam (h : fork ≥ .glamsterdam) (original new : U256)
    (cold : Bool) :
    ((sstoreCost fork original original new cold + sstoreCost fork original new original false :
      Nat) : Int) -
      (sstoreRefund fork original original new + sstoreRefund fork original new original) =
      (if cold then COLD_STORAGE_ACCESS else WARM_ACCESS) + WARM_ACCESS ∧
    sstoreStateGas fork original original new + sstoreStateGas fork original new original =
      sstoreStateRefill fork original original new + sstoreStateRefill fork original new original
  := by
  have hi : fork ≥ .istanbul := Nat.le_trans (by decide) h
  by_cases hne : original = new
  · subst hne
    obtain ⟨c₁, g₁, r₁⟩ := sstore_noop_of_glamsterdam h original original cold
    obtain ⟨c₂, -, -⟩ := sstore_noop_of_glamsterdam h original original false
    rw [c₁, c₂, g₁, r₁, sstoreRefund_noop hi]
    cases cold <;> simp
  have hne' : new ≠ original := Ne.symm hne
  unfold sstoreCost sstoreRefund sstoreStateGas sstoreStateRefill
  by_cases h0 : original = 0 <;> by_cases h1 : new = 0 <;>
    cases cold <;> simp [h, hi, h0, h1, hne, hne'] <;> simp_all <;> omega

/-- SSTORE charges state gas only to set a slot that is zero now and was at the start. -/
theorem sstoreStateGas_ne_zero {original current new : U256}
    (hs : sstoreStateGas fork original current new ≠ 0) :
    fork ≥ .glamsterdam ∧ original = 0 ∧ current = 0 ∧ new ≠ 0 := by
  unfold sstoreStateGas at hs
  split at hs
  · assumption
  · exact absurd rfl hs

/-- SSTORE refills state gas only to clear a slot that was zero at the start. -/
theorem sstoreStateRefill_ne_zero {original current new : U256}
    (hs : sstoreStateRefill fork original current new ≠ 0) :
    fork ≥ .glamsterdam ∧ original = 0 ∧ current ≠ 0 ∧ new = 0 := by
  unfold sstoreStateRefill at hs
  split at hs
  · assumption
  · exact absurd rfl hs

/-- The state gas of a new slot: 64 bytes at 1530 gas a byte. -/
theorem storageSetStateGas_eq : STORAGE_SET_STATE_GAS = 97920 := rfl

/-- Before Istanbul, a write costs 20000 to fill a zero slot, and 5000 otherwise. -/
theorem sstoreCost_of_lt_istanbul (h : fork < .istanbul) (original current new : U256)
    (cold : Bool) :
    sstoreCost fork original current new cold =
      if new ≠ 0 ∧ current = 0 then STORAGE_SET else COLD_STORAGE_WRITE := by
  have : ¬fork ≥ .istanbul := Nat.not_le_of_lt h
  have hg : ¬fork ≥ .glamsterdam := fun hg => this (Nat.le_trans (by decide) hg)
  simp only [sstoreCost, this, hg, ite_false]

/-- Before Berlin, an access to a slot is warm and leaves the frame as it is. -/
theorem accessStorageKey_of_lt_berlin (h : fork < .berlin) (evm : Evm fork Meter) (a : Address)
    (key : Bytes32) : accessStorageKey evm a key = (false, evm) := by
  have : ¬fork ≥ .berlin := Nat.not_le_of_lt h
  simp [accessStorageKey, this]

/-- From Berlin, an access is cold exactly when the transaction has not accessed the slot. -/
theorem accessStorageKey_fst (h : fork ≥ .berlin) (evm : Evm fork Meter) (a : Address)
    (key : Bytes32) :
    (accessStorageKey evm a key).1 =
      decide (key ∉ evm.substate.accessedStorageKeys.getD a ∅) := by
  simp [accessStorageKey, h]

/-- A second access to the same slot is warm. -/
theorem accessStorageKey_accessStorageKey_fst (evm : Evm fork Meter) (a : Address)
    (key : Bytes32) : (accessStorageKey (accessStorageKey evm a key).2 a key).1 = false := by
  by_cases h : fork ≥ .berlin
  · simp [accessStorageKey, h]
  · simp [accessStorageKey, h]

/-- An access to a slot keeps the message, the state and the accessed addresses. -/
theorem accessStorageKey_snd (evm : Evm fork Meter) (a : Address) (key : Bytes32) :
    ∃ keys, (accessStorageKey evm a key).2 =
      { evm with substate := { evm.substate with accessedStorageKeys := keys } } := by
  unfold accessStorageKey
  split
  · exact ⟨_, rfl⟩
  · exact ⟨evm.substate.accessedStorageKeys, rfl⟩

variable [GasMeter Meter]

/-- SLOAD on a key: access the slot, pay, read the slot, put its word in place of the key.

From Berlin, the price depends on whether the slot is cold. -/
theorem sloadStep_cons {evm : Evm fork Meter} {word : U256} {rest : List U256}
    (h : evm.stack.val = word :: rest) :
    sloadStep evm =
      let accessed := accessStorageKey { evm with stack := ⟨rest, by
        have := evm.stack.property; rw [h] at this; simp at this; omega⟩ }
        evm.message.currentTarget (U256.toBeBytes word)
      (GasMeter.charge accessed.2.gas (sloadCost fork accessed.1)).map fun gas =>
        { accessed.2 with
          gas
          state := accessed.2.state.recordStorageRead evm.message.currentTarget
            (U256.toBeBytes word)
          stack := ⟨evm.state.getStorage evm.message.currentTarget (U256.toBeBytes word) :: rest,
            by have := evm.stack.property; rw [h] at this; simpa using this⟩
          pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨word :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := evm.stack.property
    rw [h] at this
    simp only [List.length_cons] at this
    omega
  obtain ⟨accessed, hacc⟩ := accessStorageKey_snd
    { evm with stack := ⟨rest, by have := evm.stack.property; rw [h] at this; simp at this; omega⟩ }
    evm.message.currentTarget (U256.toBeBytes word)
  simp only [sloadStep, popWord, chargeGas, recordStorageRead, pushWord, advance, hstack,
    Stack.pop]
  simp only [bind, Except.bind, pure, Except.pure, hacc]
  rcases hc : GasMeter.charge _ _ with _ | _ <;> simp [Except.map, Stack.push, room] <;> rfl


/-- SSTORE never completes in a static frame, or when the current address has no account.

It fails, or it halts with an error. -/
theorem sstoreStep_halts {evm after : Evm fork Meter}
    (bad : evm.message.isStatic = true ∨
      evm.state.getAccountOptional evm.message.currentTarget = none)
    (h : sstoreStep evm = .ok after) : after.running = false ∧ after.error.isSome := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 := (popWord_sameContext h1).trans (popWord_sameContext h2)
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨keys, hacc⟩ := accessStorageKey_snd e2 e2.message.currentTarget (U256.toBeBytes k)
      rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
        ⟨cold, e3⟩
      rw [hpair] at hacc
      simp only [hpair] at h
      obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have c5 := (chargeGas_sameContext h4).trans (chargeStateGas_sameContext h5)
      have m5 : e5.message = evm.message := by
        rw [c5.message]
        cases hacc
        exact c2.message
      have s5 : e5.state = evm.state.recordStorageRead evm.message.currentTarget
          (U256.toBeBytes k) := by
        rw [c5.state]
        cases hacc
        simp only [refillStateGas, recordStorageRead]
        rw [c2.state, c2.message]
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i dynamic
        obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
        rw [m5] at dynamic
        rcases bad with static | none
        · exact absurd static dynamic
        · rw [s5, c2.message] at hst
          have absent : ((evm.state.recordStorageRead evm.message.currentTarget
              (U256.toBeBytes k)).getAccountOptional evm.message.currentTarget).isNone := by
            simpa [State.TransactionState.recordStorageRead,
              State.TransactionState.getAccountOptional] using none
          simp [State.TransactionState.setStorage, absent, Except.mapError] at hst
    · exact ⟨rfl, rfl⟩

/-- SSTORE never completes in a static frame: it fails, or it halts with an error. -/
theorem sstoreStep_halts_of_isStatic {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : sstoreStep evm = .ok after) :
    after.running = false ∧ after.error.isSome :=
  sstoreStep_halts (.inl static) h

/-- From Glamsterdam, SSTORE in a static frame fails before it reads the stack. -/
theorem sstoreStep_of_isStatic (h : fork ≥ .glamsterdam) {evm : Evm fork Meter}
    (static : evm.message.isStatic = true) : sstoreStep evm = .error .writeInStaticContext := by
  simp [sstoreStep, h, static, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- From Istanbul, SSTORE fails out of gas with 2300 gas left or less.

From Glamsterdam, this holds in a frame that may change the state. -/
theorem sstoreStep_of_gasLeft_le (h : fork ≥ .istanbul) {evm : Evm fork Meter}
    {key new : U256} {rest : List U256} (hs : evm.stack.val = key :: new :: rest)
    (low : GasMeter.gasLeft evm.gas ≤ CALL_STIPEND)
    (dynamic : fork < .glamsterdam ∨ evm.message.isStatic = false) :
    sstoreStep evm = .error .outOfGas := by
  have hstack : evm.stack = ⟨key :: new :: rest, hs ▸ evm.stack.property⟩ := Subtype.ext hs
  have first : ¬(fork ≥ .glamsterdam ∧ evm.message.isStatic = true) := by
    rintro ⟨hg, hst⟩
    rcases dynamic with hl | hd
    · exact absurd hg (Nat.not_le_of_lt hl)
    · simp [hd] at hst
  simp [sstoreStep, first, popWord, hstack, Stack.pop, bind, Except.bind, pure, Except.pure, h,
    low, throw, throwThe, MonadExceptOf.throw]

omit [GasMeter Meter] in
/-- An access to a slot keeps memory. -/
theorem memory_accessStorageKey (evm : Evm fork Meter) (a : Address) (key : Bytes32) :
    (accessStorageKey evm a key).2.memory = evm.memory := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm a key
  rw [h]

/-- Each instruction that uses storage keeps memory. -/
theorem memory_storageStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : after.memory = evm.memory := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  case sload =>
    obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    rcases hpair : accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e2⟩
    have m2 : e2.memory = evm.memory := by
      have := memory_accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes k)
      rw [hpair] at this
      exact this.trans (popWord_eq_ok h1).2.1
    simp only [hpair] at h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    simp only [advance, memory_pushWord h4, recordStorageRead, memory_chargeGas h3]
    exact m2
  case sstore =>
    unfold sstoreStep at h
    split at h
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    have m2 : e2.memory = evm.memory := (popWord_eq_ok h2).2.1.trans (popWord_eq_ok h1).2.1
    simp only [] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
        ⟨cold, e3⟩
      have m3 : e3.memory = evm.memory := by
        have := memory_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)
        rw [hpair] at this
        exact this.trans m2
      simp only [hpair] at h
      rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
      · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
        obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
          cases h
          simp only [advance]
          rw [memory_chargeStateGas h5, memory_chargeGas h4]
          exact m3
      · exact m3

end EthLib.Execution.Evm
