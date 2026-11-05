module

public import EthLib.Execution.Evm.Storage
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.Storage`

From Istanbul, a write that a second write undoes costs, net of refunds, two reads.

A cold first access adds its price on top.

A write that leaves the slot as it is costs one read and changes no refund.

From Berlin, an access to a slot is cold exactly when the transaction has not accessed it.

SSTORE never succeeds in a static frame, and from Istanbul fails with 2300 gas or less.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type}

/-- From Istanbul, a write and the write that restores the original value cost two reads.

That is net of refunds, and a cold first access adds its price. -/
theorem sstore_restore (h : fork ≥ .istanbul) {original new : U256} (hne : original ≠ new)
    (cold : Bool) :
    ((sstoreCost fork original original new cold + sstoreCost fork original new original false :
      Nat) : Int) -
      (sstoreRefund fork original original new + sstoreRefund fork original new original) =
      (if cold then COLD_STORAGE_ACCESS else 0) + 2 * sstoreReadCost fork := by
  have hne' : new ≠ original := Ne.symm hne
  unfold sstoreCost sstoreRefund sstoreResetCost sstoreReadCost
  by_cases hb : fork ≥ .berlin <;> by_cases h0 : original = 0 <;> by_cases h1 : new = 0 <;>
    cases cold <;> simp [h, hb, h0, h1, hne, hne'] <;> simp_all <;> omega

/-- From Istanbul, a write of the current value costs a read, and the cold surcharge. -/
theorem sstoreCost_noop (h : fork ≥ .istanbul) (original current : U256) (cold : Bool) :
    sstoreCost fork original current current cold =
      (if cold then COLD_STORAGE_ACCESS else 0) + sstoreReadCost fork := by
  simp [sstoreCost, h]

/-- From Istanbul, a write of the current value changes no refund. -/
theorem sstoreRefund_noop (h : fork ≥ .istanbul) (original current : U256) :
    sstoreRefund fork original current current = 0 := by
  simp [sstoreRefund, h]

/-- Before Istanbul, a write costs 20000 to fill a zero slot, and 5000 otherwise. -/
theorem sstoreCost_of_lt_istanbul (h : fork < .istanbul) (original current new : U256)
    (cold : Bool) :
    sstoreCost fork original current new cold =
      if new ≠ 0 ∧ current = 0 then STORAGE_SET else COLD_STORAGE_WRITE := by
  have : ¬fork ≥ .istanbul := Nat.not_le_of_lt h
  simp only [sstoreCost, this, ite_false]

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

/-- SSTORE never succeeds in a static frame. -/
theorem sstoreStep_ne_ok_of_isStatic {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) : sstoreStep evm ≠ .ok after := by
  intro h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have m2 : e2.message = evm.message :=
    (popWord_sameContext h2).message.trans (popWord_sameContext h1).message
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · obtain ⟨keys, hacc⟩ := accessStorageKey_snd e2 e2.message.currentTarget (U256.toBeBytes k)
    rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e3⟩
    rw [hpair] at hacc
    simp only [hpair] at h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have m4 : e4.message = evm.message := by
      rw [(chargeGas_sameContext h4).message]
      cases hacc
      exact m2
    simp [m4, static, throw, throwThe, MonadExceptOf.throw] at h

/-- From Istanbul, SSTORE fails out of gas with 2300 gas left or less. -/
theorem sstoreStep_of_gasLeft_le (h : fork ≥ .istanbul) {evm : Evm fork Meter}
    {key new : U256} {rest : List U256} (hs : evm.stack.val = key :: new :: rest)
    (low : GasMeter.gasLeft evm.gas ≤ CALL_STIPEND) : sstoreStep evm = .error .outOfGas := by
  have hstack : evm.stack = ⟨key :: new :: rest, hs ▸ evm.stack.property⟩ := Subtype.ext hs
  simp [sstoreStep, popWord, hstack, Stack.pop, bind, Except.bind, pure, Except.pure, h, low,
    throw, throwThe, MonadExceptOf.throw]

end EthLib.Execution.Evm
