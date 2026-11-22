module

public import EthLib.Execution.Proofs.Evm.Call.SlotSurplusParts

/-!
# Proofs: each instruction that gives the next frame pays for the slots it counts

From Glamsterdam, an instruction that gives the next frame changes the counted slots only by SSTORE.

The counted slots are the fresh slots of the accounts with a nonce or code.

SSTORE writes the storage of the current account.

When that account has a nonce or code, its state gas net of its refill pays for its slots.

SELFDESTRUCT moves a balance, and may pay state gas for a new account.

Every other instruction keeps the state up to its reads, its transient storage and its logs.

It charges only execution gas, or halts.

REVERT stops the frame with an error, and an exceptional halt rolls the meter back.

So from a running frame whose current account has a nonce or code, each such instruction pays.

Source: [EIP-8037][eip8037], the state gas of a new slot and its refill.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256 toAddressMasked)
open GasCosts

variable {fork : Fork}

/-- A frame that keeps the error and the surplus of a running frame pays from it. -/
private theorem paysSlots_of_surplusKept {evm after : Evm fork StateGasMeter}
    (running : evm.running = true) (h : SurplusKept evm after) : PaysSlots evm after :=
  PaysSlots.of_le running h.1 h.2

/-- A charge of execution gas keeps the net state gas. -/
private theorem stateGasUsed_chargeGas {evm after : Evm fork StateGasMeter} {amount : Nat}
    (h : chargeGas evm amount = .ok after) : after.gas.stateGasUsed = evm.gas.stateGasUsed := by
  obtain ⟨gas, hgas, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨-, rfl⟩ := StateGasMeter.charge_eq_ok_iff.mp hgas
  rfl

/-- A charge of state gas raises the net state gas by its amount. -/
private theorem stateGasUsed_chargeStateGas {evm after : Evm fork StateGasMeter} {amount : Nat}
    (h : chargeStateGas evm amount = .ok after) :
    after.gas.stateGasUsed = evm.gas.stateGasUsed + amount := by
  obtain ⟨gas, hgas, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact StateGasMeter.stateGasUsed_chargeState hgas

/-- Two frames have the same surplus when the net state gas and the count change alike.

The net state gas changes by a charge less a refill.

The count changes by that amount, in units of the state gas of a new slot. -/
private theorem slotSurplus_eq_of_net {a b : Evm fork StateGasMeter} {refill charge : Nat}
    (hgas : b.gas.stateGasUsed = a.gas.stateGasUsed - refill + charge)
    (hnet : (charge : Int) - refill = STORAGE_SET_STATE_GAS *
      (((nonceOrCodeFreshSlots b.state).card : Int) - (nonceOrCodeFreshSlots a.state).card)) :
    slotSurplus a = slotSurplus b := by
  unfold slotSurplus
  rw [hgas]
  rw [Int.mul_sub] at hnet
  omega

/-- From Glamsterdam, SSTORE pays for its slots.

The frame must run, and its current account must have a nonce or code. -/
private theorem paysSlots_sstoreStep (hfork : .glamsterdam ≤ fork)
    {evm after : Evm fork StateGasMeter} (running : evm.running = true)
    (hcode : HasNonceOrCode evm.state evm.message.currentTarget)
    (h : sstoreStep evm = .ok after) : PaysSlots evm after := by
  unfold sstoreStep at h
  split at h
  · cases h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · cases h
  rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with ⟨cold, e3⟩
  simp only [hpair] at h
  -- The access to the slot changes only the substate.
  obtain ⟨keys, hk⟩ := accessStorageKey_snd e2 e2.message.currentTarget (U256.toBeBytes k)
  rw [hpair] at hk
  dsimp only at hk
  subst hk
  -- The pops, the access and the read keep the surplus, the message and every account.
  have c2 := (popWord_sameContext h1).trans (popWord_sameContext h2)
  have pre := ((surplusKept_popWord h1).trans (surplusKept_popWord h2)).trans
    (surplusKept_recordStorageRead
      { e2 with substate := { e2.substate with accessedStorageKeys := keys } }
      e2.message.currentTarget (U256.toBeBytes k))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · cases h
    obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    -- The refill lowers the net state gas, the charge keeps it, and the state gas raises it.
    have g4 := stateGasUsed_chargeGas h4
    have g5 := stateGasUsed_chargeStateGas h5
    have s5 := (chargeStateGas_sameContext h5).state.trans (chargeGas_sameContext h4).state
    rw [s5] at hst
    have err5 := (surplusKept_chargeStateGas h5).1.trans (surplusKept_chargeGas h4).1
    -- The write is at the current account, which has a nonce or code.
    have hcode' : HasNonceOrCode
        (e2.state.recordStorageRead e2.message.currentTarget (U256.toBeBytes k))
        e2.message.currentTarget := by
      rw [c2.message, c2.state]
      exact hcode
    -- Its state gas net of its refill pays for the slots that it adds.
    have hnet := sstoreStateGas_sub_sstoreStateRefill_of_hasNonceOrCode hfork hcode'
      (Base.mapError_ok_iff.mp hst)
    refine PaysSlots.of_le running (err5.trans pre.1) (pre.2.trans (le_of_eq ?_))
    rw [g4] at g5
    exact slotSurplus_eq_of_net
      (g5.trans (congrArg (· + _) (StateGasMeter.stateGasUsed_refill _ _))) hnet
  · exact paysSlots_exceptionalHalt _ _ _

/-- SELFDESTRUCT from a running frame pays for its slots.

It moves a balance, which keeps the counted slots, and may pay state gas. -/
private theorem paysSlots_selfdestructStep {evm after : Evm fork StateGasMeter}
    (running : evm.running = true) (h : selfdestructStep fork evm = .ok after) :
    PaysSlots evm after := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  -- The pop, the access and the read keep the surplus.
  have pre := ((surplusKept_popWord h1).trans
    (surplusKept_accessAddress e1 (toAddressMasked w))).trans
      (surplusKept_recordAccountRead _ (toAddressMasked w))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    have paid := (pre.trans (surplusKept_chargeGas h2)).trans (surplusKept_chargeStateGas h3)
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
      cases h
      -- The move of the balance keeps the counted slots, and the frame stops.
      have hslots := nonceOrCodeFreshSlots_selfdestructTransfer (Base.mapError_ok_iff.mp hst)
      refine PaysSlots.of_le running paid.1 (paid.2.trans (le_of_eq ?_))
      simp only [slotSurplus, hslots]
  · exact paysSlots_exceptionalHalt _ _ _

/-- From Glamsterdam, each instruction that gives the next frame pays for its slots.

The frame must run, and its current account must have a nonce or code. -/
theorem paysSlots_instruction (hfork : .glamsterdam ≤ fork) {op : Op}
    {run : Evm fork StateGasMeter → Except EvmError (Evm fork StateGasMeter)}
    {evm after : Evm fork StateGasMeter} (running : evm.running = true)
    (hcode : HasNonceOrCode evm.state evm.message.currentTarget)
    (hrun : instruction fork op = some run) (h : run evm = .ok after) : PaysSlots evm after := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact paysSlots_of_surplusKept running (surplusKept_stackOnlyStep hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact paysSlots_of_surplusKept running (surplusKept_controlFlowStep hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact paysSlots_of_surplusKept running (surplusKept_memoryDataStep hf h)
  rcases orElse_eq_some hrun with hf | hrun
  -- RETURN keeps the surplus, and REVERT fails.
  · exact (surplusKept_returnOpStep hf h).elim (paysSlots_of_surplusKept running) .inl
  rcases orElse_eq_some hrun with hf | hrun
  · exact paysSlots_of_surplusKept running (surplusKept_environmentStep hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact paysSlots_of_surplusKept running (surplusKept_accountStep hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    case sload => exact paysSlots_of_surplusKept running (surplusKept_sloadStep h)
    case sstore => exact paysSlots_sstoreStep hfork running hcode h
  rcases orElse_eq_some hrun with hf | hrun
  · exact paysSlots_of_surplusKept running (surplusKept_transientStorageStep hf h)
  rcases orElse_eq_some hrun with hf | hf
  · exact paysSlots_of_surplusKept running (surplusKept_logOpStep hf h)
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact paysSlots_selfdestructStep running h

end EthLib.Execution.Evm
