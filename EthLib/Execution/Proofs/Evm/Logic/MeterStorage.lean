module

public import EthLib.Execution.Proofs.Evm.Logic.MeterSimulation

/-!
# Proofs: storage instructions under the state gas meter

A successful write pays execution and state gas after any refill.

Paying both from one counter is conservative for the state gas meter of EIP-8037.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)

variable {fork : Fork}

private theorem popWord_withStateGas (evm : Evm fork Nat) (meter : StateGasMeter) :
    popWord (withStateGas evm meter) =
      (popWord evm).map (fun p => (p.1, withStateGas p.2 meter)) := by
  rcases evm with ⟨pc, ⟨l, hp⟩, memory, code, flags, gas, running, message,
    output, returnData, state, substate, error⟩
  cases l <;> rfl

private theorem gas_popWord {evm after : Evm fork Nat} {word : U256}
    (ok : popWord evm = .ok (word, after)) : after.gas = evm.gas := by
  unfold popWord at ok
  obtain ⟨⟨x, st⟩, _, h⟩ := EthLib.Base.bind_ok_iff.mp ok
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

private theorem accessStorageKey_withStateGas (evm : Evm fork Nat) (meter : StateGasMeter)
    (address : EthLib.Base.Address) (key : EthLib.Base.Bytes32) :
    accessStorageKey (withStateGas evm meter) address key =
      ((accessStorageKey evm address key).1,
        withStateGas (accessStorageKey evm address key).2 meter) := by
  unfold accessStorageKey
  split <;> rfl

private theorem gas_accessStorageKey (evm : Evm fork Nat) (address : EthLib.Base.Address)
    (key : EthLib.Base.Bytes32) : (accessStorageKey evm address key).2.gas = evm.gas := by
  unfold accessStorageKey
  split <;> rfl

private theorem chargeGas_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    {amount : Nat} (below : evm.gas ≤ meter.gasLeft) (ok : chargeGas evm amount = .ok after) :
    ∃ next, chargeGas (withStateGas evm meter) amount = .ok next ∧ FollowsMeter after next := by
  change (GasMeter.charge evm.gas amount).map (fun gas => { evm with gas }) = .ok after at ok
  change ∃ next, (meter.charge amount).map
    (fun gas => { withStateGas evm meter with gas }) = .ok next ∧ FollowsMeter after next
  exact map_charge_followsMeter
    (low := fun g => { evm with gas := g })
    (high := fun m => { withStateGas evm meter with gas := m })
    below (fun _ _ => rfl) (fun _ => rfl) ok

private theorem chargeStateGas_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    {amount : Nat} (below : evm.gas ≤ meter.gasLeft)
    (ok : chargeStateGas evm amount = .ok after) :
    ∃ next, chargeStateGas (withStateGas evm meter) amount = .ok next ∧
      FollowsMeter after next := by
  change (GasMeter.chargeState evm.gas amount).map (fun gas => { evm with gas }) = .ok after at ok
  change ∃ next, (meter.chargeState amount).map
    (fun gas => { withStateGas evm meter with gas }) = .ok next ∧ FollowsMeter after next
  exact map_chargeState_followsMeter
    (low := fun g => { evm with gas := g })
    (high := fun m => { withStateGas evm meter with gas := m })
    below (fun _ _ => rfl) (fun _ => rfl) ok

/-- A normal SSTORE writes the same slot under the state gas meter. -/
theorem sstoreStep_followsMeter {evm after : Evm fork Nat} {meter : StateGasMeter}
    (below : evm.gas ≤ meter.gasLeft) (ok : sstoreStep evm = .ok after)
    (normal : after.error = none) :
    ∃ next, sstoreStep (withStateGas evm meter) = .ok next ∧ FollowsMeter after next := by
  unfold sstoreStep at ok
  split at ok
  · cases ok
  rename_i guard
  obtain ⟨⟨word, e1⟩, hp1, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
  obtain ⟨⟨new, e2⟩, hp2, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
  dsimp only at ok
  split at ok
  · cases ok
  rename_i stipend
  rcases keepReads_eq_ok ok with ok | ⟨error, rfl⟩
  · obtain ⟨e3, he, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
    obtain ⟨e4, hs, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
    split at ok
    · cases ok
    rename_i static
    obtain ⟨state, hw, ok⟩ := EthLib.Base.bind_ok_iff.mp ok
    cases ok
    let accessed := accessStorageKey e2 e2.message.currentTarget word.toBeBytes
    let read := recordStorageRead accessed.2 e2.message.currentTarget word.toBeBytes
    let refill := sstoreStateRefill fork
      (e2.state.getStorageOriginal e2.message.currentTarget word.toBeBytes)
      (e2.state.getStorage e2.message.currentTarget word.toBeBytes) new
    have below2 : e2.gas ≤ meter.gasLeft := by
      rw [gas_popWord hp2, gas_popWord hp1]
      exact below
    have belowRead : read.gas ≤ meter.gasLeft := by
      change accessed.2.gas ≤ meter.gasLeft
      rw [gas_accessStorageKey]
      exact below2
    obtain ⟨_, paid, m3, below3, rfl⟩ := chargeGas_followsMeter
      (refill_followsMeter (amount := refill) belowRead) he
    obtain ⟨_, statePaid, m4, below4, rfl⟩ := chargeStateGas_followsMeter below3 hs
    refine ⟨_, ?_, m4, below4, rfl⟩
    have highStipend : ¬(fork ≥ .istanbul ∧ meter.gasLeft ≤ GasCosts.CALL_STIPEND) := by
      simp only [GasMeter.gasLeft] at stipend
      intro h
      exact stipend ⟨h.1, Nat.le_trans below2 h.2⟩
    rw [sstoreStep, ite_eq_right (show ¬(fork ≥ .glamsterdam ∧
      (withStateGas evm meter).message.isStatic = true) from guard),
      popWord_withStateGas, hp1]
    simp only [Except.map, bind, Except.bind]
    rw [popWord_withStateGas, hp2]
    simp only [Except.map]
    simp only [show GasMeter.gasLeft (withStateGas e2 meter).gas = meter.gasLeft from rfl]
    rw [ite_eq_right highStipend, accessStorageKey_withStateGas]
    change keepReads (withStateGas read meter) id _ = .ok _
    unfold keepReads
    simp only [show (withStateGas e2 meter).message = e2.message from rfl,
      show (withStateGas e2 meter).state = e2.state from rfl]
    rw [show recordStorageRead (withStateGas accessed.2 meter) e2.message.currentTarget
      word.toBeBytes = withStateGas read meter from rfl]
    rw [show refillStateGas (withStateGas read meter) refill =
      withStateGas (refillStateGas read refill) (meter.refill refill) from rfl]
    change chargeGas (withStateGas (refillStateGas read refill) (meter.refill refill))
      (sstoreCost fork (e2.state.getStorageOriginal e2.message.currentTarget word.toBeBytes)
        (e2.state.getStorage e2.message.currentTarget word.toBeBytes) new accessed.1) =
      .ok (withStateGas e3 m3) at paid
    rw [paid]
    dsimp only
    rw [statePaid]
    simp only [withStateGas, static, hw, pure, Except.pure]
    rfl
  · simp [exceptionalHalt] at normal

end EthLib.Execution.Evm.Logic
