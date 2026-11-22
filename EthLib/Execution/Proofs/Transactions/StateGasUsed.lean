module

public import EthLib.Execution.Proofs.Evm.Call.SlotSurplusRun
public import EthLib.Execution.Proofs.Transactions.StateGas

/-!
# Proofs: the gas left of a transaction from Glamsterdam is at most its gas limit

A refill of state gas can raise what a frame holds above what it started with.

Each refill of a run still follows a charge of the same transaction.

The fresh slots of the accounts with a nonce or code count those charges.

A transaction with no write has none, and its authorizations write no storage.

The first frame starts with a meter whose net state gas is not negative.

Its run pays state gas for each slot that it makes fresh.

So the net state gas of the message is at least zero.

Its gas left and its reservoir left are then at most the gas limit less the intrinsic gas.

So the gas used before the refund, the gas limit less both, never floors at zero.

Source: [EIP-8037][eip8037], its reservoir model and its accounting for halts and reverts.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-level-gas-accounting-reservoir-model
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm

variable {fork : Fork}

/-! ## The meter of the first frame -/

/-- The later meter holds at most its starting reservoir, in its reservoir and in its baseline.

It does so whenever the earlier meter does. -/
private def Floored (a b : StateGasMeter) : Prop :=
  a.reservoir ≤ a.grant → a.baseline ≤ a.grant → b.reservoir ≤ b.grant ∧ b.baseline ≤ b.grant

/-- A meter that keeps the bounds after one that keeps them keeps them. -/
private theorem Floored.trans {a b c : StateGasMeter} (hab : Floored a b) (hbc : Floored b c) :
    Floored a c :=
  fun hr hb => hbc (hab hr hb).1 (hab hr hb).2

/-- A charge of execution gas keeps the bounds. -/
private theorem Floored.charge {meter after : StateGasMeter} {amount : Nat}
    (h : GasMeter.charge meter amount = .ok after) : Floored meter after := by
  simp only [GasMeter.charge, StateGasMeter.charge] at h
  split at h
  · cases h
  · cases h
    exact fun hr hb => ⟨hr, hb⟩

/-- A charge of state gas keeps the bounds, since it only lowers the reservoir. -/
private theorem Floored.chargeState {meter after : StateGasMeter} {amount : Nat}
    (h : GasMeter.chargeState meter amount = .ok after) : Floored meter after := by
  simp only [GasMeter.chargeState, StateGasMeter.chargeState] at h
  split at h
  · cases h
    exact fun hr hb => ⟨by dsimp only; omega, hb⟩
  · split at h
    · cases h
      exact fun _ hb => ⟨Nat.zero_le _, hb⟩
    · cases h

/-- A commit keeps the bounds, since it sets the baseline to the reservoir. -/
private theorem Floored.commit (meter : StateGasMeter) : Floored meter (GasMeter.commit meter) :=
  fun hr _ => ⟨hr, hr⟩

/-! ## The fresh slots of the first frame -/

open EthLib.Execution.State (Account StateError TransactionState)

/-- A change of an account adds no fresh slot: it keeps every word, or deletes the account. -/
private theorem freshSlots_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    tx'.freshSlots ⊆ tx.freshSlots := by
  rintro ⟨other, key⟩ hmem
  rw [TransactionState.mem_freshSlots] at hmem ⊢
  rw [TransactionState.getStorageOriginal_modifyState h,
    TransactionState.getStorage_modifyState h] at hmem
  split_ifs at hmem
  · exact absurd rfl hmem.2
  · exact hmem

/-- Setting the code of an address adds no fresh slot. -/
private theorem freshSlots_setCode {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') :
    tx'.freshSlots ⊆ tx.freshSlots := by
  dsimp only [TransactionState.setCode] at h
  split at h
  · exact freshSlots_modifyState h
  · -- A new entry of code is no word of the storage.
    exact fun _ hslot => freshSlots_modifyState h hslot

/-- A record of an account read keeps the fresh slots. -/
private theorem freshSlots_recordAccountRead (tx : TransactionState) (address : Address) :
    (tx.recordAccountRead address).freshSlots = tx.freshSlots :=
  rfl

/-- An authorization that sets the code of its authority adds no fresh slot. -/
private theorem freshSlots_delegate {state state' : TransactionState} {authority : Address}
    {auth : Authorization} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) :
    state'.freshSlots ⊆ state.freshSlots := by
  obtain ⟨coded, hcode, h⟩ := bind_ok_iff.mp h
  obtain ⟨bumped, hnonce, h⟩ := bind_ok_iff.mp h
  cases h
  exact (freshSlots_modifyState hnonce).trans (freshSlots_setCode hcode)

/-- One authorization adds no fresh slot. -/
private theorem freshSlots_applyAuthorization {Meter : Type} [GasMeter Meter] {chainId : Nat}
    {done done' : Delegations Meter} {auth : Authorization}
    (h : applyAuthorization fork chainId done auth = .ok done') :
    done'.state.freshSlots ⊆ done.state.freshSlots := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact subset_rfl
  · exact subset_rfl
  · -- The payment keeps the state, and a record of a read keeps every word.
    obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    have hread := freshSlots_recordAccountRead done.state authority
    exact hread ▸ freshSlots_delegate hdelegate

/-- A list of authorizations adds no fresh slot. -/
private theorem freshSlots_foldlM_applyAuthorization {Meter : Type} [GasMeter Meter]
    {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      done.state.freshSlots ⊆ start.state.freshSlots
  | [], _, _, h => by
    cases h
    exact subset_rfl
  | _ :: _, _, _, h => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    exact (freshSlots_foldlM_applyAuthorization h).trans (freshSlots_applyAuthorization hnext)

/-- The first frame of a message has no new fresh slot, and runs at the address of the message.

A creation runs at an address with no nonce or code.

A call whose frame holds code goes to a recipient with a nonce or code.

The recipient holds that code, or a delegation indicator. -/
private theorem prepareFirstFrame_slots {Meter : Type} [GasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    first.state.freshSlots ⊆ state.freshSlots ∧
      first.message.currentTarget = message.currentTarget ∧
      (message.target = none → ¬HasNonceOrCode first.state message.currentTarget) ∧
      ∀ target, message.target = some target → first.message.code.size ≠ 0 →
        HasNonceOrCode first.state target := by
  unfold prepareFirstFrame at h
  split at h
  · rename_i htgt
    dsimp only at h
    split at h
    · rename_i hdep
      -- A creation reads its address, which has no nonce and no code.
      obtain ⟨hn, hc, -⟩ := TransactionState.accountDeployable_eq_true_iff.mp hdep
      split at h <;>
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        refine ⟨subset_of_eq (freshSlots_recordAccountRead _ _), rfl, fun _ hnc => ?_,
          fun _ ht => by simp [htgt] at ht⟩
        rcases hnc with hnc | hnc
        · simp only [FirstFrame.ofMeter, TransactionState.getAccount_recordAccountRead] at hn hnc
          omega
        · exact hnc (by simpa [FirstFrame.ofMeter] using hc)
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target htgt
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    have vdone : done.state.freshSlots ⊆ state.freshSlots :=
      freshSlots_foldlM_applyAuthorization (start := ⟨state, _, 0, _, paid, ∅⟩) hdone
    dsimp only at h
    generalize hs1 : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = s1 at h
    have v1 : s1.freshSlots ⊆ state.freshSlots := by
      rw [← hs1]
      split
      · rw [freshSlots_recordAccountRead]
        exact vdone
      · exact vdone
    split at h
    all_goals
      obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, hcode, h⟩ := bind_ok_iff.mp h
      -- The empty code hash gives the empty code, so a recipient with code has a code hash.
      have hheld : code.size ≠ 0 → HasNonceOrCode s1 target := by
        intro hsz
        refine .inr fun hempty => hsz ?_
        have hget := mapError_ok_iff.mp hcode
        rw [TransactionState.getAccount_recordAccountRead, hempty,
          TransactionState.getCode_recordAccountRead] at hget
        simp only [TransactionState.getCode, ↓reduceIte, Except.ok.injEq] at hget
        rw [← hget]
        rfl
      split at h
      · -- A delegate comes from a delegation indicator, which is not empty.
        rename_i delegate hd
        have hsz : code.size ≠ 0 := by
          split at hd
          · unfold delegatedAddress at hd
            split at hd
            · rename_i hv
              simp only [isValidDelegation, Bool.and_eq_true, decide_eq_true_eq] at hv
              rw [hv.1, DELEGATION_SIZE]
              omega
            · cases hd
          · cases hd
        have hcur := hheld hsz
        split at h
        all_goals
          obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          refine ⟨?_, rfl, fun hn => by simp [htgt] at hn, fun t ht _ => ?_⟩
          · show ((s1.recordAccountRead target).recordAccountRead delegate).freshSlots ⊆ _
            rw [freshSlots_recordAccountRead, freshSlots_recordAccountRead]
            exact v1
          · obtain rfl : target = t := Option.some.inj (htgt.symm.trans ht)
            exact hcur
      · -- With no delegate, the frame runs the code of its recipient.
        cases h
        refine ⟨?_, rfl, fun hn => by simp [htgt] at hn, fun t ht hsz => ?_⟩
        · show (s1.recordAccountRead target).freshSlots ⊆ _
          rw [freshSlots_recordAccountRead]
          exact v1
        · obtain rfl : target = t := Option.some.inj (htgt.symm.trans ht)
          exact hheld hsz

/-! ## The net state gas of the message -/

/-- From Glamsterdam, the message of a transaction uses a net state gas of at least zero.

The state it starts from must have no fresh slot, as a transaction with no storage write has.

A call must run at its recipient, as the message of a transaction does. -/
theorem processMessageCall_stateGasUsed_nonneg
    (hfork : .glamsterdam ≤ fork) {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput} (hfresh : state.freshSlots = ∅)
    (recipient : ∀ target, message.target = some target → target = message.currentTarget)
    (h : processMessageCall (Meter := StateGasMeter) chainId message state substate auths paid =
      .ok output) :
    0 ≤ output.stateGasUsed := by
  rw [processMessageCall_unfold] at h
  split at h
  · -- A halt before the first frame uses no state gas.
    split at h
    · cases h
    · cases h
      simp [CallOutput.ofHalt]
  rename_i first hfirst
  -- The meter of the first frame holds at most its starting reservoir, so its floor is not below 0.
  obtain ⟨hres, hbase⟩ := meter_prepareFirstFrame (Q := Floored) (fun _ hr hb => ⟨hr, hb⟩)
    Floored.trans Floored.charge Floored.chargeState Floored.commit hfirst
    (Nat.le_refl _) (Nat.le_refl _)
  have hfloor : 0 ≤ min first.meter.stateGasUsed first.meter.restore.stateGasUsed := by
    simp only [StateGasMeter.stateGasUsed, StateGasMeter.restore]
    omega
  -- The state of the first frame counts no slot.
  obtain ⟨hslots, hcur, hcreate, hcall⟩ := prepareFirstFrame_slots hfirst
  have hzero : (nonceOrCodeFreshSlots first.state).card = 0 := by
    rw [hfresh, Finset.subset_empty] at hslots
    simp [nonceOrCodeFreshSlots, hslots]
  -- A frame that pays for its slots from that meter then uses a net state gas of at least 0.
  have finish : ∀ (evm : Evm fork StateGasMeter) (refund : Nat) touched,
      MessagePays first.message first.state first.substate first.meter evm →
      0 ≤ (CallOutput.ofFrame evm refund touched).stateGasUsed := by
    intro evm refund touched hpays
    obtain ⟨-, -, hpays⟩ := hpays
    have hs : (CallOutput.ofFrame evm refund touched).stateGasUsed =
        StateGasMeter.stateGasUsed evm.gas := by
      unfold CallOutput.ofFrame
      split <;> rfl
    rw [hs]
    rw [hzero] at hpays
    have hcount : (0 : Int) ≤ GasCosts.STORAGE_SET_STATE_GAS *
        (((nonceOrCodeFreshSlots evm.state).card : Int) - ((0 : Nat) : Int)) :=
      Int.mul_nonneg (Int.natCast_nonneg _) (by omega)
    omega
  split at h
  · -- A creation runs at an address with no nonce or code.
    rename_i htgt
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    exact finish _ _ _ (processCreateMessage_messagePays hfork (hcur ▸ hcreate htgt) hrun)
  · -- A call runs the code of its recipient, the address it runs at.
    rename_i target htgt
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    refine finish _ _ _ (processMessage_messagePays hfork (fun hsz => ?_) hrun)
    rw [hcur, ← recipient target htgt]
    exact hcall target htgt hsz

/-- Buying gas adds no fresh slot, since it raises a nonce and takes a fee. -/
private theorem freshSlots_buyGas {env : BlockEnvironment fork} {state state' : TransactionState}
    {sender : Address} {tx : Transaction} (h : buyGas env state sender tx = .ok state') :
    state'.freshSlots ⊆ state.freshSlots := by
  unfold buyGas at h
  obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp h
  exact (freshSlots_modifyState h2).trans (freshSlots_modifyState h1)

/-- From Glamsterdam, a transaction leaves at most its gas limit less its intrinsic gas.

What it leaves is the execution gas left and the reservoir left of its message.

So its gas used before the refund, the gas limit less both, never floors at zero.

The run named here is the transaction's: its target, its paid state, its message and its call. -/
theorem processTransaction_gasLeft_le_of_glamsterdam {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    (hGlam : .glamsterdam ≤ fork) (h : processTransaction env block included tx = .ok out) :
    let gas := allocateGas fork tx included.intrinsicGas
    ∃ target bought message output,
      messageTarget included.sender
          ((State.TransactionState.ofBlock block).getAccount included.sender).nonce tx =
        .ok target ∧
      buyGas env (State.TransactionState.ofBlock block) included.sender tx = .ok bought ∧
      transactionMessage env ⟨included.sender, included.gasPrice, fun _ => tx.blobHashes, some⟩
          bought included.sender target gas.execution tx = .ok message ∧
      processMessageCall (Meter := StateGasMeter) env.chainId.toNat
          { message with reservoir := gas.reservoir } bought
          (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
          (paidWrites included.sender target tx) = .ok output ∧
      output.gasLeft + output.reservoir ≤ tx.gas.toNat - included.intrinsicGas := by
  obtain ⟨target, bought, message, output, hTarget, hBought, hMessage, hOutput, -, -⟩ :=
    processTransaction_gasUsed_of_glamsterdam hGlam (processTransaction_lt_hegota h) h
  refine ⟨target, bought, message, output, hTarget, hBought, hMessage, hOutput, ?_⟩
  -- The paid state has no fresh slot, since buying gas writes no word of the storage.
  have hfresh : bought.freshSlots = ∅ := by
    have hsub := freshSlots_buyGas hBought
    rwa [TransactionState.freshSlots_ofBlock, Finset.subset_empty] at hsub
  -- A call of a transaction runs at its recipient.
  have hrecipient : ∀ t, ({ message with reservoir := (allocateGas fork tx
      included.intrinsicGas).reservoir } : Message fork).target = some t →
      t = ({ message with reservoir := (allocateGas fork tx
        included.intrinsicGas).reservoir } : Message fork).currentTarget := by
    intro t ht
    obtain ⟨hto, hcur⟩ := target_transactionMessage hMessage
    dsimp only at ht ⊢
    rw [hto] at ht
    rw [hcur]
    unfold messageTarget at hTarget
    rw [ht] at hTarget
    exact Except.ok.inj hTarget
  have hnonneg := processMessageCall_stateGasUsed_nonneg hGlam hfresh hrecipient
    hOutput
  -- The run leaves at most what it is given, the gas limit less the intrinsic gas.
  have hsum := allocateGas_add fork tx included.intrinsicGas
  have hmg := gas_transactionMessage hMessage
  have hheld := processMessageCall_spent_le hOutput
  dsimp only at hheld
  rw [hmg] at hheld
  omega

end EthLib.Execution.Transactions
