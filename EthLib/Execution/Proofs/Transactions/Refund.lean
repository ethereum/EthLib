module

public import EthLib.Execution.Proofs.Evm.Call.Refund
public import EthLib.Execution.Proofs.Transactions.Rebuild
public import EthLib.Execution.Proofs.Transactions.StorageAt

/-!
# Proofs: the refund counter that a transaction settles is never negative

The message of a transaction starts with no cleared slot, so its counter ends at least at zero.

That needs a block state where accounts with nonce 0 and no code, missing ones too, hold no storage.

It also needs every delegation indicator to come with a nonce.

Source: [EIP-2200][eip2200], the refunds of net gas metering, and [EIP-7523][eip7523].

[eip2200]: https://eips.ethereum.org/EIPS/eip-2200#specification
[eip7523]: https://eips.ethereum.org/EIPS/eip-7523#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## States with no write of storage -/

/-- The transaction has written no word of storage yet. -/
def NoStorageWrite (tx : TransactionState) : Prop :=
  ∀ address key, tx.storageWrites.slot address key = none

/-- A transaction with no write has written no word of storage. -/
theorem noStorageWrite_ofBlock (block : BlockState) : NoStorageWrite (.ofBlock block) :=
  fun _ _ => by simp [TransactionState.ofBlock, StorageMap.slot]

/-- A change of an account writes no word of storage: it keeps the writes, or drops some. -/
theorem NoStorageWrite.modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (hw : NoStorageWrite tx)
    (h : tx.modifyState fork address f = .ok tx') : NoStorageWrite tx' := by
  intro other key
  rcases storage_modifyState h with ⟨hs, -⟩ | ⟨-, hs, -⟩
  · rw [hs]
    exact hw other key
  · have := hw other key
    simp only [StorageMap.slot, hs, Std.ExtTreeMap.getElem?_erase] at this ⊢
    split <;> simp_all

/-- New code writes no word of storage. -/
theorem NoStorageWrite.setCode {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (hw : NoStorageWrite tx) (h : tx.setCode fork address code = .ok tx') :
    NoStorageWrite tx' := by
  dsimp only [TransactionState.setCode] at h
  split at h <;>
  · refine NoStorageWrite.modifyState ?_ h
    exact fun a k => hw a k

/-- The purchase of gas writes no word of storage. -/
theorem NoStorageWrite.buyGas {env : BlockEnvironment fork} {state bought : TransactionState}
    {sender : Address} {tx : Transaction} {lifted : LiftedRules} (hw : NoStorageWrite state)
    (h : Transactions.buyGas env state sender tx lifted = .ok bought) : NoStorageWrite bought := by
  unfold Transactions.buyGas at h
  obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp h
  exact (hw.modifyState h1).modifyState h2

/-- The first frame of a message writes no word of storage. -/
theorem NoStorageWrite.prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter} (hw : NoStorageWrite state)
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    NoStorageWrite first.state :=
  rel_prepareFirstFrame (R := fun s s' => NoStorageWrite s → NoStorageWrite s') (fun _ => id)
    (fun hab hbc hw => hbc (hab hw)) (fun _ _ hw => hw) (fun h hw => hw.modifyState h)
    (fun h hw => hw.setCode h) h hw

/-! ## No cleared slot at the start -/

/-- Under the rebuild property, a state with no write of storage has no cleared slot.

No account with nonce 0 and no code may hold storage in the block state.

A word that was not zero before the transaction comes from the block, and no wipe hid it. -/
theorem clearedSlots_eq_empty {block : BlockState} {tx : TransactionState}
    (valid : RebuildState block tx) (empty : Rebuildable block) (hw : NoStorageWrite tx) :
    tx.clearedSlots = ∅ := by
  ext ⟨address, key⟩
  simp only [TransactionState.mem_clearedSlots, Finset.notMem_empty, iff_false, not_and]
  intro horig hzero
  -- The word before the transaction is the word of the block, at an account not created.
  have hcreated : address ∉ tx.createdAccounts := by
    intro hc
    simp [TransactionState.getStorageOriginal, hc] at horig
  have hblock : tx.getStorageOriginal address key =
      (TransactionState.ofBlock block).getStorage address key := by
    rw [← valid.parent]
    simp only [TransactionState.getStorageOriginal, hcreated, ite_false]
    simp [TransactionState.getStorage, TransactionState.ofBlock, StorageMap.slot]
    rfl
  -- A wipe is at an account with no nonce or code in the block, which holds no storage there.
  have hwipe : ∀ other, other ∈ tx.storageClears →
      ∀ key, (TransactionState.ofBlock block).getStorage other key = 0 := fun other hmem =>
    empty.storage other (not_hasNonceOrCode_iff.mp (valid.clears other hmem)).1
      (not_hasNonceOrCode_iff.mp (valid.clears other hmem)).2
  -- With no write, the word now is the word of the block too.
  have hnow := valid.getStorage_of_slot_eq_none hwipe (hw address key)
  rw [hnow, ← hblock] at hzero
  exact horig hzero

/-- Under the rebuild property, a state with no write of storage counts no cleared slot. -/
theorem nonceOrCodeClearedSlots_eq_empty {block : BlockState} {tx : TransactionState}
    (valid : RebuildState block tx) (empty : Rebuildable block) (hw : NoStorageWrite tx) :
    nonceOrCodeClearedSlots tx = ∅ := by
  unfold nonceOrCodeClearedSlots nonceOrCodeSlots
  rw [clearedSlots_eq_empty valid empty hw]
  rfl

/-! ## The message -/

/-- The frame that ends the message of a transaction, when it succeeds, has a counter of at least 0.

The state that the message starts from must have the rebuild property and no write of storage.

No account with nonce 0 and no code may hold storage in its block state.

The substate must start with a counter of at least zero.

The caller must have a nonce or code, and a call must run at its recipient. -/
theorem prepareFirstFrame_refundCounter_nonneg [LawfulGasMeter Meter] {block : BlockState}
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (valid : RebuildState block state) (empty : Rebuildable block) (hw : NoStorageWrite state)
    (hcaller : HasNonceOrCode state message.caller)
    (htarget : ∀ target, message.target = some target → message.currentTarget = target)
    (hsub : 0 ≤ substate.refundCounter)
    (hfirst : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    (∀ ended, message.target ≠ none →
      processMessage fork first.message first.state first.substate first.meter first.held =
        .ok ended →
      ended.val.error = none → 0 ≤ ended.val.substate.refundCounter) ∧
    (∀ ended, message.target = none →
      processCreateMessage fork first.message first.state first.substate first.meter
        first.held = .ok ended →
      ended.val.error = none → 0 ≤ ended.val.substate.refundCounter) := by
  have hsub' : 0 ≤ first.substate.refundCounter := by
    rw [refundCounter_prepareFirstFrame hfirst]
    exact hsub
  by_cases hfork : fork < .istanbul
  · -- Before Istanbul, no write lowers the counter.
    exact ⟨fun _ _ h hok =>
        hsub'.trans (processMessage_refundCounter_le_of_lt_istanbul hfork h hok),
      fun _ _ h hok =>
        hsub'.trans (processCreateMessage_refundCounter_le_of_lt_istanbul hfork h hok)⟩
  -- From Istanbul, the first frame has no cleared slot, and the counter pays for those it adds.
  have hsd : .spuriousDragon ≤ fork := Nat.le_trans (by decide) (Nat.not_lt.mp hfork)
  obtain ⟨vfirst, -, hdep, hcode⟩ := prepareFirstFrame_rebuildState valid hcaller htarget hfirst
  have hzero : clearedRefund fork first.state = 0 := by
    unfold clearedRefund
    rw [nonceOrCodeClearedSlots_eq_empty vfirst empty (hw.prepareFirstFrame hfirst)]
    simp
  have hclear : ∀ (s : TransactionState), 0 ≤ clearedRefund fork s := fun s =>
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  refine ⟨fun ended hne h hok => ?_, fun ended hnone h hok => ?_⟩
  · have := processMessage_clearedRefund_le hsd (hcode hne) h hok
    have := hclear ended.val.state
    omega
  · -- A creation goes to an address with no nonce or code.
    have hnc : ¬HasNonceOrCode first.state first.message.currentTarget := by
      obtain ⟨hn, hc⟩ := TransactionState.accountDeployable_eq_true_iff.mp (hdep hnone)
      exact fun h => h.elim (fun h1 => by omega) (fun h2 => h2 hc)
    have := processCreateMessage_clearedRefund_le hsd hnc h hok
    have := hclear ended.val.state
    omega

/-- The message of a transaction that succeeds settles the refund of its frame, with no clamp.

That refund is the counter of the frame that ends the message, at least zero.

A call adds the refund of its authorizations.

The hypotheses on the state are those of the frame. -/
theorem processMessageCall_refundCounter_nonneg [LawfulGasMeter Meter] {block : BlockState}
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (valid : RebuildState block state) (empty : Rebuildable block) (hw : NoStorageWrite state)
    (hcaller : HasNonceOrCode state message.caller)
    (htarget : ∀ target, message.target = some target → message.currentTarget = target)
    (hsub : 0 ≤ substate.refundCounter)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output)
    (hok : output.error = none) :
    ∃ (first : FirstFrame fork Meter) (ended : {evm : Evm fork Meter //
        GasMeter.gasHeld evm.gas ≤ first.message.gas}),
      prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
        .ok first ∧
      (if message.target = none then
        processCreateMessage fork first.message first.state first.substate first.meter
          first.held = .ok ended
      else
        processMessage fork first.message first.state first.substate first.meter first.held =
          .ok ended) ∧
      (output.refund : Int) =
        (if message.target = none then 0 else first.refund) + ended.val.substate.refundCounter ∧
      0 ≤ ended.val.substate.refundCounter := by
  rw [processMessageCall_unfold] at h
  rcases hfirst : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · -- A halt before the first frame ends with an error.
    rw [hfirst] at h
    dsimp only at h
    split at h
    · cases h
    · cases h
      simp [CallOutput.ofHalt] at hok
  rw [hfirst] at h
  dsimp only at h
  obtain ⟨hcall, hcreate⟩ :=
    prepareFirstFrame_refundCounter_nonneg valid empty hw hcaller htarget hsub hfirst
  -- A frame that succeeds passes on its counter, which is not negative.
  have hframe : ∀ (evm : Evm fork Meter) (refund : Nat) (touched : Std.ExtTreeSet Address),
      (CallOutput.ofFrame evm refund touched).error = none →
        evm.error = none ∧ ((CallOutput.ofFrame evm refund touched).refund : Int) =
          refund + evm.substate.refundCounter.toNat := by
    intro evm refund touched hok
    have he : evm.error = none := by
      unfold CallOutput.ofFrame at hok
      split at hok <;> simp_all
    refine ⟨he, ?_⟩
    unfold CallOutput.ofFrame
    simp [he]
  split at h
  · rename_i hnone
    obtain ⟨ended, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    obtain ⟨herr, hrefund⟩ := hframe _ _ _ hok
    have hpos := hcreate ended hnone hrun herr
    refine ⟨first, ended, rfl, by simpa [hnone] using hrun, ?_, hpos⟩
    rw [hrefund, Int.toNat_of_nonneg hpos]
    simp [hnone]
  · rename_i target hsome
    obtain ⟨ended, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    obtain ⟨herr, hrefund⟩ := hframe _ _ _ hok
    have hne : message.target ≠ none := by simp [hsome]
    have hpos := hcall ended hne hrun herr
    refine ⟨first, ended, rfl, by simpa [hsome] using hrun, ?_, hpos⟩
    rw [hrefund, Int.toNat_of_nonneg hpos]
    simp [hsome]

/-- The state of a transaction after it buys its gas is ready for its message.

It has the rebuild property and no write of storage, and its sender has a nonce.

The block state before it must hold no storage at an account with nonce 0 and no code.

It must hold no delegation indicator at an account with nonce 0. -/
theorem buyGas_refundReady {env : BlockEnvironment fork} {block : BlockState}
    {sender : Address} {tx : Transaction} {bought : TransactionState}
    (valid : Rebuildable block) (delegations : DelegationsHaveNonce (.ofBlock block))
    (h : buyGas env (.ofBlock block) sender tx = .ok bought) :
    RebuildState block bought ∧ NoStorageWrite bought ∧ HasNonceOrCode bought sender := by
  obtain ⟨vb, -, hnonce⟩ := buyGas_rebuildState (RebuildState.ofBlock valid.code delegations) h
  exact ⟨vb, (noStorageWrite_ofBlock block).buyGas h, .inl hnonce⟩

/-- A run of a transaction meets the hypotheses on the start of its message.

Its block state must hold no storage at an account with nonce 0 and no code.

It must hold no delegation indicator at an account with nonce 0.

So the refund that it settles is the counter of the frame that ends its message, at least zero. -/
theorem TransactionRun.refundReady [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    {target : Address} {bought : TransactionState} {message : Message fork}
    {output : CallOutput} {settled : TransactionState}
    (valid : Rebuildable block) (delegations : DelegationsHaveNonce (.ofBlock block))
    (h : TransactionRun Meter env block included tx out target bought message output settled) :
    RebuildState block bought ∧ NoStorageWrite bought ∧ HasNonceOrCode bought message.caller ∧
      (∀ t, message.target = some t → message.currentTarget = t) ∧
      (startSubstate fork env.coinbase included.sender target tx).refundCounter = 0 := by
  obtain ⟨hTarget, hBought, hMessage, -⟩ := h
  obtain ⟨vb, hw, hsender⟩ := buyGas_refundReady valid delegations hBought
  refine ⟨vb, hw, caller_transactionMessage hMessage ▸ hsender, fun t ht => ?_, rfl⟩
  -- A call of a transaction runs at its recipient.
  obtain ⟨hto, hcur⟩ := target_transactionMessage hMessage
  rw [hcur]
  rw [hto] at ht
  unfold messageTarget at hTarget
  rw [ht] at hTarget
  exact (Except.ok.inj hTarget).symm

end EthLib.Execution.Transactions
