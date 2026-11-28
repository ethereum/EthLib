module

public import EthLib.Execution.Proofs.Evm.Call.Refund
public import EthLib.Execution.Proofs.Transactions.Rebuild
public import EthLib.Execution.Proofs.Transactions.StorageAt

/-!
# Proofs: the refund counter that a transaction settles is never negative

The message of a transaction starts with no cleared slot, so its counter ends at least at zero.

That needs that each wipe of storage before its first frame runs hid only zero words.

It also needs every delegation indicator to come with a nonce.

For a run of a transaction, the wipes hide zeros when no empty account holds storage.

Source: [EIP-2200][eip2200], the refunds of net gas metering, and [EIP-7523][eip7523].

[eip2200]: https://eips.ethereum.org/EIPS/eip-2200#specification
[eip7523]: https://eips.ethereum.org/EIPS/eip-7523#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State
open EthLib.Cryptography.Hash.Keccak (keccak256)

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

/-- Each storage that the transaction wiped held only zero words in the block state. -/
def WipesHideZeros (block : BlockState) (tx : TransactionState) : Prop :=
  ∀ address ∈ tx.storageClears, ∀ key, (TransactionState.ofBlock block).getStorage address key = 0

/-- On a rebuildable block state, each wipe of a state with the rebuild property hid zeros. -/
theorem _root_.EthLib.Execution.Evm.RebuildEnd.wipesHideZeros {block : BlockState}
    {tx : TransactionState} (valid : RebuildEnd block tx) (empty : Rebuildable block) :
    WipesHideZeros block tx :=
  -- A wipe is at an account with no nonce or code in the block, which holds no storage there.
  fun other hmem => empty.storage other (not_hasNonceOrCode_iff.mp (valid.clears other hmem)).1
    (not_hasNonceOrCode_iff.mp (valid.clears other hmem)).2

/-- Under the rebuild property, a state with no write of storage has no cleared slot.

Each of its wipes must have hidden only zero words of the block state.

A word that was not zero before the transaction comes from the block, and no wipe hid it. -/
theorem clearedSlots_eq_empty {block : BlockState} {tx : TransactionState}
    (valid : RebuildState block tx) (hwipe : WipesHideZeros block tx) (hw : NoStorageWrite tx) :
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
  -- With no write, the word now is the word of the block too.
  have hnow := valid.getStorage_of_slot_eq_none hwipe (hw address key)
  rw [hnow, ← hblock] at hzero
  exact horig hzero

/-- Under the rebuild property, a state with no write of storage counts no cleared slot.

Each of its wipes must have hidden only zero words of the block state. -/
theorem nonceOrCodeClearedSlots_eq_empty {block : BlockState} {tx : TransactionState}
    (valid : RebuildState block tx) (hwipe : WipesHideZeros block tx) (hw : NoStorageWrite tx) :
    nonceOrCodeClearedSlots tx = ∅ := by
  unfold nonceOrCodeClearedSlots nonceOrCodeSlots
  rw [clearedSlots_eq_empty valid hwipe hw]
  rfl

/-! ## The message -/

/-- The frame that ends the message of a transaction, when it succeeds, has a counter of at least 0.

It holds when each wipe before the first frame runs hid only zero words of the block state. -/
theorem prepareFirstFrame_refundCounter_nonneg_of_wipesHideZeros [LawfulGasMeter Meter]
    {block : BlockState} {chainId : Nat} {message : Message fork} {state : TransactionState}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {first : FirstFrame fork Meter}
    -- The state that the message starts from has the rebuild property and no write of storage.
    (valid : RebuildState block state) (hw : NoStorageWrite state)
    -- The caller has a nonce or code, and a call runs at its recipient.
    (hcaller : HasNonceOrCode state message.caller)
    (htarget : ∀ target, message.target = some target → message.currentTarget = target)
    -- The substate starts with a counter of at least zero.
    (hsub : 0 ≤ substate.refundCounter)
    (hfirst : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first)
    -- Each wipe in the state of the first frame hid only zero words of the block state.
    --
    -- For a transaction, those are empty authorities that an authorization to address 0 names.
    (hwipe : WipesHideZeros block first.state) :
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
    rw [nonceOrCodeClearedSlots_eq_empty vfirst hwipe (hw.prepareFirstFrame hfirst)]
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

/-- The frame that ends the message of a transaction, when it succeeds, has a counter of at least 0.

The hypotheses are those above, with no account of nonce 0 and no code holding storage instead.

Mainnet meets that hypothesis only once a fork applies EIP-8253, for its 28 accounts. -/
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
      ended.val.error = none → 0 ≤ ended.val.substate.refundCounter) :=
  prepareFirstFrame_refundCounter_nonneg_of_wipesHideZeros valid hw hcaller htarget hsub hfirst
    ((prepareFirstFrame_rebuildState valid hcaller htarget hfirst).1.wipesHideZeros empty)

/-- The message of a transaction that succeeds settles the refund of its frame, with no clamp.

That refund is the counter of the frame that ends the message, at least zero.

A call adds the refund of its authorizations.

The hypotheses on the state are those of the frame. -/
theorem processMessageCall_refundCounter_nonneg_of_wipesHideZeros [LawfulGasMeter Meter]
    {block : BlockState} {chainId : Nat} {message : Message fork} {state : TransactionState}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {output : CallOutput}
    (valid : RebuildState block state) (hw : NoStorageWrite state)
    (hcaller : HasNonceOrCode state message.caller)
    (htarget : ∀ target, message.target = some target → message.currentTarget = target)
    (hsub : 0 ≤ substate.refundCounter)
    -- Each wipe in the state of the first frame hid only zero words of the block state.
    (hwipe : ∀ first, prepareFirstFrame (Meter := Meter) chainId message state substate auths
      paid = .ok first → WipesHideZeros block first.state)
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
    prepareFirstFrame_refundCounter_nonneg_of_wipesHideZeros valid hw hcaller htarget hsub hfirst
      (hwipe first hfirst)
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

/-- The message of a transaction that succeeds settles the refund of its frame, with no clamp.

The hypotheses are those above, with no account of nonce 0 and no code holding storage instead.

Mainnet meets that hypothesis only once a fork applies EIP-8253, for its 28 accounts. -/
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
      0 ≤ ended.val.substate.refundCounter :=
  processMessageCall_refundCounter_nonneg_of_wipesHideZeros valid hw hcaller htarget hsub
    (fun _ hfirst =>
      (prepareFirstFrame_rebuildState valid hcaller htarget hfirst).1.wipesHideZeros empty)
    h hok

/-- The state of a transaction after it buys its gas is ready for its message.

It has the rebuild property and no write of storage, and its sender has a nonce. -/
theorem buyGas_refundReady {env : BlockEnvironment fork} {block : BlockState}
    {sender : Address} {tx : Transaction} {bought : TransactionState}
    -- Each code read in the block state before it has its hash.
    (code : ∀ hash code, (TransactionState.ofBlock block).getCode hash = .ok code →
      keccak256 code = hash)
    -- That state holds no delegation indicator at an account with nonce 0.
    (delegations : DelegationsHaveNonce (.ofBlock block))
    (h : buyGas env (.ofBlock block) sender tx = .ok bought) :
    RebuildState block bought ∧ NoStorageWrite bought ∧ HasNonceOrCode bought sender := by
  obtain ⟨vb, -, hnonce⟩ := buyGas_rebuildState (RebuildState.ofBlock code delegations) h
  exact ⟨vb, (noStorageWrite_ofBlock block).buyGas h, .inl hnonce⟩

/-- A run of a transaction meets the hypotheses on the start of its message.

So the refund that it settles is the counter of the frame that ends its message, at least zero.

That also needs that the wipes of its first frame hid only zero words. -/
theorem TransactionRun.refundReady [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    {target : Address} {bought : TransactionState} {message : Message fork}
    {output : CallOutput} {settled : TransactionState}
    -- Each code read in its block state has its hash.
    (code : ∀ hash code, (TransactionState.ofBlock block).getCode hash = .ok code →
      keccak256 code = hash)
    -- That state holds no delegation indicator at an account with nonce 0.
    (delegations : DelegationsHaveNonce (.ofBlock block))
    (h : TransactionRun Meter env block included tx out target bought message output settled) :
    RebuildState block bought ∧ NoStorageWrite bought ∧ HasNonceOrCode bought message.caller ∧
      (∀ t, message.target = some t → message.currentTarget = t) ∧
      (startSubstate fork env.coinbase included.sender target tx).refundCounter = 0 := by
  obtain ⟨vb, hcaller, htarget⟩ := h.messageReady code delegations
  exact ⟨vb, (noStorageWrite_ofBlock block).buyGas h.2.1, hcaller, htarget, rfl⟩

/-! ## The wipes of a transaction -/

/-- No account that is empty in the block state holds a nonzero word of storage.

An empty account has nonce 0, no code and balance 0. -/
def EmptyAccountsHoldNoStorage (block : BlockState) : Prop :=
  ∀ address, TransactionState.EmptyAt address (.ofBlock block) →
    ∀ key, (TransactionState.ofBlock block).getStorage address key = 0

/-- A rebuildable block state holds no storage at an empty account. -/
theorem _root_.EthLib.Execution.State.Rebuildable.emptyAccountsHoldNoStorage {block : BlockState}
    (empty : Rebuildable block) : EmptyAccountsHoldNoStorage block :=
  fun address hempty => empty.storage address hempty.1 hempty.2.1

/-- Each storage that a first frame of a run wipes held only zeros, or is at an empty account.

Any first frame from the state after the purchase of gas counts.

The zeros and the empty account are those of the block state. -/
theorem TransactionRun.wipes [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    {target : Address} {bought : TransactionState} {message : Message fork}
    {output : CallOutput} {settled : TransactionState} {chainId reservoir : Nat}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {first : FirstFrame fork Meter}
    -- Each code read in its block state has its hash.
    (code : ∀ hash code, (TransactionState.ofBlock block).getCode hash = .ok code →
      keccak256 code = hash)
    -- That state holds no delegation indicator at an account with nonce 0.
    (delegations : DelegationsHaveNonce (.ofBlock block))
    (h : TransactionRun Meter env block included tx out target bought message output settled)
    (hfirst : prepareFirstFrame (Meter := Meter) chainId { message with reservoir } bought
      substate auths paid = .ok first)
    {address : Address} (hmem : address ∈ first.state.storageClears) :
    (∀ key, (TransactionState.ofBlock block).getStorage address key = 0) ∨
      TransactionState.EmptyAt address (.ofBlock block) := by
  obtain ⟨vb, hcaller, htarget⟩ := h.messageReady code delegations
  -- The account has no code in the block state, since the state of the frame wipes it.
  have hnc := (prepareFirstFrame_rebuildState (message := { message with reservoir }) vb hcaller
    htarget hfirst).1.clears address hmem
  obtain ⟨kb, -, hcode⟩ := keptOrWipedEmpty_buyGas (address := address) h.2.1
  have codeless : CodelessAtZero address bought auths := fun _ _ _ _ =>
    hcode.trans (not_hasNonceOrCode_iff.mp hnc).2
  obtain ⟨hkept | ⟨-, hempty⟩, -⟩ :=
    kb.trans (keptOrWipedEmpty_prepareFirstFrame hfirst codeless).1
  · -- The storage is as in the block state, and the frame reads 0 there, with no write.
    refine .inl fun key => ?_
    have hw := ((noStorageWrite_ofBlock block).buyGas h.2.1).prepareFirstFrame hfirst
      address key
    rw [← congrFun hkept key]
    simp [TransactionState.getStorage, hw, hmem]
  · exact .inr hempty

/-- The first frame of a run wipes only storages of zeros when no empty account holds storage. -/
theorem TransactionRun.wipesHideZeros [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    {target : Address} {bought : TransactionState} {message : Message fork}
    {output : CallOutput} {settled : TransactionState} {chainId reservoir : Nat}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {first : FirstFrame fork Meter}
    -- Each code read in its block state has its hash.
    (code : ∀ hash code, (TransactionState.ofBlock block).getCode hash = .ok code →
      keccak256 code = hash)
    -- That state holds no delegation indicator at an account with nonce 0.
    (delegations : DelegationsHaveNonce (.ofBlock block))
    -- No account with nonce 0, no code and balance 0 holds storage there.
    (empty : EmptyAccountsHoldNoStorage block)
    (h : TransactionRun Meter env block included tx out target bought message output settled)
    (hfirst : prepareFirstFrame (Meter := Meter) chainId { message with reservoir } bought
      substate auths paid = .ok first) :
    WipesHideZeros block first.state :=
  fun _ hmem => (h.wipes code delegations hfirst hmem).elim id (empty _)

/-- The message of a run that succeeds settles the counter of the frame that ends it, at least 0.

The block state must hold no storage at an empty account, which mainnet meets. -/
theorem TransactionRun.refundCounter_nonneg [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    {target : Address} {bought : TransactionState} {message : Message fork}
    {output : CallOutput} {settled : TransactionState}
    -- Each code read in its block state has its hash.
    (code : ∀ hash code, (TransactionState.ofBlock block).getCode hash = .ok code →
      keccak256 code = hash)
    -- That state holds no delegation indicator at an account with nonce 0.
    (delegations : DelegationsHaveNonce (.ofBlock block))
    -- No account with nonce 0, no code and balance 0 holds storage there.
    (empty : EmptyAccountsHoldNoStorage block)
    (h : TransactionRun Meter env block included tx out target bought message output settled)
    (hok : output.error = none) :
    ∃ (first : FirstFrame fork Meter) (ended : {evm : Evm fork Meter //
        GasMeter.gasHeld evm.gas ≤ first.message.gas}),
      prepareFirstFrame (Meter := Meter) env.chainId.toNat
          { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir }
          bought (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
          (paidWrites included.sender target tx) = .ok first ∧
      (if message.target = none then
        processCreateMessage fork first.message first.state first.substate first.meter
          first.held = .ok ended
      else
        processMessage fork first.message first.state first.substate first.meter first.held =
          .ok ended) ∧
      (output.refund : Int) =
        (if message.target = none then 0 else first.refund) + ended.val.substate.refundCounter ∧
      0 ≤ ended.val.substate.refundCounter := by
  obtain ⟨vb, hw, hcaller, htarget, hsub⟩ := h.refundReady code delegations
  exact processMessageCall_refundCounter_nonneg_of_wipesHideZeros vb hw hcaller htarget
    (Int.le_of_eq hsub.symm) (fun _ hfirst => h.wipesHideZeros code delegations empty hfirst)
    h.2.2.2.1 hok

end EthLib.Execution.Transactions
