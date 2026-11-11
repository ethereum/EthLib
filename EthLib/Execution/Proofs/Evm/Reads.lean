module

public import EthLib.Execution.Evm.Interpreter
public import EthLib.Execution.Proofs.Evm.Instructions.AccountData
public import EthLib.Execution.Proofs.Evm.Instructions.ControlFlow
public import EthLib.Execution.Proofs.Evm.Instructions.EnvironmentData
public import EthLib.Execution.Proofs.Evm.Instructions.LogData
public import EthLib.Execution.Proofs.Evm.Instructions.MemoryData
public import EthLib.Execution.Proofs.Evm.Instructions.Return
public import EthLib.Execution.Proofs.Evm.Instructions.SelfDestruct
public import EthLib.Execution.Proofs.Evm.Instructions.StackOnly
public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Instructions.TransientStorage
public import EthLib.Execution.Proofs.Evm.Step
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the reads of an instruction

From Glamsterdam, an instruction checks the gas it knows before it reads the state.

Before Glamsterdam, that check always passes.

An exceptional halt keeps the state of the frame, so it keeps the reads that the frame made.

BALANCE, EXTCODESIZE, EXTCODECOPY and EXTCODEHASH each read the account at their address.

SELFBALANCE reads the current account.

SLOAD and SSTORE each read their slot in the storage of the current account.

SSTORE records that read even when it then halts, as EIP-7928 asks.

When it completes, its write also reads the current account.

SELFDESTRUCT reads its beneficiary even when it then halts.

When it completes, it also reads the current account.

From Paris, an account that SELFDESTRUCT leaves empty is deleted.

The keys that the transaction wrote at that account then become storage reads.

BALANCE, EXTCODESIZE, EXTCODECOPY, EXTCODEHASH, SELFBALANCE and SLOAD add only that read.

SSTORE and SELFDESTRUCT give the account reads and the storage reads at every address.

Every other instruction of the dispatch keeps the account reads and the storage reads.

The calls and the creations are outside the dispatch, and they read accounts too.

A step that fails before its read gives no frame, so it adds no read.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Before Glamsterdam, the gas check passes. -/
theorem checkGas_of_lt_glamsterdam (h : fork < .glamsterdam) (evm : Evm fork Meter)
    (amount : Nat) : checkGas evm amount = .ok () := by
  have hpre : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp [checkGas, hpre, pure, Except.pure]

/-- From Glamsterdam, the gas check passes exactly when the frame has the amount left. -/
theorem checkGas_eq_ok_iff (h : fork ≥ .glamsterdam) {evm : Evm fork Meter} {amount : Nat} :
    checkGas evm amount = .ok () ↔ amount ≤ GasMeter.gasLeft evm.gas := by
  unfold checkGas
  by_cases hlt : GasMeter.gasLeft evm.gas < amount
  · simp [h, hlt, throw, throwThe, MonadExceptOf.throw]
  · simp [h, hlt, pure, Except.pure]
    omega

/-- An exceptional halt keeps the state of the frame, with its reads. -/
theorem state_exceptionalHalt (evm : Evm fork Meter) (e : EvmError) :
    (exceptionalHalt evm e).state = evm.state := rfl

/-- BALANCE reads the account at its address. -/
theorem mem_accountReads_balanceStep {evm after : Evm fork Meter} {word : U256}
    {rest : List U256} (hs : evm.stack.val = word :: rest) (h : balanceStep evm = .ok after) :
    Base.toAddressMasked word ∈ after.state.accountReads := by
  rw [balanceStep_cons hs] at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · cases h
    exact (State.TransactionState.mem_accountReads_recordAccountRead _ _ _).mpr (.inl rfl)

/-- BALANCE adds the account at its address to the account reads.

It keeps every other read. -/
theorem reads_balanceStep {evm after : Evm fork Meter} {word : U256} {rest : List U256}
    (hs : evm.stack.val = word :: rest) (h : balanceStep evm = .ok after) :
    after.state.accountReads = evm.state.accountReads.insert (Base.toAddressMasked word) ∧
      after.state.storageReads = evm.state.storageReads := by
  rw [balanceStep_cons hs] at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · cases h
    rw [state_accessAddress]
    exact ⟨rfl, rfl⟩

/-- EXTCODESIZE adds the account at its address to the account reads.

It keeps every other read. -/
theorem reads_extcodesizeStep {evm after : Evm fork Meter} {word : U256} {rest : List U256}
    (hs : evm.stack.val = word :: rest) (h : extcodesizeStep evm = .ok after) :
    after.state.accountReads = evm.state.accountReads.insert (Base.toAddressMasked word) ∧
      after.state.storageReads = evm.state.storageReads := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, -⟩ := popWord_of_stack hs h1
  rcases hacc : accessAddress e1 (Base.toAddressMasked word) with ⟨cold, e2⟩
  have s2 : e2.state = evm.state := by
    have s := state_accessAddress e1 (Base.toAddressMasked word)
    rw [hacc] at s
    exact s.trans (popWord_sameContext h1).state
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rw [(pushWord_sameContext h4).advance.state, ← s2, ← (chargeGas_sameContext h3).state]
  exact ⟨rfl, rfl⟩

/-- EXTCODECOPY adds the account at its address to the account reads.

It keeps every other read. -/
theorem reads_extcodecopyStep {evm after : Evm fork Meter} {word start offset size : U256}
    {rest : List U256} (hs : evm.stack.val = word :: start :: offset :: size :: rest)
    (h : extcodecopyStep evm = .ok after) :
    after.state.accountReads = evm.state.accountReads.insert (Base.toAddressMasked word) ∧
      after.state.storageReads = evm.state.storageReads := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, -⟩ := popWord_of_stack hs h1
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e4 (Base.toAddressMasked word) with ⟨cold, e5⟩
  have s5 : e5.state = evm.state := by
    have s := state_accessAddress e4 (Base.toAddressMasked word)
    rw [hacc] at s
    exact s.trans ((((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
      (popWord_sameContext h3)).trans (popWord_sameContext h4)).state
  simp only [hacc] at h
  obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rw [← s5, ← (chargeGasAndMemory_sameContext h6).state]
  exact ⟨rfl, rfl⟩

/-- EXTCODEHASH adds the account at its address to the account reads.

It keeps every other read. -/
theorem reads_extcodehashStep {evm after : Evm fork Meter} {word : U256} {rest : List U256}
    (hs : evm.stack.val = word :: rest) (h : extcodehashStep evm = .ok after) :
    after.state.accountReads = evm.state.accountReads.insert (Base.toAddressMasked word) ∧
      after.state.storageReads = evm.state.storageReads := by
  rw [extcodehashStep_cons hs] at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · cases h
    rw [state_accessAddress]
    exact ⟨rfl, rfl⟩

/-- SELFBALANCE adds the current account to the account reads.

It keeps every other read.

It has no step of its own: it reads the frame once the read is recorded. -/
theorem reads_selfbalanceStep {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} (hstep : accountStep fork .selfbalance = some run)
    (h : run evm = .ok after) :
    after.state.accountReads = evm.state.accountReads.insert evm.message.currentTarget ∧
      after.state.storageReads = evm.state.storageReads := by
  simp only [accountStep] at hstep
  split at hstep
  · simp only [Option.some.injEq] at hstep
    subst hstep
    rw [(readFrame_sameContext h).state]
    exact ⟨rfl, rfl⟩
  · cases hstep

/-- SLOAD adds its slot to the storage reads of the current account.

It keeps every other read. -/
theorem reads_sloadStep {evm after : Evm fork Meter} {word : U256} {rest : List U256}
    (hs : evm.stack.val = word :: rest) (h : sloadStep evm = .ok after) :
    after.state.accountReads = evm.state.accountReads ∧
      after.state.storageReads = evm.state.storageReads.insert evm.message.currentTarget
        ((evm.state.storageReads.getD evm.message.currentTarget ∅).insert
          (U256.toBeBytes word)) := by
  rw [sloadStep_cons hs] at h
  dsimp only [Except.map] at h
  split at h
  · cases h
  · cases h
    rw [state_accessStorageKey]
    exact ⟨rfl, rfl⟩

/-- SSTORE adds its slot to the storage reads of the current account, even when it then halts.

When it halts after reading, it keeps the account reads.

When it completes, it adds the current account to the account reads. -/
theorem reads_sstoreStep {evm after : Evm fork Meter} {key new : U256} {rest : List U256}
    (hs : evm.stack.val = key :: new :: rest) (h : sstoreStep evm = .ok after) :
    after.state.storageReads = evm.state.storageReads.insert evm.message.currentTarget
        ((evm.state.storageReads.getD evm.message.currentTarget ∅).insert
          (U256.toBeBytes key)) ∧
      ((after.state.accountReads = evm.state.accountReads ∧ ∃ e, after.error = some e) ∨
        (after.state.accountReads = evm.state.accountReads.insert evm.message.currentTarget ∧
          after.error = evm.error)) := by
  unfold sstoreStep at h
  split at h
  · cases h
  obtain ⟨⟨w1, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, r1, -⟩ := popWord_of_stack hs h1
  obtain ⟨⟨w2, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, -⟩ := popWord_of_stack r1 h2
  have err1 : e1.error = evm.error := by
    obtain ⟨⟨_, _⟩, -, h1'⟩ := Base.bind_ok_iff.mp h1
    cases h1'
    rfl
  have err2 : e2.error = e1.error := by
    obtain ⟨⟨_, _⟩, -, h2'⟩ := Base.bind_ok_iff.mp h2
    cases h2'
    rfl
  have c2 := (popWord_sameContext h1).trans (popWord_sameContext h2)
  dsimp only at h
  split at h
  · cases h
  rcases hacc : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes key) with ⟨cold, e3⟩
  have s3 : e3.state = evm.state ∧ e3.error = evm.error := by
    have s := state_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes key)
    have herr : (accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes key)).2.error =
        e2.error := by
      unfold accessStorageKey
      split <;> rfl
    rw [hacc] at s herr
    exact ⟨s.trans c2.state, herr.trans (err2.trans err1)⟩
  simp only [hacc] at h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · cases h
    obtain ⟨state, hset, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have err4 : e4.error = e3.error := by
      obtain ⟨_, -, h4'⟩ := Base.bind_ok_iff.mp h4
      cases h4'
      rfl
    have err5 : e5.error = e4.error := by
      obtain ⟨_, -, h5'⟩ := Base.bind_ok_iff.mp h5
      cases h5'
      rfl
    have c5 := (chargeGas_sameContext h4).trans (chargeStateGas_sameContext h5)
    have hset' : e5.state.setStorage e2.message.currentTarget (U256.toBeBytes key) new =
        .ok state := by
      revert hset
      cases e5.state.setStorage e2.message.currentTarget (U256.toBeBytes key) new <;>
        simp [Except.mapError]
    obtain ⟨ha, hst⟩ := State.TransactionState.reads_setStorage hset'
    refine ⟨?_, .inr ⟨?_, err5.trans (err4.trans s3.2)⟩⟩
    · show state.storageReads = _
      rw [hst, c5.state]
      show (recordStorageRead e3 _ _).state.storageReads = _
      simp [recordStorageRead, State.TransactionState.recordStorageRead, s3.1, c2.message]
    · show state.accountReads = _
      rw [ha, c5.state]
      show (recordStorageRead e3 _ _).state.accountReads.insert _ = _
      simp [recordStorageRead, State.TransactionState.recordStorageRead, s3.1, c2.message]
  · refine ⟨?_, .inl ⟨?_, e, rfl⟩⟩
    · show (recordStorageRead e3 _ _).state.storageReads = _
      simp [recordStorageRead, State.TransactionState.recordStorageRead, s3.1, c2.message]
    · show (recordStorageRead e3 _ _).state.accountReads = _
      simp [recordStorageRead, State.TransactionState.recordStorageRead, s3.1]

/-- SSTORE reads its slot, whether it then completes or halts.

The slot is the top word of the stack, in the storage of the current account. -/
theorem mem_storageReads_sstoreStep {evm after : Evm fork Meter} {key new : U256}
    {rest : List U256} (hs : evm.stack.val = key :: new :: rest)
    (h : sstoreStep evm = .ok after) :
    U256.toBeBytes key ∈ after.state.storageReads.getD evm.message.currentTarget ∅ := by
  rw [(reads_sstoreStep hs h).1, Std.ExtTreeMap.getD_insert_self]
  exact Std.ExtTreeSet.mem_insert_self

/-- The transfer of SELFDESTRUCT adds the originator and the beneficiary to the account reads. -/
theorem accountReads_selfdestructTransfer {tx tx' : State.TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    tx'.accountReads = (tx.accountReads.insert originator).insert beneficiary := by
  unfold selfdestructTransfer at h
  dsimp only at h
  split at h
  · obtain ⟨mid, hmove, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨hmid, -⟩ := State.TransactionState.reads_moveEther hmove
    split at h
    · obtain ⟨hset, -⟩ := State.TransactionState.reads_setAccountBalance h
      rw [hset, hmid]
      ext a
      simp [Std.ExtTreeSet.mem_insert, or_left_comm]
    · cases h
      exact hmid
  · obtain ⟨mid, hcreate, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨hmid, -⟩ := State.TransactionState.reads_createEther hcreate
    obtain ⟨hset, -⟩ := State.TransactionState.reads_setAccountBalance h
    rw [hset, hmid]
    ext a
    simp [Std.ExtTreeSet.mem_insert, or_left_comm]

/-- The transfer of SELFDESTRUCT gives the storage reads at every address.

From Paris, an originator whose nonce and code are empty has its written keys read.

From Paris, a beneficiary that the transfer leaves empty has its written keys read.

Every other address keeps its storage reads, and before Paris every address keeps them. -/
theorem getElem?_storageReads_selfdestructTransfer {tx tx' : State.TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') (address : Address) :
    tx'.storageReads[address]? =
      if fork ≥ .paris ∧
          ((address = originator ∧
              { tx.getAccount originator with balance := 0 } = State.EMPTY_ACCOUNT) ∨
            (address = beneficiary ∧ tx'.getAccount beneficiary = State.EMPTY_ACCOUNT)) then
        (tx.destroyStorage address).storageReads[address]?
      else tx.storageReads[address]? := by
  unfold selfdestructTransfer at h
  dsimp only at h
  split at h
  · obtain ⟨mid, hmove, h⟩ := Base.bind_ok_iff.mp h
    have hsub : (tx.getAccount originator).balance - (tx.getAccount originator).balance = 0 :=
      BitVec.sub_self _
    split at h
    · obtain ⟨_, hf, hread, hother⟩ := State.TransactionState.modifyState_eq_ok h
      cases hf
      by_cases ha : address = originator
      · subst ha
        rw [State.TransactionState.getElem?_storageReads_modifyState_self h, hread]
        have hm := State.TransactionState.getElem?_storageReads_moveEther hmove address
        have hw := State.TransactionState.getD_storageWrites_moveEther hmove address
        rw [hsub] at hm hw
        have hmid_orig : mid.getAccount address =
            { tx.getAccount address with balance :=
                if address = beneficiary then (tx.getAccount address).balance else 0 } := by
          by_cases hab : address = beneficiary
          · subst hab
            rw [(State.TransactionState.moveEther_self hmove).1]
            cases tx.getAccount address
            simp
          · rw [(State.TransactionState.moveEther_eq_ok hab hmove).2.2.1, hsub]
            simp [hab]
        have hsame_empty : { mid.getAccount address with balance := 0 } = State.EMPTY_ACCOUNT ↔
            { tx.getAccount address with balance := 0 } = State.EMPTY_ACCOUNT := by
          rw [hmid_orig]
        by_cases hp : fork ≥ .paris
        · by_cases he : { tx.getAccount address with balance := 0 } = State.EMPTY_ACCOUNT
          · have he_mid : { mid.getAccount address with balance := 0 } = State.EMPTY_ACCOUNT :=
              hsame_empty.mpr he
            have hw0 : mid.storageWrites.getD address ∅ = ∅ := by
              rw [hw, ite_eq_left_of_eq_true _ _ (eq_true ⟨hp, .inl ⟨rfl, he⟩⟩)]
            have hr0 : mid.storageReads[address]? =
                (tx.destroyStorage address).storageReads[address]? := by
              rw [hm, ite_eq_left_of_eq_true _ _ (eq_true ⟨hp, .inl ⟨rfl, he⟩⟩)]
            have hd : (mid.destroyStorage address).storageReads[address]? =
                (tx.destroyStorage address).storageReads[address]? := by
              simp [State.TransactionState.destroyStorage, hw0,
                Std.ExtTreeMap.keys_eq_nil_iff.mpr rfl, Std.ExtTreeSet.insertMany_nil,
                Std.ExtTreeMap.getD_eq_getD_getElem?, hr0]
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hp, he_mid⟩),
              ite_eq_left_of_eq_true _ _ (eq_true ⟨hp, .inl ⟨rfl, he⟩⟩), hd]
          · have he_mid : { mid.getAccount address with balance := 0 } ≠ State.EMPTY_ACCOUNT :=
              mt hsame_empty.mp he
            have he_tx' : tx'.getAccount address ≠ State.EMPTY_ACCOUNT := by
              rw [hread]
              exact he_mid
            have he_mid_acc : mid.getAccount address ≠ State.EMPTY_ACCOUNT := by
              intro hc
              apply he_mid
              rw [hc]
              rfl
            have hr0 : mid.storageReads[address]? = tx.storageReads[address]? := by
              rw [hm, ite_eq_right_of_eq_false _ _ (eq_false fun hc => ?_)]
              rcases hc.2 with ⟨-, h1⟩ | ⟨rfl, h2⟩
              · exact he h1
              · exact he_mid_acc h2
            rw [ite_eq_right_of_eq_false _ _ (eq_false fun hc => he_mid hc.2), hr0,
              ite_eq_right_of_eq_false _ _ (eq_false fun hc => ?_)]
            rcases hc.2 with ⟨-, h1⟩ | ⟨rfl, h2⟩
            · exact he h1
            · exact he_tx' h2
        · rw [hm]
          simp [hp]
      · rw [State.TransactionState.getElem?_storageReads_modifyState_of_ne ha h,
          State.TransactionState.getElem?_storageReads_moveEther hmove address, hsub]
        by_cases hab : address = beneficiary
        · subst hab
          rw [hother address ha]
        · simp [ha, hab]
    · cases h
      rw [State.TransactionState.getElem?_storageReads_moveEther hmove address, hsub]
  · obtain ⟨mid, hcreate, h⟩ := Base.bind_ok_iff.mp h
    rw [State.TransactionState.getElem?_storageReads_modifyState_modifyState hcreate h address]
    obtain ⟨_, hf, hread, hother⟩ := State.TransactionState.modifyState_eq_ok h
    cases hf
    by_cases hp : fork ≥ .paris
    · by_cases ha : address = originator
      · subst ha
        by_cases hab : address = beneficiary
        · subst hab
          obtain ⟨-, hn, hc⟩ := State.TransactionState.getAccount_createEther hcreate address
          have heq_zero : { mid.getAccount address with balance := 0 } =
              { tx.getAccount address with balance := 0 } := by
            cases hmid_acc : mid.getAccount address
            cases htx_acc : tx.getAccount address
            rw [hmid_acc, htx_acc] at hn hc
            dsimp only at hn hc
            subst hn hc
            rfl
          have htx'_zero : tx'.getAccount address =
              { tx.getAccount address with balance := 0 } :=
            hread.trans heq_zero
          have hiff : (mid.getAccount address = State.EMPTY_ACCOUNT ∨
              tx'.getAccount address = State.EMPTY_ACCOUNT) ↔
              ({ tx.getAccount address with balance := 0 } = State.EMPTY_ACCOUNT ∨
                tx'.getAccount address = State.EMPTY_ACCOUNT) := by
            rw [htx'_zero, or_self]
            refine ⟨fun h => h.elim (fun hm => ?_) id, Or.inr⟩
            rw [← heq_zero, hm]
            rfl
          by_cases he : { tx.getAccount address with balance := 0 } = State.EMPTY_ACCOUNT
          · have h1 : mid.getAccount address = State.EMPTY_ACCOUNT ∨
                tx'.getAccount address = State.EMPTY_ACCOUNT :=
              hiff.mpr (.inl he)
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hp, by simpa using h1⟩),
              ite_eq_left_of_eq_true _ _ (eq_true ⟨hp, .inl ⟨rfl, he⟩⟩)]
          · have hne_tx' : tx'.getAccount address ≠ State.EMPTY_ACCOUNT := by
              rw [htx'_zero]
              exact he
            have h1 : ¬(mid.getAccount address = State.EMPTY_ACCOUNT ∨
                tx'.getAccount address = State.EMPTY_ACCOUNT) := by
              rw [hiff]
              exact not_or.mpr ⟨he, hne_tx'⟩
            rw [ite_eq_right_of_eq_false _ _ (eq_false fun hc => h1 (by simpa using hc.2)),
              ite_eq_right_of_eq_false _ _ (eq_false fun hc =>
                (not_or.mpr ⟨he, hne_tx'⟩) (by simpa using hc.2))]
        · obtain ⟨_, _, _, hrest⟩ := State.TransactionState.modifyState_eq_ok hcreate
          have hne_ba : address ≠ beneficiary := hab
          rw [hread, hrest address hne_ba]
          simp [hp, hab]
      · by_cases hab : address = beneficiary
        · subst hab
          rw [hother address ha]
          simp [hp, ha]
        · simp [hp, ha, hab]
    · simp [hp]

/-- The transfer of SELFDESTRUCT keeps the account reads and storage reads in lockstep. -/
theorem reads_selfdestructTransfer {tx tx' : State.TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    tx'.accountReads = (tx.accountReads.insert originator).insert beneficiary ∧
      (∀ address, tx'.storageReads[address]? =
        if fork ≥ .paris ∧
            ((address = originator ∧
                { tx.getAccount originator with balance := 0 } = State.EMPTY_ACCOUNT) ∨
              (address = beneficiary ∧ tx'.getAccount beneficiary = State.EMPTY_ACCOUNT)) then
          (tx.destroyStorage address).storageReads[address]?
        else tx.storageReads[address]?) ∧
      (fork < .paris → tx'.storageReads = tx.storageReads) := by
  refine ⟨accountReads_selfdestructTransfer h,
    getElem?_storageReads_selfdestructTransfer h, fun hfork => ?_⟩
  have hnp : ¬fork ≥ .paris := Nat.not_le_of_lt hfork
  exact Std.ExtTreeMap.ext_getElem? fun address => by
    rw [getElem?_storageReads_selfdestructTransfer h address]
    simp [hnp]

omit [GasMeter Meter] in
/-- Completing SELFDESTRUCT adds the current account and the beneficiary to the account reads.

From Paris, an empty current account or beneficiary has its written keys read.

Every other address keeps its storage reads, and before Paris every address keeps them. -/
theorem reads_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.state.accountReads =
        (evm.state.accountReads.insert evm.message.currentTarget).insert beneficiary ∧
      (∀ address, after.state.storageReads[address]? =
        if fork ≥ .paris ∧
            ((address = evm.message.currentTarget ∧
                { evm.state.getAccount evm.message.currentTarget with balance := 0 } =
                  State.EMPTY_ACCOUNT) ∨
              (address = beneficiary ∧
                after.state.getAccount beneficiary = State.EMPTY_ACCOUNT)) then
          (evm.state.destroyStorage address).storageReads[address]?
        else evm.state.storageReads[address]?) ∧
      (fork < .paris → after.state.storageReads = evm.state.storageReads) := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨state, htr, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have htr' : selfdestructTransfer fork evm.state evm.message.currentTarget beneficiary =
        .ok state := by
      revert htr
      cases selfdestructTransfer fork evm.state evm.message.currentTarget beneficiary <;>
        simp [Except.mapError]
    exact reads_selfdestructTransfer htr'

omit [GasMeter Meter] in
/-- Completing SELFDESTRUCT adds the current account and the beneficiary to the account reads. -/
theorem accountReads_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.state.accountReads =
      (evm.state.accountReads.insert evm.message.currentTarget).insert beneficiary :=
  (reads_finishSelfdestruct h).1

/-- SELFDESTRUCT adds its beneficiary to the account reads, even when it then halts.

When it halts after reading the beneficiary, it keeps every storage read.

When it completes, it adds the current account and applies the transfer storage reads. -/
theorem reads_selfdestructStep {evm after : Evm fork Meter} {word : U256}
    {rest : List U256} (hs : evm.stack.val = word :: rest)
    (h : selfdestructStep fork evm = .ok after) :
    (after.state.accountReads = evm.state.accountReads.insert (Base.toAddressMasked word) ∧
        after.state.storageReads = evm.state.storageReads ∧
        ∃ e, after.error = some e) ∨
      (after.state.accountReads =
          (evm.state.accountReads.insert evm.message.currentTarget).insert
            (Base.toAddressMasked word) ∧
        (∀ address, after.state.storageReads[address]? =
          if fork ≥ .paris ∧
              ((address = evm.message.currentTarget ∧
                  { evm.state.getAccount evm.message.currentTarget with balance := 0 } =
                    State.EMPTY_ACCOUNT) ∨
                (address = Base.toAddressMasked word ∧
                  after.state.getAccount (Base.toAddressMasked word) = State.EMPTY_ACCOUNT)) then
            (evm.state.destroyStorage address).storageReads[address]?
          else evm.state.storageReads[address]?) ∧
        (fork < .paris → after.state.storageReads = evm.state.storageReads) ∧
        after.error = evm.error) := by
  unfold selfdestructStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨rfl, -⟩ := popWord_of_stack hs h1
  have err1 : e1.error = evm.error := by
    obtain ⟨⟨_, _⟩, -, h1'⟩ := Base.bind_ok_iff.mp h1
    cases h1'
    rfl
  have c1 := popWord_sameContext h1
  dsimp only at h
  rcases hacc : accessAddress e1 (Base.toAddressMasked word) with ⟨cold, e2⟩
  have c2 : e2.message = evm.message ∧ e2.state = evm.state ∧ e2.error = evm.error := by
    obtain ⟨_, ha⟩ := accessAddress_snd e1 (Base.toAddressMasked word)
    rw [hacc] at ha
    dsimp only at ha
    rw [ha]
    exact ⟨c1.message, c1.state, err1⟩
  simp only [hacc] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have err3 : e3.error = e2.error := by
      obtain ⟨_, -, h3'⟩ := Base.bind_ok_iff.mp h3
      cases h3'
      rfl
    have err4 : e4.error = e3.error := by
      obtain ⟨_, -, h4'⟩ := Base.bind_ok_iff.mp h4
      cases h4'
      rfl
    have c4 := (chargeGas_sameContext h3).trans (chargeStateGas_sameContext h4)
    obtain ⟨ha, hst, hpre⟩ := reads_finishSelfdestruct h
    have herr : after.error = evm.error := by
      unfold finishSelfdestruct at h
      split at h
      · cases h
      · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact err4.trans (err3.trans c2.2.2)
    right
    have he4_msg : e4.message = evm.message := by
      rw [c4.message]
      exact c2.1
    have he4_state : e4.state.getAccount = evm.state.getAccount := by
      funext addr
      rw [c4.state]
      simp [recordAccountRead, c2.2.1]
    have he4_sr : e4.state.storageReads = evm.state.storageReads := by
      rw [c4.state]
      simp [recordAccountRead, State.TransactionState.recordAccountRead, c2.2.1]
    have he4_ds : ∀ address, (e4.state.destroyStorage address).storageReads =
        (evm.state.destroyStorage address).storageReads := by
      intro address
      rw [c4.state]
      simp [recordAccountRead, State.TransactionState.recordAccountRead,
        State.TransactionState.destroyStorage, c2.2.1]
    refine ⟨?_, fun address => ?_, fun hfork => (hpre hfork).trans he4_sr, herr⟩
    · rw [ha, he4_msg, c4.state]
      show ((e2.state.accountReads.insert _).insert evm.message.currentTarget).insert _ = _
      rw [c2.2.1]
      ext a
      simp [Std.ExtTreeSet.mem_insert, or_left_comm]
    · rw [hst address, he4_msg, he4_state, he4_sr, he4_ds address]
  · left
    refine ⟨?_, ?_, e, rfl⟩
    · simp [id, state_exceptionalHalt, recordAccountRead, State.TransactionState.recordAccountRead,
        c2.2.1]
    · simp [id, state_exceptionalHalt, recordAccountRead, State.TransactionState.recordAccountRead,
        c2.2.1]

/-- SELFDESTRUCT adds its beneficiary to the account reads, even when it then halts.

When it completes, it also adds the current account. -/
theorem accountReads_selfdestructStep {evm after : Evm fork Meter} {word : U256}
    {rest : List U256} (hs : evm.stack.val = word :: rest)
    (h : selfdestructStep fork evm = .ok after) :
    (after.state.accountReads = evm.state.accountReads.insert (Base.toAddressMasked word) ∧
        ∃ e, after.error = some e) ∨
      after.state.accountReads =
        (evm.state.accountReads.insert evm.message.currentTarget).insert
          (Base.toAddressMasked word) := by
  rcases reads_selfdestructStep hs h with ⟨ha, -, he⟩ | ⟨ha, -⟩
  · exact .inl ⟨ha, he⟩
  · exact .inr ha


/-- Every other instruction of the dispatch keeps the account and storage reads.

The dispatch leaves out the calls and the creations.

Of its own instructions, the eight that read an account or a storage slot are left out. -/
theorem reads_instruction {op : Op} {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {evm after : Evm fork Meter} (hrun : instruction fork op = some run)
    (ordinary : op ∉ [.balance, .selfbalance, .extcodesize, .extcodecopy, .extcodehash,
      .sload, .sstore, .selfdestruct])
    (h : run evm = .ok after) :
    after.state.accountReads = evm.state.accountReads ∧
      after.state.storageReads = evm.state.storageReads := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · have hs := (stackOnlyStep_sameContext hf h).state
    exact ⟨by rw [hs], by rw [hs]⟩
  rcases orElse_eq_some hrun with hf | hrun
  · have hs := (controlFlowStep_sameContext hf h).state
    exact ⟨by rw [hs], by rw [hs]⟩
  rcases orElse_eq_some hrun with hf | hrun
  · have hs := (memoryDataStep_sameContext hf h).state
    exact ⟨by rw [hs], by rw [hs]⟩
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hf
    case «return» =>
      subst hf
      have hs := (returnStep_sameContext h).state
      exact ⟨by rw [hs], by rw [hs]⟩
    case revert =>
      split at hf
      · cases hf
        have hs := (revertStep_sameContext h).state
        exact ⟨by rw [hs], by rw [hs]⟩
      · cases hf
  rcases orElse_eq_some hrun with hf | hrun
  · have hs := (environmentStep_sameContext hf h).state
    exact ⟨by rw [hs], by rw [hs]⟩
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [accountStep, reduceCtorEq] at hf <;> exact absurd (by simp) ordinary
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf <;>
      exact absurd (by simp) ordinary
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · have hs := (tloadStep_sameContext h).state
      exact ⟨by rw [hs], by rw [hs]⟩
    · obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨⟨v, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · cases h
        have hs := (((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
          (chargeGas_sameContext h3)).state
        obtain ⟨ha, hst⟩ := State.TransactionState.reads_setTransientStorage e3.state
          e3.message.currentTarget (U256.toBeBytes w) v
        exact ⟨ha.trans (by rw [hs]), hst.trans (by rw [hs])⟩
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, -, -, hs, -⟩ := logStep_eq_ok h
    exact ⟨by rw [hs], by rw [hs]⟩
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    exact absurd (by simp) ordinary

end EthLib.Execution.Evm
