module

public import EthLib.Execution.Proofs.Evm.Call.StorageAt

/-!
# Proofs: an invariant of the storage of a contract holds over every message

Take an account that holds a given code, and an invariant of its storage.

If each call that runs that code there keeps the invariant, so does every message.

The message must start from the invariant, and run that code when it goes to the account.

The proof assumes that no other code has the Keccak-256 hash of the given code.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State (Account EMPTY_ACCOUNT EMPTY_CODE_HASH StateError TransactionState)
open EthLib.Execution.State.TransactionState
open Cryptography.Hash.Keccak (keccak256)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The code of the account -/

/-- The account at `address` holds `code`.

Its code hash is the hash of `code`, and the state keeps `code` under that hash. -/
def HoldsCode (address : Address) (code : ByteArray) (tx : TransactionState) : Prop :=
  (tx.getAccount address).codeHash = keccak256 code ∧ tx.getCode (keccak256 code) = .ok code

/-- What the proofs ask of the code of the contract.

Its hash is not that of the empty code, and it names no delegate.

No other code has its hash: an assumption on Keccak-256, which SOUNDNESS.md lists. -/
structure CodeHyp (code : ByteArray) : Prop where
  /-- The hash of the code is not the hash of the empty code. -/
  hash_ne : keccak256 code ≠ EMPTY_CODE_HASH
  /-- The code is no delegation indicator. -/
  noDelegate : delegatedAddress code = none
  /-- No other code has the hash of the code.

  It is not provable for any code, and is believed false for Keccak-256 as a function.

  Until a random-oracle bound replaces it, the theorems that use it say nothing if it is false. -/
  hashOnly : ∀ other, keccak256 other = keccak256 code → other = code

/-- The code names no delegate at any fork. -/
theorem CodeHyp.noDelegateAt {code : ByteArray} (hyp : CodeHyp code) :
    (if fork ≥ .pectra then delegatedAddress code else none) = none := by
  split
  · exact hyp.noDelegate
  · rfl

/-- The code is not empty. -/
theorem CodeHyp.size_ne {code : ByteArray} (hyp : CodeHyp code) : code.size ≠ 0 := by
  intro h
  apply hyp.hash_ne
  have : code = .empty := by
    cases code with
    | mk data =>
      simp only [ByteArray.size] at h
      rw [Array.size_eq_zero_iff] at h
      subst h
      rfl
  rw [this]
  rfl

/-- The code is no delegation indicator. -/
theorem CodeHyp.not_valid {code : ByteArray} (hyp : CodeHyp code) :
    isValidDelegation code = false := by
  have h := hyp.noDelegate
  unfold delegatedAddress at h
  split at h
  · cases h
  · simpa using ‹¬isValidDelegation code = true›

/-- A change keeps the code of `address` and its storage, when the account holds `code`. -/
def KeepsAt (address : Address) (code : ByteArray) (tx tx' : TransactionState) : Prop :=
  HoldsCode address code tx →
    HoldsCode address code tx' ∧ tx'.getStorage address = tx.getStorage address

namespace KeepsAt

variable {address : Address} {code : ByteArray} {tx tx' tx'' : TransactionState}

/-- A state keeps itself. -/
theorem refl (tx : TransactionState) : KeepsAt address code tx tx :=
  fun h => ⟨h, rfl⟩

/-- Two changes that keep the account keep it together. -/
theorem trans (h : KeepsAt address code tx tx') (h' : KeepsAt address code tx' tx'') :
    KeepsAt address code tx tx'' := fun hold =>
  let ⟨hold', hs⟩ := h hold
  let ⟨hold'', hs'⟩ := h' hold'
  ⟨hold'', hs'.trans hs⟩

/-- A state with the same account, codes and storage at `address` keeps it. -/
theorem of_eq (hacc : tx'.getAccount address = tx.getAccount address)
    (hcode : ∀ codeHash, tx'.getCode codeHash = tx.getCode codeHash)
    (hstorage : tx'.getStorage address = tx.getStorage address) : KeepsAt address code tx tx' :=
  fun ⟨h1, h2⟩ => ⟨⟨hacc ▸ h1, (hcode _).trans h2⟩, hstorage⟩

end KeepsAt

variable {address : Address} {code : ByteArray} {tx tx' : TransactionState}

/-- A change of an account that keeps its code hash keeps the account that holds `code`.

It may delete an account only when it leaves it empty, and an account with code is never empty. -/
theorem keepsAt_modifyState (hyp : CodeHyp code) {other : Address}
    {f : Account → Except StateError Account}
    (hf : ∀ account account', f account = .ok account' → account'.codeHash = account.codeHash)
    (h : tx.modifyState fork other f = .ok tx') : KeepsAt address code tx tx' := by
  intro ⟨hhash, hcode⟩
  obtain ⟨account, hacc, hself, hother⟩ := modifyState_eq_ok h
  have hhash' : (tx'.getAccount address).codeHash = keccak256 code := by
    by_cases ho : address = other
    · subst ho
      rw [hself, hf _ _ hacc, hhash]
    · rw [hother address ho, hhash]
  refine ⟨⟨hhash', by rw [getCode_modifyState h]; exact hcode⟩, funext fun key => ?_⟩
  rw [getStorage_modifyState h]
  -- The account at `address` stays, since it holds code.
  rw [ite_eq_right]
  rintro ⟨rfl, hnone⟩
  have : (tx'.getAccount address).codeHash = EMPTY_CODE_HASH := by
    simp [getAccount, hnone, EMPTY_ACCOUNT]
  exact hyp.hash_ne (hhash'.symm.trans this)

/-- A move of ether keeps the account that holds `code`. -/
theorem keepsAt_moveEther (hyp : CodeHyp code) {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') : KeepsAt address code tx tx' := by
  unfold moveEther at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  refine (keepsAt_modifyState hyp (fun _ _ hd => ?_) h1).trans
    (keepsAt_modifyState hyp (fun _ _ hc => ?_) h2)
  · unfold Account.debit at hd
    split at hd
    · cases hd
    · cases hd
      rfl
  · unfold Account.credit at hc
    split at hc
    · cases hc
      rfl
    · cases hc

/-- New ether keeps the account that holds `code`. -/
theorem keepsAt_createEther (hyp : CodeHyp code) {other : Address} {amount : U256}
    (h : tx.createEther fork other amount = .ok tx') : KeepsAt address code tx tx' := by
  refine keepsAt_modifyState hyp (fun _ _ hc => ?_) h
  unfold Account.credit at hc
  split at hc
  · cases hc
    rfl
  · cases hc

/-- A new balance keeps the account that holds `code`. -/
theorem keepsAt_setAccountBalance (hyp : CodeHyp code) {other : Address} {amount : U256}
    (h : tx.setAccountBalance fork other amount = .ok tx') : KeepsAt address code tx tx' :=
  keepsAt_modifyState hyp (fun _ _ hc => by cases hc; rfl) h

/-- A rise of a nonce keeps the account that holds `code`. -/
theorem keepsAt_incrementNonce (hyp : CodeHyp code) {other : Address}
    (h : tx.incrementNonce fork other = .ok tx') : KeepsAt address code tx tx' :=
  keepsAt_modifyState hyp (fun _ _ hc => by cases hc; rfl) h

/-- A write of storage at another address keeps the account that holds `code`. -/
theorem keepsAt_setStorage {other : Address} {key : Bytes32} {value : U256}
    (h : tx.setStorage other key value = .ok tx') (hne : address ≠ other) :
    KeepsAt address code tx tx' :=
  .of_eq (by simp only [getAccount, getAccountOptional_setStorage h]) (getCode_setStorage h)
    (funext fun _ => getStorage_setStorage_of_ne h (.inl hne))

/-- New code at another address keeps the account that holds `code`.

A code with the hash of `code` is `code`, by the hypothesis on its hash. -/
theorem keepsAt_setCode (hyp : CodeHyp code) {other : Address} {code' : ByteArray}
    (h : tx.setCode fork other code' = .ok tx') (hne : address ≠ other) :
    KeepsAt address code tx tx' := by
  intro ⟨hhash, hcode⟩
  obtain ⟨-, hother⟩ := getAccount_setCode h
  refine ⟨⟨by simp only [getAccount, hother address hne]; exact hhash, ?_⟩, ?_⟩
  · by_cases hk : keccak256 code = keccak256 code'
    · rw [hyp.hashOnly code' hk.symm] at h
      exact getCode_setCode_self h hyp.hash_ne
    · rw [getCode_setCode_of_ne h hk]
      exact hcode
  · -- The new code changes only the account at `other`, so it keeps the storage at `address`.
    funext key
    dsimp only [setCode] at h
    split at h
    · rw [getStorage_modifyState h, ite_eq_right fun hc => hne hc.1]
    · rw [getStorage_modifyState h, ite_eq_right fun hc => hne hc.1]
      rfl

/-- A successful move of the balance of a destroyed account keeps the account that holds `code`. -/
theorem keepsAt_selfdestructTransfer (hyp : CodeHyp code) {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    KeepsAt address code tx tx' := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (keepsAt_moveEther hyp h1).trans (keepsAt_setAccountBalance hyp h)
    · cases h
      exact keepsAt_moveEther hyp h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (keepsAt_createEther hyp h1).trans (keepsAt_setAccountBalance hyp h)

omit [GasMeter Meter] in
/-- A state that only adds reads keeps the account that holds `code`. -/
theorem keepsAt_staticStep {a b : Evm fork Meter} (h : StaticStep a b) :
    KeepsAt address code a.state b.state :=
  .of_eq (getAccount_of_staticStep h address)
    (fun codeHash => by rw [h.tracker.rest]; rfl)
    (funext fun key => (h.state address List.not_mem_nil).2.1 key)

/-- An account that holds code is never the address of a new contract. -/
theorem HoldsCode.not_deployable (hyp : CodeHyp code) (h : HoldsCode address code tx) :
    tx.accountDeployable address = false := by
  unfold accountDeployable
  have : (tx.getAccount address).codeHash ≠ EMPTY_CODE_HASH := by rw [h.1]; exact hyp.hash_ne
  simp [this]

/-- An account that holds code is not empty. -/
theorem HoldsCode.not_empty (hyp : CodeHyp code) {tx : TransactionState}
    (h : HoldsCode address code tx) : tx.accountExistsAndIsEmpty address = false := by
  cases he : tx.accountExistsAndIsEmpty address
  · rfl
  · have hsome := (accountExistsAndIsEmpty_iff_eq_some tx address).mp he
    have : (tx.getAccount address).codeHash = EMPTY_CODE_HASH := by
      simp [getAccount, hsome, EMPTY_ACCOUNT]
    exact absurd (h.1.symm.trans this) hyp.hash_ne

/-- The preparation of a creation at another address keeps the account that holds `code`. -/
theorem keepsAt_prepareCreation (hyp : CodeHyp code) {target : Address}
    (h : prepareCreation fork tx target = .ok tx') (hne : address ≠ target) :
    KeepsAt address code tx tx' := by
  have wipe : KeepsAt address code tx ((tx.destroyStorage target).markAccountCreated target) :=
    .of_eq rfl
      (fun _ => rfl) (funext fun key => getStorage_destroyStorage_of_ne tx hne key)
  unfold prepareCreation at h
  split at h
  · exact wipe.trans (keepsAt_incrementNonce hyp (Base.mapError_ok_iff.mp h))
  · cases h
    exact wipe

/-- The state that a message enters keeps the account that holds `code`. -/
theorem keepsAt_entered (hyp : CodeHyp code) {message : Message fork}
    {state entry : TransactionState} {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    KeepsAt address code state entry := by
  -- A touch gives an account only to an address with none, and the account at `address` exists.
  have start : KeepsAt address code state (startState fork message state) := by
    intro hold
    unfold startState
    split
    · unfold touchAccount
      split
      · exact ⟨hold, rfl⟩
      · rename_i hnot
        refine ⟨⟨?_, hold.2⟩, rfl⟩
        by_cases ho : address = message.currentTarget
        · exfalso
          apply hnot
          rw [← ho]
          have hne : (state.getAccount address).codeHash ≠ EMPTY_CODE_HASH := by
            rw [hold.1]; exact hyp.hash_ne
          unfold accountExists
          cases hacc : state.getAccountOptional address
          · simp [getAccount, hacc, EMPTY_ACCOUNT] at hne
          · simp
        · simp only [getAccount, getAccountOptional_setAccount_of_ne _ _ ho]
          exact hold.1
    · exact ⟨hold, rfl⟩
  rcases h with ⟨-, rfl, -⟩ | ⟨-, moved, -⟩
  · exact start
  · exact start.trans (keepsAt_moveEther hyp moved)

/-- A rollback to a snapshot of the same block gives back the account and the storage. -/
theorem keepsAt_restoreTxState {tx snapshot : TransactionState}
    (hparent : tx.parent = snapshot.parent) :
    KeepsAt address code snapshot (tx.restoreTxState snapshot) :=
  .of_eq (by simp only [getAccount, getAccountOptional_restoreTxState hparent])
    (getCode_restoreTxState hparent) (funext (getStorage_restoreTxState hparent address))

/-! ## The steps of frames at other accounts -/

/-- Each step of a frame at another account keeps the account that holds `code`. -/
theorem stepRules_keepsAt (hyp : CodeHyp code) :
    StepRules fork (fun a b : Evm fork Meter => b.message = a.message ∧
      (a.message.currentTarget ≠ address → KeepsAt address code a.state b.state)) where
  trans hab hbc := ⟨hbc.1.trans hab.1, fun hne =>
    (hab.2 hne).trans (hbc.2 (by rw [hab.1]; exact hne))⟩
  static h := ⟨h.message, fun _ => keepsAt_staticStep h⟩
  -- SSTORE writes the storage of the account of the frame, which is another one.
  sstore _ _ _ _ _ h := ⟨rfl, fun hne => keepsAt_setStorage h (Ne.symm hne)⟩
  tstore _ _ _ _ := ⟨rfl, fun _ => .of_eq rfl (fun _ => rfl) rfl⟩
  log _ hs _ hm _ := ⟨hm, fun _ => by rw [hs]; exact .refl _⟩
  selfdestruct _ _ h := ⟨message_finishSelfdestruct h, fun _ => by
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact keepsAt_selfdestructTransfer hyp (Base.mapError_ok_iff.mp hst)⟩
  incrementNonce _ _ _ _ h := ⟨rfl, fun _ => keepsAt_incrementNonce hyp h⟩
  incorporate h := ⟨message_incorporateChild _ _, fun hne => by
    rw [state_incorporateChild]
    exact h.2 hne⟩

/-- A run of a frame keeps its message, whatever the messages it sends do. -/
theorem message_runFrame [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound} {evm after : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    after.message = evm.message := by
  let T := stepRules_messageCode (fork := fork) (Meter := Meter)
  have r : after.message = evm.message ∧ after.code = evm.code := by
    refine rel_runFrame (Inv := fun _ => True) (C := fun _ _ _ => True)
      (R := fun a b : Evm fork Meter => b.message = a.message ∧ b.code = a.code) T.refl T.trans
      (fun _ _ => trivial) (fun evm error _ => T.static (staticStep_exceptionalHalt evm error))
      (fun {evm result} _ _ hstep => ?_) (fun _ _ _ _ _ _ => trivial) trivial h
    have k := T.step hstep
    cases result with
    | next after => exact k
    | child caller message resume =>
      refine ⟨k.1, fun child after hres _ => ?_⟩
      have same := sameContext_of_step_eq_child hstep hres
      exact ⟨by rw [same.message, message_incorporateChild, k.1.1],
        by rw [same.code, code_incorporateChild, k.1.2]⟩
  exact r.1

/-! ## Frames and messages -/

variable (address code)

/-- The storage of `address` meets `Inv`, and the account at `address` holds `code`. -/
def GoodAt (Inv : (Bytes32 → U256) → Prop) (tx : TransactionState) : Prop :=
  HoldsCode address code tx ∧ Inv (tx.getStorage address)

/-- A message at `address` is a call that runs `code`. -/
def RunsCode (message : Message fork) : Prop :=
  message.currentTarget = address → message.code = code ∧ message.target ≠ none

/-- Each call that runs `code` at `address` keeps `Inv` of its storage, and the code.

Its frame starts as a call starts it, from a state where the account holds `code`.

It keeps them when it ends with no error, and when its message runs no precompile.

Its runner keeps them over each message that may run at `address`, from a state with them.

A frame that sends DELEGATECALL or CALLCODE to other code gets nothing from its runner. -/
def FramesKeepCode (fork : Fork) (Meter : Type) [GasMeter Meter] [LawfulGasMeter Meter]
    (Inv : (Bytes32 → U256) → Prop) : Prop :=
  ∀ {bound : Nat} {runChild : MessageRunner fork Meter bound},
    RunnerEnsures (fun caller message child => GoodAt address code Inv caller.state →
      RunsCode address code message → GoodAt address code Inv child.state) runChild →
    -- The frame is the start frame of a call to `address` that runs `code`.
    ∀ {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
      {after : Evm fork Meter} {within : GasMeter.gasHeld meter ≤ bound},
      message.currentTarget = address → message.code = code → message.target ≠ none →
      precompileAddress fork message = none → GoodAt address code Inv state →
      runFrame (step fork) (step_decreases fork) bound runChild
        (startFrame message state substate meter) within = .ok after →
      after.error = none → GoodAt address code Inv after.state

/-- What a call keeps: its message, the block, and the invariant when it may run there. -/
def CallGood (Inv : (Bytes32 → U256) → Prop) (message : Message fork)
    (state : TransactionState) (_substate : Substate) (_meter : Meter)
    (ended : Evm fork Meter) : Prop :=
  ended.message = message ∧ ended.state.parent = state.parent ∧
    (GoodAt address code Inv state → RunsCode address code message →
      GoodAt address code Inv ended.state)

/-- What a creation keeps: the block, and the invariant when it goes to another address. -/
def CreateGood (Inv : (Bytes32 → U256) → Prop) (message : Message fork)
    (state : TransactionState) (_substate : Substate) (_meter : Meter)
    (ended : Evm fork Meter) : Prop :=
  ended.state.parent = state.parent ∧
    (GoodAt address code Inv state → message.currentTarget ≠ address →
      GoodAt address code Inv ended.state)

variable {address code}

/-- A change that keeps the account keeps the invariant. -/
theorem GoodAt.of_keepsAt {Inv : (Bytes32 → U256) → Prop} {tx tx' : TransactionState}
    (h : GoodAt address code Inv tx) (k : KeepsAt address code tx tx') :
    GoodAt address code Inv tx' :=
  let ⟨hold, hs⟩ := k h.1
  ⟨hold, hs ▸ h.2⟩

variable [LawfulGasMeter Meter] {Inv : (Bytes32 → U256) → Prop}

/-- A run of a frame at another account keeps the invariant and the code of `address`.

Its runner must keep them over each message that it runs. -/
theorem goodAt_runFrame (hyp : CodeHyp code) {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    (runs : RunnerEnsures (ChildRelByKind (CallGood address code Inv)
      (CreateGood address code Inv)) runChild)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hne : evm.message.currentTarget ≠ address) (good : GoodAt address code Inv evm.state)
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    GoodAt address code Inv after.state := by
  let T := stepRules_keepsAt (fork := fork) (Meter := Meter) (address := address) hyp
  -- A frame at another account with the invariant keeps it.
  let Q : Evm fork Meter → Prop := fun e =>
    e.message.currentTarget ≠ address ∧ GoodAt address code Inv e.state
  let R : Evm fork Meter → Evm fork Meter → Prop := fun a b =>
    b.message = a.message ∧ (Q a → GoodAt address code Inv b.state)
  have conv : ∀ {a b : Evm fork Meter}, (b.message = a.message ∧
      (a.message.currentTarget ≠ address → KeepsAt address code a.state b.state)) → R a b :=
    fun h => ⟨h.1, fun q => q.2.of_keepsAt (h.2 q.1)⟩
  have r : R evm after := by
    refine rel_runFrame (Inv := Q)
      (C := ChildRelByKind (CallGood address code Inv) (CreateGood address code Inv))
      (fun e => ⟨rfl, fun q => q.2⟩)
      (fun {a b c} hab hbc => ⟨hbc.1.trans hab.1, fun q =>
        hbc.2 ⟨by rw [hab.1]; exact q.1, hab.2 q⟩⟩)
      (fun {a b} q hab => ⟨by rw [hab.1]; exact q.1, hab.2 q⟩)
      (fun evm error _ => conv (T.static (staticStep_exceptionalHalt evm error)))
      (fun {evm result} q _ hstep => ?_) (fun caller message lt ended _ hran =>
        runs caller message lt ended hran) ⟨hne, good⟩ h
    have k := T.step hstep
    cases result with
    | next after => exact conv k
    | child caller message resume =>
      have kc := conv k.1
      refine ⟨kc, fun child after hres hc => ?_⟩
      have same := sameContext_of_step_eq_child hstep hres
      have hstate : after.state = child.state := by rw [same.state, state_incorporateChild]
      refine ⟨by rw [same.message, message_incorporateChild, kc.1], fun q' => ?_⟩
      rw [hstate]
      have gcaller := kc.2 q
      unfold ChildRelByKind at hc
      split at hc
      · -- A call to `address` from another account runs the code that the account holds.
        rename_i target htarget
        refine (hc.2.2 gcaller fun hat => ⟨?_, by simp [htarget]⟩)
        refine step_eq_child_callsCode hstep (by simp [htarget]) (by rw [hat]; exact Ne.symm q.1)
          code ?_ hyp.noDelegateAt
        rw [hat, q.2.1.1]
        exact q.2.1.2
      · -- A creation never goes to `address`, which holds code.
        rename_i htarget
        refine hc.2 gcaller fun hat => ?_
        have hd := step_eq_child_deployable hstep htarget
        rw [hat, q.2.1.not_deployable hyp] at hd
        cases hd
  exact r.2 ⟨hne, good⟩

/-- Every call and creation that returns a frame keeps the invariant and the code of `address`.

Each frame that runs `code` at `address` must keep them.

A call must start where the account holds `code`, and run it if it goes there.

A creation must go to another address. -/
theorem goodAt_processMessage_induction (hyp : CodeHyp code)
    (frames : FramesKeepCode address code fork Meter Inv) (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        CallGood address code Inv message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CreateGood address code Inv message state substate meter ended.val) := by
  -- A frame keeps its message and the block, and the invariant when it ends with no error.
  --
  -- Only start frames of messages need the invariant, since a call starts its frame there.
  let F : Evm fork Meter → Evm fork Meter → Prop := fun evm after =>
    after.message = evm.message ∧ after.state.parent = evm.state.parent ∧
      ∀ (message : Message fork) (entry : TransactionState) (substate : Substate) (meter : Meter),
        evm = startFrame message entry substate meter →
        GoodAt address code Inv entry → RunsCode address code message →
        after.error = none → GoodAt address code Inv after.state
  have kept : ∀ {a b : Evm fork Meter}, StaticStep a b → F a b := fun h =>
    ⟨h.message, h.parent, fun _ _ _ _ he good _ _ =>
      (he ▸ good : GoodAt address code Inv _).of_keepsAt (keepsAt_staticStep h)⟩
  refine processMessage_frame_byKind (F := F) (Mcall := CallGood address code Inv)
    (Mcreate := CreateGood address code Inv)
    (fun {bound runChild evm after within} runs hpre h => ?_)
    (fun _ _ _ => kept (.of_sameContext ⟨rfl, rfl, rfl, rfl⟩))
    (fun _ _ h => kept (staticStep_runPrecompile h))
    (fun {message state entry substate entrySubstate meter ended} hentry hrun => ?_)
    (fun {message state prepared substate meter evm after} hp hm hd => ?_) n
  · -- Each message keeps the block, and the invariant when it may.
    have parents : KeepsParent runChild := by
      intro caller message lt ended hran
      have hc := runs caller message lt ended hran
      unfold ChildRelByKind ChildRel at hc
      split at hc
      · exact hc.2.1
      · exact hc.1
    have goods : RunnerEnsures (fun caller message child => GoodAt address code Inv caller.state →
        RunsCode address code message → GoodAt address code Inv child.state) runChild := by
      intro caller message lt ended hran good hruns
      have hc := runs caller message lt ended hran
      unfold ChildRelByKind ChildRel at hc
      split at hc
      · exact hc.2.2 good hruns
      · rename_i htarget
        exact hc.2 good fun hat => (hruns hat).2 htarget
    refine ⟨message_runFrame h, parent_runFrame parents h,
      fun message entry substate meter he good hruns herr => ?_⟩
    subst he
    by_cases hat : message.currentTarget = address
    · exact frames goods hat (hruns hat).1 (hruns hat).2 hpre good h herr
    · exact goodAt_runFrame hyp runs hat good h
  · -- A call ends in its frame, or in the state it is sent from after a failure.
    have hparent : ended.state.parent = state.parent := hrun.2.1.trans (parent_entered hentry)
    refine ⟨(message_rollbackOnError state ended).trans hrun.1,
      (parent_rollbackOnError state ended).trans hparent, fun good hruns => ?_⟩
    unfold rollbackOnError
    split
    · exact good.of_keepsAt (keepsAt_restoreTxState hparent)
    · rename_i hok
      exact hrun.2.2 message entry entrySubstate meter rfl
        (good.of_keepsAt (keepsAt_entered hyp hentry)) hruns (Option.not_isSome_iff_eq_none.mp hok)
  · -- A creation at another address prepares it, runs its init code, then deposits the code.
    have hparent : evm.state.parent = state.parent := hm.2.1.trans (parent_prepareCreation hp)
    refine ⟨(parent_depositCode hd).trans hparent, fun good hne => ?_⟩
    have hgood : GoodAt address code Inv evm.state :=
      hm.2.2 (good.of_keepsAt (keepsAt_prepareCreation hyp hp (Ne.symm hne)))
        fun hat => absurd hat hne
    rcases (depositCode_cases hd).2.2 with hs | hs | hs
    · rw [hs]
      exact good.of_keepsAt (keepsAt_restoreTxState hparent)
    · rw [hs]
      exact hgood
    · rw [hm.1] at hs
      exact hgood.of_keepsAt (keepsAt_setCode hyp hs (Ne.symm hne))

/-- A call that returns a frame keeps the invariant and the code of `address`.

Each frame that runs `code` at `address` must keep them.

The call must start where the account holds `code`, and run it if it goes there. -/
theorem goodAt_processMessage (hyp : CodeHyp code)
    (frames : FramesKeepCode address code fork Meter Inv) {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (good : GoodAt address code Inv state) (runs : RunsCode address code message) :
    GoodAt address code Inv ended.val.state :=
  ((goodAt_processMessage_induction hyp frames message.gas).1 message state substate meter held
    rfl ended h).2.2 good runs

/-- A creation elsewhere that returns a frame keeps the invariant and the code of `address`.

Each frame that runs `code` at `address` must keep them.

It holds at every fork, whether or not the frame of the creation halts with an error. -/
theorem goodAt_processCreateMessage (hyp : CodeHyp code)
    (frames : FramesKeepCode address code fork Meter Inv) {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (good : GoodAt address code Inv state) (hne : message.currentTarget ≠ address) :
    GoodAt address code Inv ended.val.state :=
  ((goodAt_processMessage_induction hyp frames message.gas).2 message state substate meter held
    rfl ended h).2 good hne

end EthLib.Execution.Evm
