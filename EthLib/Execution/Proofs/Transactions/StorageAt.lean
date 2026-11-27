module

public import EthLib.Execution.Proofs.Evm.Call.StorageAt
public import EthLib.Execution.Proofs.Evm.Call.StorageAway
public import EthLib.Execution.Proofs.Transactions.Deletion
public import EthLib.Execution.Proofs.Transactions.NoninterferenceRun

/-!
# Proofs: a transaction keeps the storage of an account it does not read

Outside its message, each step of a transaction keeps or wipes the storage of every address.

Its message keeps or wipes the storage of an account, unless it reads the account.

It also keeps or wipes it when no frame of the message runs at the account.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State.TransactionState

variable {fork : Fork} {Meter : Type} [GasMeter Meter] {address : Address}

/-! ## The steps outside the message -/

/-- An authorization keeps or wipes every storage: it only sets a code and raises a nonce. -/
theorem keptOrWiped_applyAuthorization {chainId : Nat} {done done' : Delegations Meter}
    {auth : Authorization} (h : applyAuthorization fork chainId done auth = .ok done') :
    KeptOrWiped address done.state done'.state := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact .refl _ _
  · exact .of_eq fun _ => rfl
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    obtain ⟨coded, hcode, hdelegate⟩ := bind_ok_iff.mp hdelegate
    obtain ⟨bumped, hnonce, hdelegate⟩ := bind_ok_iff.mp hdelegate
    cases hdelegate
    exact (KeptOrWiped.of_eq fun _ => rfl).trans
      ((keptOrWiped_setCode hcode).trans (keptOrWiped_incrementNonce hnonce))

/-- Authorizations that succeed keep or wipe every storage. -/
theorem keptOrWiped_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      KeptOrWiped address start.state done.state
  | [], _, _, h => by
    cases h
    exact .refl _ _
  | _ :: _, _, _, h => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    exact (keptOrWiped_applyAuthorization hnext).trans (keptOrWiped_foldlM_applyAuthorization h)

/-- The first frame of a message keeps or wipes every storage of the state before it.

Only its authorizations write; the rest records reads. -/
theorem keptOrWiped_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    KeptOrWiped address state first.state := by
  have read : ∀ (s : State.TransactionState) (other : Address),
      KeptOrWiped address s (s.recordAccountRead other) := fun _ _ => .of_eq fun _ => rfl
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact read _ _
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact read _ _
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target _
    dsimp only at h
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    have hauth : KeptOrWiped address state done.state := keptOrWiped_foldlM_applyAuthorization hdone
    -- After the authorizations, the first frame only records reads.
    generalize hread : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = read0 at h
    have base : KeptOrWiped address state read0 := by
      subst hread
      split
      · exact hauth.trans (read _ _)
      · exact hauth
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact base.trans (read _ _)
      · dsimp only at h
        split at h <;>
        · obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact (base.trans (read _ _)).trans (read _ _)

/-- The purchase of gas keeps or wipes every storage: it raises a nonce and takes a fee. -/
theorem keptOrWiped_buyGas {env : BlockEnvironment fork} {state bought : State.TransactionState}
    {sender : Address} {tx : Transaction} {lifted : LiftedRules}
    (h : buyGas env state sender tx lifted = .ok bought) :
    KeptOrWiped address state bought := by
  unfold buyGas at h
  obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp h
  exact (keptOrWiped_incrementNonce h1).trans (keptOrWiped_modifyState h2)

/-- The settlement of gas keeps or wipes every storage: it credits the sender and the beneficiary.

Before Paris, it may delete an empty beneficiary. -/
theorem keptOrWiped_settleGas {env : BlockEnvironment fork} {state settled : State.TransactionState}
    {sender : Address} {tx : Transaction} {gasLeft refundCounter gasUsed : Nat}
    {lifted : LiftedRules}
    (h : settleGas env state sender tx gasLeft refundCounter lifted = .ok (settled, gasUsed)) :
    KeptOrWiped address state settled := by
  have credit : ∀ {s s' : State.TransactionState} {other : Address} {amount : Nat},
      creditEther fork s other amount = .ok s' → KeptOrWiped address s s' := by
    intro s s' other amount hc
    unfold creditEther at hc
    split at hc
    · exact keptOrWiped_createEther hc
    · cases hc
  unfold settleGas at h
  obtain ⟨mid, h1, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, h2, h⟩ := bind_ok_iff.mp h
  cases h
  refine (credit h1).trans ?_
  unfold payBeneficiary at h2
  split at h2
  · cases h2
    split
    · exact keptOrWiped_destroyAccount _
    · exact .refl _ _
  · exact credit h2

/-- The deletions at the end of a transaction keep or wipe every storage. -/
theorem keptOrWiped_deleteAccounts {state state' : State.TransactionState} {output : CallOutput}
    (h : deleteAccounts fork state output = .ok state') : KeptOrWiped address state state' := by
  have fold : ∀ (l : List Address) (init final : State.TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      KeptOrWiped address init final := by
    intro l
    induction l with
    | nil =>
      intro init final h
      cases h
      exact .refl _ _
    | cons other rest ih =>
      intro init final h
      obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
      refine KeptOrWiped.trans ?_ (ih mid final h)
      split at hmid
      · exact keptOrWiped_clearAccountPreservingBalance hmid
      · cases hmid
        exact keptOrWiped_destroyAccount _
  unfold deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  exact (fold _ _ _ hdeleted).trans (keptOrWiped_destroyTouchedEmptyAccounts _)

/-- The settlement of gas keeps every read. -/
theorem readsLe_settleGas {env : BlockEnvironment fork} {state settled : State.TransactionState}
    {sender : Address} {tx : Transaction} {gasLeft refundCounter gasUsed : Nat}
    {lifted : LiftedRules}
    (h : settleGas env state sender tx gasLeft refundCounter lifted = .ok (settled, gasUsed)) :
    state.ReadsLe settled := by
  unfold settleGas at h
  obtain ⟨mid, h1, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, h2, h⟩ := bind_ok_iff.mp h
  cases h
  refine (readsLe_creditEther h1).trans ?_
  unfold payBeneficiary at h2
  split at h2
  · cases h2
    split
    · exact readsLe_destroyAccount _ _
    · exact .refl _
  · exact readsLe_creditEther h2

/-! ## The message and the transaction -/

variable [LawfulGasMeter Meter]

/-- The message of a transaction keeps or wipes the storage of `address`, unless it reads it.

A call must run at its recipient, as the message of a transaction and a system call do. -/
theorem keptOrRead_processMessageCall {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (recipient : ∀ target, message.target = some target → target = message.currentTarget)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    KeptOrRead address state output.state := by
  have ofFrame : ∀ (evm : Evm fork Meter) (refund : Nat) (touched : Std.ExtTreeSet Address),
      (CallOutput.ofFrame evm refund touched).state = evm.state := by
    intro evm refund touched
    unfold CallOutput.ofFrame
    split <;> rfl
  rw [processMessageCall_unfold] at h
  split at h
  · -- A halt before the first frame keeps the state, up to its reads.
    split at h
    · cases h
    · cases h
      exact .inl (.of_eq fun _ => rfl)
  · rename_i first hfirst
    have hstart : KeptOrWiped address state first.state :=
      keptOrWiped_prepareFirstFrame hfirst
    -- The first frame runs at the recipient, which its preparation reads.
    have hread : first.message.currentTarget = address → address ∈ first.state.accountReads :=
      fun hat => by
        rw [← hat, (substate_prepareFirstFrame hfirst).2.2.2]
        exact currentRead_prepareFirstFrame recipient hfirst
    split at h
    · obtain ⟨⟨evm, _⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [ofFrame]
      exact .of_keptOrWiped hstart (keptOrRead_processCreateMessage hrun hread)
    · obtain ⟨⟨evm, _⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [ofFrame]
      exact .of_keptOrWiped hstart (keptOrRead_processMessage hrun hread)

/-- A transaction keeps or wipes the storage of `address`, unless it reads the account.

Every frame at `address` runs from a state that has read the account.

It runs with the gas meter `Meter`. -/
theorem keptOrRead_runTransaction {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {tx : Transaction} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok out) :
    KeptOrRead address (.ofBlock block) out.state := by
  obtain ⟨target, bought, message, output, settled, htarget, hbought, hmessage, houtput, -,
    hsettle, hdelete⟩ := runTransaction_eq_ok h
  have hlast := (readsLe_settleGas hsettle).trans (readsLe_deleteAccounts hdelete)
  -- The message of a transaction runs at its recipient.
  have recipient : ∀ to, ({ message with
      reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } : Message fork).target =
        some to → to = ({ message with
          reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } :
            Message fork).currentTarget := by
    intro to hto
    obtain ⟨hmt, hmc⟩ := target_transactionMessage hmessage
    dsimp only at hto ⊢
    rw [hmc]
    rw [hmt] at hto
    unfold messageTarget at htarget
    rw [hto] at htarget
    exact Except.ok.inj htarget
  exact KeptOrRead.trans (.of_keptOrWiped (keptOrWiped_buyGas hbought)
    (keptOrRead_processMessageCall recipient houtput))
    (.inl ((keptOrWiped_settleGas hsettle).trans (keptOrWiped_deleteAccounts hdelete))) hlast

/-- A transaction keeps or wipes the storage of `address`, unless it reads the account.

It runs with the gas meter of its fork, at every fork that runs transactions. -/
theorem keptOrRead_processTransaction {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {tx : Transaction} {out : TransactionOutput}
    (h : processTransaction env block included tx = .ok out) :
    KeptOrRead address (.ofBlock block) out.state := by
  by_cases hhegota : .hegota ≤ fork
  · rw [processTransaction_of_hegota_le hhegota] at h
    cases h
  by_cases hglam : .glamsterdam ≤ fork
  · rw [processTransaction_of_glamsterdam hglam (Nat.lt_of_not_le hhegota)] at h
    exact keptOrRead_runTransaction h
  · rw [processTransaction_of_lt_glamsterdam (Nat.lt_of_not_le hglam)] at h
    exact keptOrRead_runTransaction h

/-! ## A message that runs no frame at the address -/

/-- Where the run of a message starts, from its first frame: a call, or a creation. -/
def FirstFrame.start (first : FirstFrame fork Meter) : BurnStart fork Meter :=
  match first.message.target with
  | some _ => .call first.message first.state first.substate first.meter
  | none => .create first.message first.state first.substate first.meter

/-- Every frame of the message that a transaction or a system call runs meets `P`. -/
def CallAll (P : Evm fork Meter → Prop) (chainId : Nat) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) : Prop :=
  ∀ first : FirstFrame fork Meter,
    prepareFirstFrame chainId message state substate auths paid = .ok first →
      ReachesAll P first.start

/-- No frame of the message that a transaction or a system call runs is at `address`. -/
def CallAway (address : Address) (chainId : Nat) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) : Prop :=
  CallAll (Meter := Meter) (fun reached => reached.message.currentTarget ≠ address) chainId message
    state substate auths paid

/-- The message of a transaction keeps or wipes the storage of `address`, if no frame runs there.
-/
theorem keptOrWiped_processMessageCall_of_away {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output)
    (away : CallAway (Meter := Meter) address chainId message state substate auths paid) :
    KeptOrWiped address state output.state := by
  have ofFrame : ∀ (evm : Evm fork Meter) (refund : Nat) (touched : Std.ExtTreeSet Address),
      (CallOutput.ofFrame evm refund touched).state = evm.state := by
    intro evm refund touched
    unfold CallOutput.ofFrame
    split <;> rfl
  rw [processMessageCall_unfold] at h
  split at h
  · -- A halt before the first frame keeps the state, up to its reads.
    split at h
    · cases h
    · cases h
      exact .of_eq fun _ => rfl
  · rename_i first hfirst
    have hstart : KeptOrWiped address state first.state := keptOrWiped_prepareFirstFrame hfirst
    have htarget := (substate_prepareFirstFrame hfirst).2.2.1
    have hfar := away first hfirst
    unfold FirstFrame.start at hfar
    rw [htarget] at hfar
    split at h
    · rename_i hnone
      rw [hnone] at hfar
      obtain ⟨⟨evm, _⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [ofFrame]
      exact hstart.trans (keptOrWiped_processCreateMessage_of_away hrun hfar)
    · rename_i t hsome
      rw [hsome] at hfar
      obtain ⟨⟨evm, _⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [ofFrame]
      exact hstart.trans (keptOrWiped_processMessage_of_away hrun hfar)

variable (Meter) in
/-- Every frame of the message that a transaction runs, with the gas meter `Meter`, meets `P`. -/
def TransactionAll (P : Evm fork Meter → Prop) (env : BlockEnvironment fork)
    (block : State.BlockState) (included : Included) (tx : Transaction) (out : TransactionOutput) :
    Prop :=
  ∀ {target bought message output settled},
    TransactionRun Meter env block included tx out target bought message output settled →
    CallAll P env.chainId.toNat
      { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } bought
      (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
      (paidWrites included.sender target tx)

variable (Meter) in
/-- No frame of the message that a transaction runs, with the gas meter `Meter`, is at `address`. -/
def TransactionAway (address : Address) (env : BlockEnvironment fork) (block : State.BlockState)
    (included : Included) (tx : Transaction) (out : TransactionOutput) : Prop :=
  TransactionAll Meter (fun reached => reached.message.currentTarget ≠ address) env block included
    tx out

/-- A transaction keeps or wipes the storage of `address`, if no frame of its message runs there.

It runs with the gas meter `Meter`. -/
theorem keptOrWiped_runTransaction_of_away {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok out)
    (away : TransactionAway Meter address env block included tx out) :
    KeptOrWiped address (.ofBlock block) out.state := by
  obtain ⟨target, bought, message, output, settled, run⟩ := runTransaction_eq_ok h
  have far := away run
  obtain ⟨-, hbought, -, houtput, -, hsettle, hdelete⟩ := run
  exact (keptOrWiped_buyGas hbought).trans
    ((keptOrWiped_processMessageCall_of_away houtput far).trans
      ((keptOrWiped_settleGas hsettle).trans (keptOrWiped_deleteAccounts hdelete)))

/-- A transaction keeps or wipes the storage of `address`, if no frame of its message runs there.

It runs with the gas meter of its fork. -/
theorem keptOrWiped_processTransaction_of_away {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    (h : processTransaction env block included tx = .ok out)
    (away : fork < .glamsterdam → TransactionAway Nat address env block included tx out)
    (awayState : .glamsterdam ≤ fork →
      TransactionAway StateGasMeter address env block included tx out) :
    KeptOrWiped address (.ofBlock block) out.state := by
  by_cases hhegota : .hegota ≤ fork
  · rw [processTransaction_of_hegota_le hhegota] at h
    cases h
  by_cases hglam : .glamsterdam ≤ fork
  · rw [processTransaction_of_glamsterdam hglam (Nat.lt_of_not_le hhegota)] at h
    exact keptOrWiped_runTransaction_of_away h (awayState hglam)
  · rw [processTransaction_of_lt_glamsterdam (Nat.lt_of_not_le hglam)] at h
    exact keptOrWiped_runTransaction_of_away h (away (Nat.lt_of_not_le hglam))

end EthLib.Execution.Transactions
