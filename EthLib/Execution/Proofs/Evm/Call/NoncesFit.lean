module

public import EthLib.Execution.Proofs.Evm.Call.Nonce

/-!
# Proofs: no message raises a nonce above `2^64 - 1`

EIP-2681 limits every nonce to `2^64 - 1`.

CREATE and CREATE2 raise the nonce of the creator only when it is below that bound.

From Spurious Dragon, a creation also raises the nonce of its new address.

So a creation must start at an address whose nonce is below the bound.

Every other write keeps each nonce, or from Paris deletes an account left empty, with nonce 0.

A frame that fails rolls back to its snapshot.

So a message that starts with every nonce within the bound ends with every nonce within it.
-/

@[expose] public section

namespace EthLib.Execution.State

/-- Every account of the state has a nonce of at most `2^64 - 1`, the bound of EIP-2681.

An absent account reads as the empty account, whose nonce is 0. -/
def TransactionState.NoncesFit (tx : TransactionState) : Prop :=
  ∀ address, (tx.getAccount address).nonce ≤ Evm.MAX_NONCE

end EthLib.Execution.State

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (Account StateError TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A state whose nonces are at most those of a state within the bound is within the bound. -/
theorem NoncesFit.of_nonceLe {tx tx' : TransactionState} (h : NonceLe tx' tx)
    (hfit : tx.NoncesFit) : tx'.NoncesFit :=
  fun address => Nat.le_trans (h address) (hfit address)

/-- A rise of a nonce that is not the greatest keeps every nonce within the bound. -/
theorem noncesFit_incrementNonce {tx tx' : TransactionState} {address : Address}
    (hfit : tx.NoncesFit) (hn : (tx.getAccount address).nonce ≠ MAX_NONCE)
    (h : tx.incrementNonce fork address = .ok tx') : tx'.NoncesFit := by
  obtain ⟨hself, hother⟩ := TransactionState.getAccount_incrementNonce h
  intro other
  by_cases hne : other = address
  · subst hne
    rw [hself]
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (hfit _) hn)
  · unfold TransactionState.getAccount
    rw [hother other hne]
    exact hfit other

/-- A change of one account that keeps or lowers its nonce raises no nonce. -/
private theorem nonceLe_modifyState_rev {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account}
    (hf : ∀ account account', f account = .ok account' → account'.nonce ≤ account.nonce)
    (h : tx.modifyState fork address f = .ok tx') : NonceLe tx' tx := by
  obtain ⟨account, hfa, hself, hother⟩ := TransactionState.modifyState_eq_ok h
  intro other
  by_cases hne : other = address
  · subst hne
    rw [hself]
    exact hf _ _ hfa
  · rw [hother other hne]
    exact Nat.le_refl _

/-- A debit keeps the nonce. -/
private theorem nonce_debit_le {address : Address} {amount : U256} {account account' : Account}
    (h : Account.debit address amount account = .ok account') :
    account'.nonce ≤ account.nonce := by
  unfold Account.debit at h
  split at h <;> cases h
  exact Nat.le_refl _

/-- A credit keeps the nonce. -/
private theorem nonce_credit_le {address : Address} {amount : U256} {account account' : Account}
    (h : Account.credit address amount account = .ok account') :
    account'.nonce ≤ account.nonce := by
  unfold Account.credit at h
  split at h <;> cases h
  exact Nat.le_refl _

/-- A move of ether raises no nonce. -/
private theorem nonceLe_moveEther_rev {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    NonceLe tx' tx := by
  unfold TransactionState.moveEther at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  exact (nonceLe_modifyState_rev (fun _ _ => nonce_credit_le) h2).trans
    (nonceLe_modifyState_rev (fun _ _ => nonce_debit_le) h1)

/-- A new balance raises no nonce. -/
private theorem nonceLe_setAccountBalance_rev {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.setAccountBalance fork address amount = .ok tx') : NonceLe tx' tx :=
  nonceLe_modifyState_rev (fun _ _ hf => by cases hf; exact Nat.le_refl _) h

/-- A successful move of the balance of a destroyed account raises no nonce. -/
private theorem nonceLe_selfdestructTransfer_rev {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') : NonceLe tx' tx := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (nonceLe_setAccountBalance_rev h).trans (nonceLe_moveEther_rev h1)
    · cases h
      exact nonceLe_moveEther_rev h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (nonceLe_setAccountBalance_rev h).trans
      (nonceLe_modifyState_rev (fun _ _ => nonce_credit_le) h1)

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT raises no nonce. -/
private theorem nonceLe_finishSelfdestruct_rev {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    NonceLe after.state evm.state := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact nonceLe_selfdestructTransfer_rev (Base.mapError_ok_iff.mp hst)

/-- A new code raises no nonce. -/
private theorem nonceLe_setCode_rev {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') : NonceLe tx' tx := by
  obtain ⟨hself, hother⟩ := TransactionState.getAccount_setCode h
  intro other
  by_cases hne : other = address
  · subst hne
    rw [hself]
    exact Nat.le_refl _
  · unfold TransactionState.getAccount
    rw [hother other hne]
    exact Nat.le_refl _

/-- The state that a message starts its frame from has the nonces of the state it is sent from. -/
private theorem nonceLe_startState_rev (message : Message fork) (state : TransactionState) :
    NonceLe (startState fork message state) state := by
  unfold startState
  split
  · intro other
    by_cases hne : other = message.currentTarget
    · subst hne
      rw [TransactionState.getAccount_touchAccount_self]
      exact Nat.le_refl _
    · rw [TransactionState.getAccount_touchAccount hne]
      exact Nat.le_refl _
  · exact NonceLe.refl _

/-- A rollback to a snapshot of the same block raises no nonce of the snapshot. -/
private theorem nonceLe_restoreTxState_rev {tx snapshot : TransactionState}
    (h : tx.parent = snapshot.parent) : NonceLe (tx.restoreTxState snapshot) snapshot :=
  NonceLe.of_getAccountOptional fun address =>
    (TransactionState.getAccountOptional_restoreTxState h address).symm

/-- Each write of a step keeps every nonce within the bound, static frame or not. -/
theorem stepRules_noncesFit :
    StepRules fork (fun a b : Evm fork Meter => a.state.NoncesFit → b.state.NoncesFit) where
  trans hab hbc h := hbc (hab h)
  static h := NoncesFit.of_nonceLe
    (NonceLe.of_getAccountOptional fun address => (h.state address List.not_mem_nil).1.symm)
  sstore _ _ _ _ _ _ h := NoncesFit.of_nonceLe
    (NonceLe.of_getAccountOptional fun _ => (TransactionState.getAccountOptional_setStorage h).symm)
  tstore _ _ _ _ := NoncesFit.of_nonceLe (NonceLe.of_getAccountOptional fun _ => rfl)
  log _ hs _ _ _ h := hs ▸ h
  selfdestruct _ _ h := NoncesFit.of_nonceLe (nonceLe_finishSelfdestruct_rev h)
  incrementNonce _ _ _ hn h hfit := noncesFit_incrementNonce hfit hn h
  incorporate h := by rw [state_incorporateChild]; exact h

/-- The address of a creation that a launch sends has nonce at most 1 in its caller. -/
private theorem launchCreate_child_nonce_le {evm caller : Evm fork Meter} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : launchCreate evm value initCode salt = .ok (.child caller message resume)) :
    (caller.state.getAccount message.currentTarget).nonce ≤ 1 := by
  unfold Evm.launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, hc⟩ := Base.map_ok_iff.mp h
    cases hc
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with hr | ⟨_, hc⟩
  · obtain ⟨e1, -, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, -, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, hst, hr⟩ := Base.bind_ok_iff.mp hr
    split at hr
    · rename_i hd
      cases hr
      have h0 := TransactionState.nonce_eq_zero_of_accountDeployable hd
      obtain ⟨hself, hother⟩ :=
        TransactionState.getAccount_incrementNonce (Base.mapError_ok_iff.mp hst)
      dsimp only
      by_cases hne : address = evm.message.currentTarget
      · subst hne
        rw [hself]
        simp only [h0, Nat.le_refl]
      · unfold TransactionState.getAccount at h0 ⊢
        rw [hother address hne, h0]
        exact Nat.zero_le _
    · obtain ⟨_, -, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
  · cases hc

/-- The address of a creation that a successful step sends has nonce at most 1 in its caller.

The step checks that the address has nonce 0, then raises the nonce of the creator.

The address may be the creator itself, so its nonce is then 1. -/
theorem step_eq_child_create_nonce_le {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) (create : message.target = none) :
    (caller.state.getAccount message.currentTarget).nonce ≤ 1 := by
  unfold Evm.step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · rename_i op hop
      split at h
      · cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm <;>
          simp [hr, Functor.map, Except.map] at h
      · split at h
        · rename_i run hm
          unfold Evm.messageInstruction at hm
          cases hc : callInstruction (Meter := Meter) fork op with
          | some call =>
            simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hm
            subst hm
            cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
            all_goals first
              | (subst hc; exact absurd create (callStep_target_ne h))
              | (split at hc
                 · simp only [Option.some.injEq] at hc
                   subst hc
                   exact absurd create (callStep_target_ne h)
                 · cases hc)
          | none =>
            simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hm
            have hcreate : ∃ b, run = createStep b := by
              cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hm
              all_goals first
                | (subst hm; exact ⟨_, rfl⟩)
                | (split at hm
                   · simp only [Option.some.injEq] at hm
                     subst hm
                     exact ⟨_, rfl⟩
                   · cases hm)
            obtain ⟨b, rfl⟩ := hcreate
            obtain ⟨_, _, _, _, _, _, -, -, -, -, -, launched⟩ := createStep_eq_ok h
            exact launchCreate_child_nonce_le launched
        · cases h
  · simp [stopStep, Functor.map, Except.map] at h

/-- A call keeps every nonce within the bound, and the block of its state, after its rollback.

Its frame must do so from the state it enters. -/
private theorem noncesFit_rollbackOnError {message : Message fork}
    {state entry : TransactionState} {substate entrySubstate : Substate} {ended : Evm fork Meter}
    (hentry : Entered fork message state substate entry entrySubstate)
    (hrun : (entry.NoncesFit → ended.state.NoncesFit) ∧ ended.state.parent = entry.parent) :
    (state.NoncesFit → (rollbackOnError state ended).state.NoncesFit) ∧
      (rollbackOnError state ended).state.parent = state.parent := by
  have hp : ended.state.parent = state.parent := hrun.2.trans (parent_entered hentry)
  refine ⟨fun hfit => ?_, (parent_rollbackOnError state ended).trans hp⟩
  unfold rollbackOnError
  split
  · exact NoncesFit.of_nonceLe (nonceLe_restoreTxState_rev hp) hfit
  · apply hrun.1
    rcases hentry with ⟨-, rfl, -⟩ | ⟨-, hm, -⟩
    · exact NoncesFit.of_nonceLe (nonceLe_startState_rev message state) hfit
    · exact NoncesFit.of_nonceLe ((nonceLe_moveEther_rev hm).trans
        (nonceLe_startState_rev message state)) hfit

/-- A creation keeps every nonce within the bound, and the block of its state, after its deposit.

Its address must start with a nonce below the greatest, and its init code must keep both. -/
private theorem noncesFit_prepareCreation_depositCode {state prepared : TransactionState}
    {address : Address} {evm after : Evm fork Meter}
    (hp : prepareCreation fork state address = .ok prepared)
    (hm : (prepared.NoncesFit → evm.state.NoncesFit) ∧ evm.state.parent = prepared.parent)
    (hd : depositCode fork state evm = .ok after) :
    (state.NoncesFit → (state.getAccount address).nonce < MAX_NONCE → after.state.NoncesFit) ∧
      after.state.parent = state.parent := by
  have hpar : evm.state.parent = state.parent := hm.2.trans (parent_prepareCreation hp)
  refine ⟨fun hfit hlt => ?_, (parent_depositCode hd).trans hpar⟩
  have hprep : prepared.NoncesFit := by
    unfold prepareCreation at hp
    have h0 : ((state.destroyStorage address).markAccountCreated address).NoncesFit :=
      NoncesFit.of_nonceLe (NonceLe.of_getAccountOptional fun _ => rfl) hfit
    split at hp
    · exact noncesFit_incrementNonce h0 (Nat.ne_of_lt hlt) (Base.mapError_ok_iff.mp hp)
    · cases hp
      exact h0
  have hevm := hm.1 hprep
  rcases (depositCode_cases hd).2.2 with hs | hs | hs
  · rw [hs]
    exact NoncesFit.of_nonceLe (nonceLe_restoreTxState_rev hpar) hfit
  · rw [hs]
    exact hevm
  · exact NoncesFit.of_nonceLe (nonceLe_setCode_rev hs) hevm

/-- Every call and creation that returns a frame keeps every nonce within the bound.

A creation must start at an address whose nonce is below the greatest.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_noncesFit_induction [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        state.NoncesFit → ended.val.state.NoncesFit) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        state.NoncesFit → (state.getAccount message.currentTarget).nonce < MAX_NONCE →
        ended.val.state.NoncesFit) := by
  have T := (stepRules_noncesFit (fork := fork) (Meter := Meter)).and stepRules_parent
  have steps : ∀ {evm : Evm fork Meter} {result : StepResult fork Meter}, True →
      step fork evm = .ok result →
      StepResult.Keeps
        (fun a b => (a.state.NoncesFit → b.state.NoncesFit) ∧ b.state.parent = a.state.parent)
        (ChildRelByKind
          (fun _ state _ _ ended =>
            (state.NoncesFit → ended.state.NoncesFit) ∧ ended.state.parent = state.parent)
          (fun message state _ _ ended =>
            (state.NoncesFit → (state.getAccount message.currentTarget).nonce < MAX_NONCE →
              ended.state.NoncesFit) ∧ ended.state.parent = state.parent))
        evm result := by
    intro evm result _ h
    have r := T.step h
    cases result with
    | next after => exact r
    | child caller message resume =>
      refine ⟨r.1, fun child after hres hc => ?_⟩
      have hs : after.state = child.state :=
        (sameContext_of_step_eq_child h hres).state.trans (state_incorporateChild caller child)
      dsimp only
      rw [hs]
      unfold ChildRelByKind ChildRel at hc
      rcases ht : message.target with _ | target
      · simp only [ht] at hc
        refine ⟨fun hfit => hc.1 (r.1.1 hfit) ?_, hc.2.trans r.1.2⟩
        exact Nat.lt_of_le_of_lt (step_eq_child_create_nonce_le h ht) (by decide)
      · simp only [ht] at hc
        exact ⟨fun hfit => hc.1 (r.1.1 hfit), hc.2.trans r.1.2⟩
  have both := processMessage_rel_byKind (fork := fork) (Meter := Meter)
    (R := fun a b => (a.state.NoncesFit → b.state.NoncesFit) ∧ b.state.parent = a.state.parent)
    (Inv := fun _ => True)
    (Mcall := fun _ state _ _ ended =>
      (state.NoncesFit → ended.state.NoncesFit) ∧ ended.state.parent = state.parent)
    (Mcreate := fun message state _ _ ended =>
      (state.NoncesFit → (state.getAccount message.currentTarget).nonce < MAX_NONCE →
        ended.state.NoncesFit) ∧ ended.state.parent = state.parent)
    T.refl T.trans (fun _ _ => trivial)
    (fun evm error _ => T.static (staticStep_exceptionalHalt evm error))
    steps
    (fun _ _ => T.sameContext ⟨rfl, rfl, rfl, rfl⟩)
    (fun h _ => T.static (staticStep_runPrecompile h))
    (fun hentry hrun => noncesFit_rollbackOnError hentry (hrun trivial))
    (fun hp hm hd => noncesFit_prepareCreation_depositCode hp hm hd)
    n
  exact ⟨fun message state substate meter held hn ended h =>
      (both.1 message state substate meter held hn ended h).1,
    fun message state substate meter held hn ended h =>
      (both.2 message state substate meter held hn ended h).1⟩

/-- A call that returns a frame keeps every nonce within the bound, at every fork.

That holds whether or not the frame ends with an error. -/
theorem noncesFit_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (hfit : state.NoncesFit)
    (h : processMessage fork message state substate meter held = .ok ended) :
    ended.val.state.NoncesFit :=
  (processMessage_noncesFit_induction message.gas).1 message state substate meter held rfl ended h
    hfit

/-- A creation that returns a frame keeps every nonce within the bound, at every fork.

Its address must start with a nonce below the greatest.

That holds whether or not the frame ends with an error. -/
theorem noncesFit_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended} (hfit : state.NoncesFit)
    (htarget : (state.getAccount message.currentTarget).nonce < MAX_NONCE)
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    ended.val.state.NoncesFit :=
  (processMessage_noncesFit_induction message.gas).2 message state substate meter held rfl ended h
    hfit htarget

end EthLib.Execution.Evm
