module

public import EthLib.Execution.Proofs.Evm.Call.Fresh

/-!
# Proofs: a message never marks for deletion an account with a nonce above 0 and no code

SELFDESTRUCT marks for deletion at most the account that runs it.

So only a frame that runs code at an account can mark it.

Take an account with a nonce above 0, no code, and not created in its transaction.

A message never creates it, so it keeps no code.

A call to it runs its code, which is empty, so that frame stops at once.

CALLCODE and DELEGATECALL run at the account of their sender, and no code there sends them.

A creation never goes to it, since it has a nonce.

So no frame that runs code has it as its current target, and no message marks it.

These facts hold at every fork, whether or not the message ends with an error.

The proofs about transactions use them for the sender, which has a nonce once it pays for gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (EMPTY_CODE_HASH TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The account at `address` has a nonce above 0 and no code.

Its transaction has not created it. -/
def PlainAccount (address : Address) (tx : TransactionState) : Prop :=
  1 ≤ (tx.getAccount address).nonce ∧ address ∉ tx.createdAccounts ∧
    (tx.getAccount address).codeHash = EMPTY_CODE_HASH

/-- A run that creates only fresh accounts keeps an account plain. -/
theorem PlainAccount.of_createsFresh {allowed : Address → Prop} {address : Address}
    {tx tx' : TransactionState} (h : CreatesFresh allowed tx tx') (plain : PlainAccount address tx)
    (hallowed : ¬allowed address) : PlainAccount address tx' := by
  obtain ⟨hn, hc, hcode⟩ := plain
  have hc' : address ∉ tx'.createdAccounts := fun hx =>
    (h.fresh address hx hc).elim (fun h0 => by omega) hallowed
  exact ⟨Nat.le_trans hn (h.nonce address), hc', h.code address hc' hcode⟩

/-- A caller that takes in a child marks `address` only if the caller or the child marks it. -/
theorem unmarked_incorporateChild {caller child : Evm fork Meter} {address : Address}
    (hcaller : address ∉ caller.substate.accountsToDelete)
    (hchild : address ∉ child.substate.accountsToDelete) :
    address ∉ (incorporateChild fork caller child).substate.accountsToDelete := fun hx =>
  (mem_accountsToDelete_incorporateChild.mp hx).elim hcaller fun h => hchild h.2

/-- A step from a frame that does not run at `address` never marks `address` for deletion.

The frames on the way keep the message, so they do not run at `address` either. -/
theorem stepRules_unmarked (address : Address) :
    StepRules fork (fun a b : Evm fork Meter =>
      (a.message.currentTarget ≠ address → b.message.currentTarget ≠ address) ∧
        (a.message.currentTarget ≠ address → address ∉ a.substate.accountsToDelete →
          address ∉ b.substate.accountsToDelete)) where
  trans hab hbc := ⟨fun h => hbc.1 (hab.1 h), fun h hx => hbc.2 (hab.1 h) (hab.2 h hx)⟩
  static h := ⟨fun hne => h.message ▸ hne, fun _ hx => h.toDelete ▸ hx⟩
  sstore _ _ _ _ _ _ _ := ⟨id, fun _ hx => hx⟩
  tstore _ _ _ _ := ⟨id, fun _ hx => hx⟩
  log _ _ hsub hm _ := ⟨fun hne => hm ▸ hne, fun _ hx => by rw [hsub]; exact hx⟩
  selfdestruct _ _ h := by
    refine ⟨fun hne => message_finishSelfdestruct h ▸ hne, fun hne hx => ?_⟩
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, -, h⟩ := Base.bind_ok_iff.mp h
      cases h
      dsimp only
      split
      · rw [Std.ExtTreeSet.mem_insert]
        rintro (heq | hin)
        · exact hne (Std.LawfulEqCmp.eq_of_compare heq)
        · exact hx hin
      · exact hx
  incrementNonce _ _ _ _ _ := ⟨id, fun _ hx => hx⟩
  incorporate h := ⟨fun hne => by rw [message_incorporateChild]; exact hne,
    fun hne hx => unmarked_incorporateChild hx (h.2 hne hx)⟩

/-- Every message that returns a frame keeps a plain account unmarked, unless it runs code there.

A call must run no code when its current target is that account.

A creation must not go to that account.

The account must be plain in the state that the message starts from.

If it is not marked at the start, it is not marked at the end.

That holds at every fork, whether or not the message ends with an error.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem unmarked_processMessage_induction [LawfulGasMeter Meter] (address : Address) (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        (message.currentTarget = address → message.code.size = 0) → PlainAccount address state →
          address ∉ substate.accountsToDelete →
            address ∉ ended.val.substate.accountsToDelete) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        message.currentTarget ≠ address → PlainAccount address state →
          address ∉ substate.accountsToDelete →
            address ∉ ended.val.substate.accountsToDelete) := by
  have C := (stepRules_createsFresh (fork := fork) (Meter := Meter)).and stepRules_messageCode
  have T := C.and (stepRules_unmarked address)
  let R : Evm fork Meter → Evm fork Meter → Prop := fun a b =>
    (CreatesFresh (fun _ => False) a.state b.state ∧ b.message = a.message ∧ b.code = a.code) ∧
      ((a.message.currentTarget = address → a.code.size = 0) → PlainAccount address a.state →
        address ∉ a.substate.accountsToDelete → address ∉ b.substate.accountsToDelete)
  have ofStatic : ∀ {a b : Evm fork Meter}, StaticStep a b → R a b := fun h =>
    ⟨C.static h, fun _ _ hx => h.toDelete ▸ hx⟩
  have conv : ∀ {a b : Evm fork Meter},
      (CreatesFresh (fun _ => False) a.state b.state ∧ b.message = a.message ∧ b.code = a.code) ∧
        ((a.message.currentTarget ≠ address → b.message.currentTarget ≠ address) ∧
          (a.message.currentTarget ≠ address → address ∉ a.substate.accountsToDelete →
            address ∉ b.substate.accountsToDelete)) →
      ¬(a.message.currentTarget = address ∧ a.code.size = 0) → R a b :=
    fun h hstop => ⟨h.1, fun hinv _ hx => h.2.2 (fun heq => hstop ⟨heq, hinv heq⟩) hx⟩
  let Mcall : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop :=
    fun message state substate _ ended =>
      CreatesFresh (fun _ => False) state ended.state ∧ ended.message = message ∧
        ((message.currentTarget = address → message.code.size = 0) → PlainAccount address state →
          address ∉ substate.accountsToDelete → address ∉ ended.substate.accountsToDelete)
  let Mcreate : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop :=
    fun message state substate _ ended =>
      CreatesFresh (· = message.currentTarget) state ended.state ∧
        (message.currentTarget ≠ address → PlainAccount address state →
          address ∉ substate.accountsToDelete → address ∉ ended.substate.accountsToDelete)
  have steps : ∀ {evm : Evm fork Meter} {result : StepResult fork Meter}, True →
      step fork evm = .ok result →
        StepResult.Keeps R (ChildRelByKind Mcall Mcreate) evm result := by
    intro evm result _ h
    by_cases hstop : evm.message.currentTarget = address ∧ evm.code.size = 0
    · have h' := h
      unfold step at h'
      simp only [hstop.2, Nat.not_lt_zero, ↓reduceDIte, stopStep, Functor.map, Except.map,
        Except.ok.injEq] at h'
      subst h'
      exact ofStatic (.of_sameContext ⟨rfl, rfl, rfl, rfl⟩)
    have r := T.step h
    cases result with
    | next after => exact conv r hstop
    | child caller message resume =>
      have rc := conv r.1 hstop
      refine ⟨rc, fun child after hres hc => ⟨createsFresh_messageCode_resume h hres rc.1
        (hc.mono (fun _ _ _ _ _ h => h.1) (fun _ _ _ _ _ h => h.1)), fun hinv plain hx => ?_⟩⟩
      have hne : evm.message.currentTarget ≠ address := fun heq => hstop ⟨heq, hinv heq⟩
      have hcaller : address ∉ caller.substate.accountsToDelete := r.1.2.2 hne hx
      have pcaller : PlainAccount address caller.state :=
        PlainAccount.of_createsFresh rc.1.1 plain id
      rw [(sameContext_of_step_eq_child h hres).substate]
      refine unmarked_incorporateChild hcaller ?_
      unfold ChildRelByKind ChildRel at hc
      rcases ht : message.target with _ | target
      · simp only [ht] at hc
        refine hc.2 (fun heq => ?_) pcaller hcaller
        have hd := TransactionState.nonce_eq_zero_of_accountDeployable
          (step_eq_child_deployable h ht)
        rw [heq] at hd
        have := plain.1
        omega
      · simp only [ht] at hc
        refine hc.2.2 (fun heq => ?_) pcaller hcaller
        rcases step_eq_child_staticCode h (by simp [ht]) with he | sc
        · exact absurd (he ▸ heq) hne
        · apply Classical.byContradiction
          intro hsize
          exact sc hsize (heq ▸ plain.2.2)
  have both := processMessage_rel_byKind (fork := fork) (Meter := Meter) (R := R)
    (Inv := fun _ => True) (Mcall := Mcall) (Mcreate := Mcreate)
    (fun evm => ofStatic (.refl evm))
    (fun {a b c} hab hbc => ⟨C.trans hab.1 hbc.1, fun hinv plain hx =>
        hbc.2 (by rw [hab.1.2.1, hab.1.2.2]; exact hinv)
          (PlainAccount.of_createsFresh hab.1.1 plain id) (hab.2 hinv plain hx)⟩)
    (fun _ _ => trivial)
    (fun evm error _ => ofStatic (staticStep_exceptionalHalt evm error))
    steps
    (fun _ _ => ofStatic (.of_sameContext ⟨rfl, rfl, rfl, rfl⟩))
    (fun h _ => ofStatic (staticStep_runPrecompile h))
    (fun {_ state _ substate _ _ ended} hentry hrun => by
      have hr := hrun trivial
      refine ⟨createsFresh_rollbackOnError hentry hr.1.1,
        (message_rollbackOnError state ended).trans hr.1.2.1, fun hinv plain hx => ?_⟩
      rw [(createdAccounts_rollbackOnError state ended).2]
      refine hr.2 hinv (PlainAccount.of_createsFresh (createsFresh_entered hentry) plain id) ?_
      rcases hentry with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · exact hx
      · exact hx)
    (fun hp hm hd => by
      refine ⟨createsFresh_depositCode hp hm.1 (congrArg (·.currentTarget) hm.2.1) hd,
        fun hne plain hx => ?_⟩
      rw [(createdAccounts_depositCode hd).2]
      exact hm.2.2 (fun heq => absurd heq hne)
        (PlainAccount.of_createsFresh (createsFresh_prepareCreation hp).1 plain (Ne.symm hne)) hx)
    n
  exact ⟨fun message state substate meter held hn ended h =>
      (both.1 message state substate meter held hn ended h).2.2,
    fun message state substate meter held hn ended h =>
      (both.2 message state substate meter held hn ended h).2⟩

/-- A call never marks a plain account for deletion, unless it runs code there.

It must run no code when its current target is that account.

That holds at every fork, whether or not the call ends with an error. -/
theorem unmarked_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended} {address : Address}
    (h : processMessage fork message state substate meter held = .ok ended)
    (empty : message.currentTarget = address → message.code.size = 0)
    (plain : PlainAccount address state) (unmarked : address ∉ substate.accountsToDelete) :
    address ∉ ended.val.substate.accountsToDelete :=
  (unmarked_processMessage_induction address message.gas).1 message state substate meter held rfl
    ended h empty plain unmarked

/-- A creation never marks a plain account for deletion, unless it goes to that account.

That holds at every fork, whether or not the creation ends with an error. -/
theorem unmarked_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended} {address : Address}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (ne : message.currentTarget ≠ address) (plain : PlainAccount address state)
    (unmarked : address ∉ substate.accountsToDelete) :
    address ∉ ended.val.substate.accountsToDelete :=
  (unmarked_processMessage_induction address message.gas).2 message state substate meter held rfl
    ended h ne plain unmarked

end EthLib.Execution.Evm
