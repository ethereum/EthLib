module

public import EthLib.Execution.Proofs.Evm.Call.NonceOrCode
public import EthLib.Execution.Proofs.Evm.Call.Rebuild
public import EthLib.Execution.Proofs.Evm.Call.ToDelete

/-!
# Proofs: a run creates accounts only where no nonce or code was

A run keeps every account that the transaction created.

Each account that it creates had no nonce or code in the state that the run started from.

So the words of such an account before the transaction never counted at an account with code.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The second state keeps every account that the first created.

Each account that it creates beyond those has no nonce or code in the first state. -/
def CreatesPlain (tx tx' : TransactionState) : Prop :=
  (∀ address, address ∈ tx.createdAccounts → address ∈ tx'.createdAccounts) ∧
    ∀ address, address ∈ tx'.createdAccounts → address ∉ tx.createdAccounts →
      ¬HasNonceOrCode tx address

/-- Two states with the same created accounts are related. -/
theorem createsPlain_of_eq {tx tx' : TransactionState}
    (h : tx'.createdAccounts = tx.createdAccounts) : CreatesPlain tx tx' :=
  ⟨fun _ hx => h ▸ hx, fun _ hx hn => absurd (h ▸ hx) hn⟩

/-- The relation passes to a later state with the same created accounts. -/
theorem CreatesPlain.of_created {tx tx' tx'' : TransactionState}
    (h : CreatesPlain tx tx') (hc : tx''.createdAccounts = tx'.createdAccounts) :
    CreatesPlain tx tx'' :=
  ⟨fun a ha => hc ▸ h.1 a ha, fun a ha hn => h.2 a (hc ▸ ha) hn⟩

/-- The relation composes when the first transition keeps each nonce or code.

An account with no nonce or code in the middle state had none in the first. -/
theorem CreatesPlain.trans {a b c : TransactionState} (hk : KeepsNonceOrCode a b)
    (hab : CreatesPlain a b) (hbc : CreatesPlain b c) : CreatesPlain a c := by
  refine ⟨fun x hx => hbc.1 x (hab.1 x hx), fun x hx hxa => ?_⟩
  by_cases hxb : x ∈ b.createdAccounts
  · exact hab.2 x hxb hxa
  · exact fun hn => hbc.2 x hx hxb (hk.2 x hn)

/-- The start of a creation at an address with no nonce or code is related to the state before. -/
theorem createsPlain_prepareCreation {state prepared : TransactionState}
    {address : Address} (hnc : ¬HasNonceOrCode state address)
    (h : prepareCreation fork state address = .ok prepared) : CreatesPlain state prepared := by
  -- The start records the address as created, and creates no other account.
  have hc : prepared.createdAccounts = state.createdAccounts.insert address := by
    unfold prepareCreation at h
    split at h
    · exact (TransactionState.createdAccounts_modifyState (Base.mapError_ok_iff.mp h)).trans rfl
    · cases h
      rfl
  refine ⟨fun x hx => hc ▸ Std.ExtTreeSet.mem_insert.mpr (.inr hx), fun x hx hxs => ?_⟩
  rw [hc] at hx
  rcases Std.ExtTreeSet.mem_insert.mp hx with heq | hx
  · cases Std.LawfulEqCmp.eq_of_compare heq
    exact hnc
  · exact absurd hx hxs

/-! ## Frames -/

/-- What a step keeps of the state: each nonce or code and the block, and the created accounts.

It also keeps the message and the code. -/
abbrev KeepsPlain (a b : Evm fork Meter) : Prop :=
  KeepsNonceOrCodeFrame a b ∧ CreatesPlain a.state b.state

/-- Each write of a step keeps each nonce or code, and creates no account. -/
theorem stepRules_keepsPlain : StepRules fork (KeepsPlain (fork := fork) (Meter := Meter)) where
  trans hab hbc := ⟨stepRules_keepsNonceOrCodeFrame.trans hab.1 hbc.1,
    CreatesPlain.trans hab.1.1.1 hab.2 hbc.2⟩
  static h := ⟨stepRules_keepsNonceOrCodeFrame.static h, createsPlain_of_eq h.created⟩
  sstore evm key value state h :=
    ⟨stepRules_keepsNonceOrCodeFrame.sstore evm key value state h,
      createsPlain_of_eq (TransactionState.createdAccounts_setStorage h)⟩
  tstore evm address key value :=
    ⟨stepRules_keepsNonceOrCodeFrame.tstore evm address key value, createsPlain_of_eq rfl⟩
  log log hs hsub hm hc :=
    ⟨stepRules_keepsNonceOrCodeFrame.log log hs hsub hm hc, createsPlain_of_eq (by rw [hs])⟩
  selfdestruct beneficiary refund h :=
    ⟨stepRules_keepsNonceOrCodeFrame.selfdestruct beneficiary refund h,
      createsPlain_of_eq (createdAccounts_finishSelfdestruct h)⟩
  incrementNonce evm state hn h :=
    ⟨stepRules_keepsNonceOrCodeFrame.incrementNonce evm state hn h,
      createsPlain_of_eq (TransactionState.createdAccounts_modifyState h)⟩
  incorporate h :=
    ⟨stepRules_keepsNonceOrCodeFrame.incorporate h.1, by rw [state_incorporateChild]; exact h.2⟩

/-- A frame runs its code only at an account with a nonce or code. -/
abbrev CodeAtNonceOrCode (evm : Evm fork Meter) : Prop :=
  evm.code.size ≠ 0 → HasNonceOrCode evm.state evm.message.currentTarget

omit [GasMeter Meter] in
/-- A frame that keeps each nonce or code of one that runs code only there does so too. -/
theorem CodeAtNonceOrCode.keeps {a b : Evm fork Meter} (ha : CodeAtNonceOrCode a)
    (hab : KeepsPlain a b) : CodeAtNonceOrCode b := by
  intro hs
  rw [hab.1.2.1]
  exact hab.1.1.1.2 _ (ha (hab.1.2.2 ▸ hs))

/-- A step that sends a message runs code. -/
theorem code_size_ne_zero_of_step_child {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) : evm.code.size ≠ 0 := by
  unfold Evm.step at h
  split at h
  · omega
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    cases h

/-- A message that a step sends meets the hypothesis that its kind of message asks for.

A call runs code only at an account with a nonce or code.

A creation goes to an address with no nonce or code.

The step must run code only at an account with a nonce or code, and its caller must keep them. -/
theorem childRelByKind_of_step
    {Mcall Mcreate : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop}
    {evm caller child : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hinv : CodeAtNonceOrCode evm) (h : step fork evm = .ok (.child caller message resume))
    (hcaller : KeepsNonceOrCode evm.state caller.state)
    (hchild : ChildRelByKind
      (fun message state substate meter ended =>
        (message.code.size ≠ 0 → HasNonceOrCode state message.currentTarget) →
          Mcall message state substate meter ended)
      (fun message state substate meter ended =>
        ¬HasNonceOrCode state message.currentTarget → Mcreate message state substate meter ended)
      caller message child) :
    ChildRelByKind Mcall Mcreate caller message child := by
  have hcur : HasNonceOrCode evm.state evm.message.currentTarget :=
    hinv (code_size_ne_zero_of_step_child h)
  unfold ChildRelByKind ChildRel at hchild ⊢
  rcases ht : message.target with _ | target
  · -- A creation goes to an address with no nonce or code in the state of its caller.
    simp only [ht] at hchild ⊢
    obtain ⟨hn0, hc0⟩ := TransactionState.accountDeployable_eq_true_iff.mp
      (accountDeployable_of_create_step hcur h ht).1
    exact hchild fun hnc => hnc.elim (fun hn => by omega) (fun hc => hc hc0)
  · -- A call runs at the current account, or runs code only at an account with code.
    simp only [ht] at hchild ⊢
    refine hchild fun hne => ?_
    rcases step_eq_child_staticCode h (by simp [ht]) with heq | hstatic
    · rw [heq]
      exact hcaller.2 _ hcur
    · exact hcaller.2 _ (.inr (hstatic hne))

/-- The frame that resumes after a message keeps the created accounts from the frame before.

That needs the caller to keep each nonce or code of the frame before. -/
theorem createsPlain_resume {evm caller child after : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) (resumed : resume child = .ok after)
    (hcaller : KeepsPlain evm caller) (hchild : CreatesPlain caller.state child.state) :
    CreatesPlain evm.state after.state := by
  -- The frame that resumes has the state of the child.
  have hs : after.state = child.state :=
    (sameContext_of_step_eq_child h resumed).state.trans (state_incorporateChild caller child)
  rw [hs]
  exact CreatesPlain.trans hcaller.1.1.1 hcaller.2 hchild

end EthLib.Execution.Evm
