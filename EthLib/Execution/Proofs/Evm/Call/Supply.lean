module

public import EthLib.Execution.Proofs.Evm.Call.Parent
public import EthLib.Execution.Proofs.Evm.Call.ToDelete
public import EthLib.Execution.Proofs.State.Supply

/-!
# Proofs: no message creates ether

Every successful step of every frame keeps or lowers the supply of ether, at every fork.

A transfer of value moves ether, and so keeps the supply.

A creation, a new code, a write of storage and the rise of a nonce keep it too.

Only SELFDESTRUCT can lower it, when the account it runs in is its own beneficiary.

Before Cancun, SELFDESTRUCT credits the beneficiary, then sets the balance of its account to 0.

So an account that is its own beneficiary loses its balance.

From Cancun, it does so only for an account created in the same transaction, by [EIP-6780][e6780].

From Glamsterdam, it never does: the account keeps its balance, by [EIP-8246][e8246].

So from Glamsterdam no step burns ether.

From Cancun, a message keeps the supply when its transaction has created no account by its end.

A frame that fails rolls back to its snapshot, which gives back the supply of its start.

So a call or creation that returns a frame ends with at most the supply it started with.

That holds whether or not the frame ends with an error.

The deletions at the end of a transaction are not part of a message, so they are not covered here.

[e6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
[e8246]: https://eips.ethereum.org/EIPS/eip-8246#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The order of supplies -/

/-- Whether `fork` is Glamsterdam or later, or Cancun or later with no account created in `tx`.

Then a message that ends in `tx` keeps the supply. -/
def BurnsNone (fork : Fork) (tx : TransactionState) : Prop :=
  .glamsterdam ≤ fork ∨ (.dencun ≤ fork ∧ ∀ address, address ∉ tx.createdAccounts)

/-- The second state has at most the supply of the first, and every created account of the first.

It has the same supply from Glamsterdam, and from Cancun when the second has no created account. -/
def SupplyLe (fork : Fork) (tx tx' : TransactionState) : Prop :=
  tx'.supply ≤ tx.supply ∧ CreatedLe tx tx' ∧ (BurnsNone fork tx' → tx'.supply = tx.supply)

/-- A state whose created accounts the other holds burns nothing when that other burns nothing. -/
theorem BurnsNone.of_createdLe {tx tx' : TransactionState} (h : CreatedLe tx tx')
    (burns : BurnsNone fork tx') : BurnsNone fork tx :=
  burns.imp id fun ⟨hfork, hnone⟩ => ⟨hfork, fun address hx => hnone address (h address hx)⟩

/-- The relation holds from a state to itself. -/
theorem SupplyLe.refl (tx : TransactionState) : SupplyLe fork tx tx :=
  ⟨Nat.le_refl _, fun _ hx => hx, fun _ => rfl⟩

/-- Two steps that each keep or lower the supply keep or lower it together. -/
theorem SupplyLe.trans {a b c : TransactionState} (hab : SupplyLe fork a b)
    (hbc : SupplyLe fork b c) : SupplyLe fork a c :=
  ⟨Nat.le_trans hbc.1 hab.1, fun x hx => hbc.2.1 x (hab.2.1 x hx),
    fun burns => (hbc.2.2 burns).trans (hab.2.2 (burns.of_createdLe hbc.2.1))⟩

/-- A step that keeps the supply and every created account keeps the relation. -/
theorem SupplyLe.of_supply_eq {tx tx' : TransactionState} (supply : tx'.supply = tx.supply)
    (created : CreatedLe tx tx') : SupplyLe fork tx tx' :=
  ⟨Nat.le_of_eq supply, created, fun _ => supply⟩

/-- A step that keeps the supply and the created accounts keeps the relation. -/
theorem SupplyLe.of_eq {tx tx' : TransactionState} (supply : tx'.supply = tx.supply)
    (created : tx'.createdAccounts = tx.createdAccounts) : SupplyLe fork tx tx' :=
  of_supply_eq supply fun _ hx => created ▸ hx

/-! ## The writes of the state -/

/-- The wei that the move of the balance of SELFDESTRUCT burns, in the state `tx`.

It burns the balance of the account it runs in, when that account is its own beneficiary.

Before Cancun, it burns it for every such account.

From Cancun, it burns it only for an account created in the same transaction.

From Glamsterdam, it never burns it. -/
def selfdestructBurn (fork : Fork) (tx : TransactionState) (originator beneficiary : Address) :
    Nat :=
  if originator = beneficiary ∧
      (fork < .dencun ∨ (fork < .glamsterdam ∧ originator ∈ tx.createdAccounts)) then
    tx.balanceOf originator
  else 0

/-- A successful move of the balance of SELFDESTRUCT lowers the supply by exactly its burn. -/
theorem supply_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    tx'.supply + selfdestructBurn fork tx originator beneficiary = tx.supply := by
  have h0 : (0 : U256).toNat = 0 := rfl
  unfold selfdestructTransfer at h
  split at h
  · rename_i hdencun
    obtain ⟨mid, hm, h⟩ := Base.bind_ok_iff.mp h
    have moved := TransactionState.supply_moveEther hm
    have created := TransactionState.createdAccounts_moveEther hm
    split at h
    · -- An account created here and its own beneficiary loses the balance it gets back.
      rename_i hburn
      have hs := TransactionState.supply_setAccountBalance h
      rw [h0] at hs
      by_cases same : originator = beneficiary
      · subst same
        have balance := (TransactionState.moveEther_self hm).1
        simp only [selfdestructBurn, true_and, created ▸ hburn, or_true, ↓reduceIte]
        unfold TransactionState.balanceOf at hs ⊢
        rw [balance] at hs
        omega
      · obtain ⟨-, -, balance, -⟩ := TransactionState.moveEther_eq_ok same hm
        have hb : mid.balanceOf originator = 0 := by
          unfold TransactionState.balanceOf
          rw [balance, BitVec.sub_self]
          rfl
        simp only [selfdestructBurn, same, false_and, ↓reduceIte]
        omega
    · rename_i hburn
      cases h
      have notBurn : ¬(originator = beneficiary ∧
          (fork < .dencun ∨ (fork < .glamsterdam ∧ originator ∈ tx.createdAccounts))) := by
        rintro ⟨-, hlt | hcreated⟩
        · exact Nat.not_lt_of_ge hdencun hlt
        · exact hburn (created ▸ hcreated)
      simp only [selfdestructBurn, notBurn, ↓reduceIte, Nat.add_zero]
      exact moved
  · -- Before Cancun, the balance goes to the beneficiary, then the account is set to 0.
    rename_i hdencun
    obtain ⟨mid, hm, h⟩ := Base.bind_ok_iff.mp h
    have added := TransactionState.supply_createEther hm
    have hs := TransactionState.supply_setAccountBalance h
    have balance := (TransactionState.getAccount_createEther hm originator).1
    rw [h0] at hs
    unfold TransactionState.balanceOf at hs
    rw [balance] at hs
    by_cases same : originator = beneficiary
    · subst same
      simp only [selfdestructBurn, true_and,
        (show fork < .dencun from Nat.lt_of_not_ge hdencun), true_or, ↓reduceIte]
      simp only [↓reduceIte] at hs
      unfold TransactionState.balanceOf
      omega
    · simp only [selfdestructBurn, same, false_and, ↓reduceIte]
      simp only [Ne.symm same, ↓reduceIte] at hs
      omega

/-- An account with no balance burns nothing. -/
theorem selfdestructBurn_eq_zero {state : TransactionState} {originator beneficiary : Address}
    (balance : state.balanceOf originator = 0) :
    selfdestructBurn fork state originator beneficiary = 0 := by
  unfold selfdestructBurn
  split <;> first | assumption | rfl

/-- A move of the balance of SELFDESTRUCT that burns some wei leaves its account with no balance. -/
theorem balanceOf_selfdestructTransfer_eq_zero {state after : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork state originator beneficiary = .ok after)
    (nonzero : selfdestructBurn fork state originator beneficiary ≠ 0) :
    after.balanceOf originator = 0 := by
  have setZero : ∀ {a b : TransactionState}, a.setAccountBalance fork originator 0 = .ok b →
      b.balanceOf originator = 0 := by
    intro a b h
    obtain ⟨account, changed, read, -⟩ := TransactionState.modifyState_eq_ok h
    cases changed
    unfold TransactionState.balanceOf
    rw [read]
    rfl
  unfold selfdestructTransfer at h
  split at h
  · rename_i hdencun
    obtain ⟨mid, moved, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact setZero h
    · rename_i notCreated
      cases h
      apply False.elim
      apply nonzero
      unfold selfdestructBurn
      split
      · rename_i condition
        rcases condition.2 with early | created
        · exact False.elim (Nat.not_lt_of_ge hdencun early)
        · exact False.elim (notCreated
            (TransactionState.createdAccounts_moveEther moved ▸ created))
      · rfl
  · obtain ⟨mid, _, h⟩ := Base.bind_ok_iff.mp h
    exact setZero h

/-- A burn of SELFDESTRUCT above 0 is from an account to itself, at a fork before Glamsterdam. -/
theorem selfdestructBurn_ne_zero {tx : TransactionState} {originator beneficiary : Address}
    (h : selfdestructBurn fork tx originator beneficiary ≠ 0) :
    originator = beneficiary ∧ fork < .glamsterdam := by
  sorry

/-- A successful move of the balance of SELFDESTRUCT keeps or lowers the supply.

It keeps it exactly from Glamsterdam, and from Cancun when the end state has no created account. -/
theorem supplyLe_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    SupplyLe fork tx tx' := by
  have created := createdAccounts_selfdestructTransfer h
  have burned := supply_selfdestructTransfer h
  refine ⟨by omega, fun _ hx => created ▸ hx, fun burns => ?_⟩
  suffices selfdestructBurn fork tx originator beneficiary = 0 by omega
  unfold selfdestructBurn
  split
  rotate_left
  · rfl
  rename_i burnt
  exfalso
  obtain ⟨-, early | ⟨early, hcreated⟩⟩ := burnt
  · rcases burns with hglam | ⟨hdencun, -⟩
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le early (Nat.le_trans (by decide) hglam))
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le early hdencun)
  · rcases burns with hglam | ⟨-, hnone⟩
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le early hglam)
    · exact hnone originator (created ▸ hcreated)

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT keeps or lowers the supply. -/
theorem supplyLe_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    SupplyLe fork evm.state after.state := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact supplyLe_selfdestructTransfer (Base.mapError_ok_iff.mp hst)

/-- A successful preparation of a creation keeps the supply exactly. -/
theorem supply_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') : tx'.supply = tx.supply := by
  unfold prepareCreation at h
  split at h
  · rw [TransactionState.supply_incrementNonce (Base.mapError_ok_iff.mp h),
      TransactionState.supply_markAccountCreated, TransactionState.supply_destroyStorage]
  · cases h
    rw [TransactionState.supply_markAccountCreated, TransactionState.supply_destroyStorage]

/-- A successful preparation of a creation keeps the supply. -/
theorem supplyLe_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') : SupplyLe fork tx tx' :=
  SupplyLe.of_supply_eq (supply_prepareCreation h) (createdLe_prepareCreation h)

/-- The state that a message starts its frame from has the supply of the state it is sent from. -/
theorem supply_startState (message : Message fork) (state : TransactionState) :
    (startState fork message state).supply = state.supply := by
  unfold startState
  split
  · exact TransactionState.supply_touchAccount _ _
  · rfl

/-- The state that a message enters has the supply of the state it is sent from.

A move of its value keeps the supply. -/
theorem supply_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    entry.supply = state.supply := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, moved, -⟩
  · exact supply_startState _ _
  · exact (TransactionState.supply_moveEther moved).trans (supply_startState _ _)

/-- A successful deposit of code ends with the supply of the snapshot, or of the init code's end.

The first case is a creation that fails, and rolls back to the snapshot. -/
theorem supply_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (hp : evm.state.parent = snapshot.parent) (h : depositCode fork snapshot evm = .ok after) :
    after.state.supply = snapshot.supply ∨ after.state.supply = evm.state.supply := by
  rcases (depositCode_cases h).2.2 with hs | hs | hs
  · rw [hs]
    exact .inl (TransactionState.supply_restoreTxState hp)
  · rw [hs]
    exact .inr rfl
  · exact .inr (TransactionState.supply_setCode hs)

/-- A successful deposit of code keeps or lowers the supply of the state before the creation.

The frame at the end of the init code must be in this relation to that state, with its block. -/
theorem supplyLe_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (hle : SupplyLe fork snapshot evm.state) (hp : evm.state.parent = snapshot.parent)
    (h : depositCode fork snapshot evm = .ok after) : SupplyLe fork snapshot after.state := by
  have created : CreatedLe snapshot after.state :=
    fun x hx => (createdAccounts_depositCode h).1 ▸ hle.2.1 x hx
  rcases supply_depositCode hp h with back | kept
  · exact SupplyLe.of_supply_eq back created
  · refine ⟨kept ▸ hle.1, created, fun burns => kept.trans (hle.2.2 ?_)⟩
    rwa [BurnsNone, ← (createdAccounts_depositCode h).1]

/-! ## A step -/

/-- Each write of a step keeps or lowers the supply, static frame or not. -/
theorem stepRules_supplyLe :
    StepRules fork (fun a b : Evm fork Meter => SupplyLe fork a.state b.state) where
  trans := SupplyLe.trans
  static h := SupplyLe.of_eq (TransactionState.supply_eq_of_sameOutside h.state) h.created
  sstore _ _ _ _ _ _ h :=
    SupplyLe.of_eq (TransactionState.supply_setStorage h)
      (TransactionState.createdAccounts_setStorage h)
  tstore _ _ _ _ := SupplyLe.of_eq rfl rfl
  log _ hs _ _ _ := by rw [hs]; exact SupplyLe.refl _
  selfdestruct _ _ h := supplyLe_finishSelfdestruct h
  incrementNonce _ _ _ h :=
    SupplyLe.of_eq (TransactionState.supply_incrementNonce h)
      (TransactionState.createdAccounts_modifyState h)
  incorporate h := by rw [state_incorporateChild]; exact h

/-- Each write of a step other than SELFDESTRUCT keeps the supply exactly. -/
theorem ordinaryStepRules_supply :
    OrdinaryStepRules fork (fun a b : Evm fork Meter => b.state.supply = a.state.supply) where
  trans hab hbc := hbc.trans hab
  static h := TransactionState.supply_eq_of_sameOutside h.state
  sstore _ _ _ _ _ _ h := TransactionState.supply_setStorage h
  tstore _ _ _ _ := rfl
  log _ hs _ _ _ := by rw [hs]
  incrementNonce _ _ _ h := TransactionState.supply_incrementNonce h
  incorporate h := by rw [state_incorporateChild]; exact h

/-! ## Messages -/

/-- Every successful call and creation keeps or lowers the supply, at every fork.

It keeps it exactly from Glamsterdam, and from Cancun when the end state has no created account.

It also keeps the block of the state.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_supplyLe [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        SupplyLe fork state ended.val.state ∧ ended.val.state.parent = state.parent) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        SupplyLe fork state ended.val.state ∧ ended.val.state.parent = state.parent) :=
  (stepRules_supplyLe (fork := fork) (Meter := Meter)).and stepRules_parent
    |>.processMessage
    (M := fun _ state _ _ ended =>
      SupplyLe fork state ended.state ∧ ended.state.parent = state.parent)
    (fun {message state state1 _ _ _ ended} hentry hrun => by
      have h1 : SupplyLe fork state state1 ∧ state1.parent = state.parent :=
        ⟨SupplyLe.of_eq (supply_entered hentry) (createdAccounts_entered hentry),
          parent_entered hentry⟩
      obtain ⟨hle, hpar⟩ := hrun
      have hp : ended.state.parent = state.parent := hpar.trans h1.2
      refine ⟨?_, (parent_rollbackOnError state ended).trans hp⟩
      unfold rollbackOnError
      split
      · exact SupplyLe.of_supply_eq (TransactionState.supply_restoreTxState hp)
          fun x hx => (h1.1.trans hle).2.1 x hx
      · exact h1.1.trans hle)
    (fun hp hm hd =>
      ⟨supplyLe_depositCode ((supplyLe_prepareCreation hp).trans hm.1)
          (hm.2.trans (parent_prepareCreation hp)) hd,
        (parent_depositCode hd).trans (hm.2.trans (parent_prepareCreation hp))⟩)
    (fun h => h) n

/-- A call that returns a frame keeps or lowers the supply, at every fork.

It keeps it exactly from Glamsterdam, and from Cancun when the end state has no created account.

That holds whether or not the frame ends with an error. -/
theorem supplyLe_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    SupplyLe fork state ended.val.state :=
  ((processMessage_supplyLe message.gas).1 message state substate meter held rfl ended h).1

/-- A creation that returns a frame keeps or lowers the supply, at every fork.

It keeps it exactly from Glamsterdam, and from Cancun when the end state has no created account.

That holds whether or not the frame ends with an error. -/
theorem supplyLe_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    SupplyLe fork state ended.val.state :=
  ((processMessage_supplyLe message.gas).2 message state substate meter held rfl ended h).1

end EthLib.Execution.Evm
