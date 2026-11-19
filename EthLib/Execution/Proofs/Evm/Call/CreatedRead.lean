module

public import EthLib.Execution.Proofs.Evm.Call.ReadsGrow
public import EthLib.Execution.Proofs.Evm.Call.ToDelete

/-!
# Proofs: every account that a call or a creation created is among its reads

A creation marks its address as created, and that mark survives a rollback.

The step that sends a creation first reads the new address.

A creation sent from outside a frame must have read its address first.

Reads never shrink, and a rollback keeps them too.

So a call keeps every created account among the account reads.

So does a creation whose address was read at its start.

From Cancun, SELFDESTRUCT marks an account for deletion only if the transaction created it.

[EIP-6780][e6780] sets that rule.

From Glamsterdam, the deletion at the end of a transaction reads the account to keep its balance.

So that deletion needs each created account among the recorded reads.

The end of a transaction is not covered here.

[EIP-7928, Scope and Inclusion][bal] asks the block access list to name every accessed account.

[e6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
[bal]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (BlockState TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Every account that the transaction created so far is among its account reads. -/
def CreatedRead (tx : TransactionState) : Prop :=
  ∀ address, address ∈ tx.createdAccounts → address ∈ tx.accountReads

/-- A transaction that starts on a block state has created no account yet. -/
theorem CreatedRead.ofBlock (block : BlockState) : CreatedRead (.ofBlock block) := by
  intro address h
  simp [TransactionState.ofBlock] at h

/-- A state with more reads and the same created accounts keeps the invariant. -/
private theorem CreatedRead.of_readsLe {tx tx' : TransactionState} (hr : tx.ReadsLe tx')
    (hc : tx'.createdAccounts = tx.createdAccounts) (h : CreatedRead tx) : CreatedRead tx' :=
  fun x hx => hr.accountReads x (h x (hc ▸ hx))

/-- A preparation of a creation whose address was read keeps the invariant. -/
private theorem CreatedRead.prepareCreation {tx tx' : TransactionState} {address : Address}
    (hp : prepareCreation fork tx address = .ok tx') (h : CreatedRead tx)
    (hread : address ∈ tx.accountReads) : CreatedRead tx' := by
  have hc : tx'.createdAccounts = tx.createdAccounts.insert address := by
    unfold Evm.prepareCreation at hp
    split at hp
    · exact TransactionState.createdAccounts_modifyState (Base.mapError_ok_iff.mp hp)
    · cases hp
      rfl
  have hr := readsLe_prepareCreation hp
  intro x hx
  rw [hc, Std.ExtTreeSet.mem_insert] at hx
  rcases hx with hx | hx
  · rw [← Std.LawfulEqCmp.compare_eq_iff_eq.mp hx]
    exact hr.accountReads _ hread
  · exact hr.accountReads x (h x hx)

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT keeps the created accounts. -/
private theorem createdAccounts_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.state.createdAccounts = evm.state.createdAccounts := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact createdAccounts_selfdestructTransfer (Base.mapError_ok_iff.mp hst)

/-- The second frame holds the reads of the first, and keeps the invariant if the first has it. -/
private def CreatedRel (a b : Evm fork Meter) : Prop :=
  a.state.ReadsLe b.state ∧ (CreatedRead a.state → CreatedRead b.state)

/-- Each write of a step keeps the reads and the invariant. -/
private theorem stepRules_createdRel : StepRules fork (CreatedRel (fork := fork) (Meter := Meter))
    where
  trans hab hbc := ⟨hab.1.trans hbc.1, fun h => hbc.2 (hab.2 h)⟩
  static h :=
    ⟨stepRules_readsLe.static h, CreatedRead.of_readsLe (stepRules_readsLe.static h) h.created⟩
  sstore evm address key value state gain h :=
    ⟨stepRules_readsLe.sstore evm address key value state gain h,
      CreatedRead.of_readsLe (stepRules_readsLe.sstore evm address key value state gain h)
        (TransactionState.createdAccounts_setStorage h)⟩
  tstore evm address key value :=
    ⟨stepRules_readsLe.tstore evm address key value,
      CreatedRead.of_readsLe (stepRules_readsLe.tstore evm address key value) rfl⟩
  log _ hs _ _ _ := by
    unfold CreatedRel
    rw [hs]
    exact ⟨.refl _, id⟩
  selfdestruct beneficiary refund h :=
    ⟨stepRules_readsLe.selfdestruct beneficiary refund h,
      CreatedRead.of_readsLe (stepRules_readsLe.selfdestruct beneficiary refund h)
        (createdAccounts_finishSelfdestruct h)⟩
  incrementNonce evm address state hn h :=
    ⟨stepRules_readsLe.incrementNonce evm address state hn h,
      CreatedRead.of_readsLe (stepRules_readsLe.incrementNonce evm address state hn h)
        (TransactionState.createdAccounts_modifyState h)⟩
  incorporate h := by
    unfold CreatedRel
    rw [state_incorporateChild]
    exact h

/-- Calls keep the invariant, and creations keep it when their address was read at the start.

Both keep every read.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
private theorem processMessage_createdRead [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        state.ReadsLe ended.val.state ∧ (CreatedRead state → CreatedRead ended.val.state)) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        state.ReadsLe ended.val.state ∧ (CreatedRead state →
          message.currentTarget ∈ state.accountReads → CreatedRead ended.val.state)) := by
  have rules := stepRules_createdRel (fork := fork) (Meter := Meter)
  refine processMessage_rel_byKind (Inv := fun _ => True)
    (Mcall := fun _ state _ _ ended =>
      state.ReadsLe ended.state ∧ (CreatedRead state → CreatedRead ended.state))
    (Mcreate := fun message state _ _ ended => state.ReadsLe ended.state ∧
      (CreatedRead state → message.currentTarget ∈ state.accountReads → CreatedRead ended.state))
    rules.refl rules.trans
    (fun _ _ => trivial) (fun _ _ _ => rules.static (staticStep_exceptionalHalt _ _))
    ?_ (fun _ _ => rules.sameContext ⟨rfl, rfl, rfl, rfl⟩)
    (fun h _ => rules.static (staticStep_runPrecompile h)) ?_ ?_ n
  · intro evm result _ h
    have k := rules.step h
    cases result with
    | next after => exact k
    | child caller message resume =>
      refine ⟨k.1, fun child after hres p => k.2 child after hres ?_⟩
      have hcur := step_eq_child_currentRead h
      revert p
      unfold ChildRelByKind ChildRel
      split
      · exact fun p => ⟨p.1, p.2⟩
      · exact fun p => ⟨p.1, fun hc => p.2 hc hcur⟩
  · intro message state entry substate entrySubstate meter ended hentry hrun
    have r := hrun trivial
    refine ⟨((readsLe_entered hentry).trans r.1).trans (readsLe_rollbackOnError _ _),
      fun hc => ?_⟩
    exact CreatedRead.of_readsLe (readsLe_rollbackOnError _ _)
      (createdAccounts_rollbackOnError _ _).1
      (r.2 (CreatedRead.of_readsLe (readsLe_entered hentry) (createdAccounts_entered hentry) hc))
  · intro message state prepared substate meter evm after hp hm hd
    refine ⟨((readsLe_prepareCreation hp).trans hm.1).trans (readsLe_depositCode hd),
      fun hc hcur => ?_⟩
    exact CreatedRead.of_readsLe (readsLe_depositCode hd) (createdAccounts_depositCode hd).1
      (hm.2 (CreatedRead.prepareCreation hp hc hcur))

/-- A call that returns a frame keeps every created account among the reads. -/
theorem createdRead_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hinv : CreatedRead state)
    (h : processMessage fork message state substate meter held = .ok ended) :
    CreatedRead ended.val.state :=
  ((processMessage_createdRead message.gas).1 message state substate meter held rfl ended h).2 hinv

/-- A creation that returns a frame keeps every created account among the reads.

The state it is sent from must already have read the address it creates. -/
theorem createdRead_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hinv : CreatedRead state) (hcurrent : message.currentTarget ∈ state.accountReads)
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    CreatedRead ended.val.state :=
  ((processMessage_createdRead message.gas).2 message state substate meter held rfl ended h).2 hinv
    hcurrent

end EthLib.Execution.Evm
