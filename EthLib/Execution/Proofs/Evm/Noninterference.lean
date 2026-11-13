module

public import EthLib.Execution.Proofs.Evm.Instructions.AccountData
public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Reads
public import EthLib.Execution.Proofs.State.Agreement

/-!
# Proofs: changing state outside an instruction's read

The two frames differ only in their transaction state.

Their stack, gas meter and substate, including the warm access sets, are the same.

BALANCE depends only on the balance at its address, and SLOAD only on the word at its slot.

EXTCODEHASH depends on its account, since the empty account gives zero.

Agreement there gives the same error, or the same frame with the other state and its read recorded.

The file then covers every instruction of the dispatch.

The calls and the creations are outside the dispatch.

On two frames whose states agree on some sets, an instruction gives the same failure in both.

That holds unless the failure aborts the run.

On success, it gives agreeing frames, when the sets hold every read of the result.

The sets must also hold the current account.

The code hash of each account in the first set must be empty, written, or in the code set.

SELFDESTRUCT reads the balance of the current account to price a new account.

These are local steps toward the coverage of [EIP-7928, Scope and Inclusion][bal].

The warm access sets determine the charges in [EIP-2929, Storage read changes][warm].

[bal]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
[warm]: https://eips.ethereum.org/EIPS/eip-2929#storage-read-changes
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Hash32 U256 toAddressMasked)
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState (AgreesOn)

variable {fork : Base.Fork} {Meter : Type} [GasMeter Meter]

/-- Changing the state keeps BALANCE's result when the balance it reads agrees.

On success, the other state receives exactly the account read. -/
theorem balanceStep_congr_state {evm : Evm fork Meter} {word : U256} {rest : List U256}
    (stack : evm.stack.val = word :: rest) (other : State.TransactionState)
    (read : (other.getAccount (toAddressMasked word)).balance =
      (evm.state.getAccount (toAddressMasked word)).balance) :
    balanceStep { evm with state := other } =
      (balanceStep evm).map (fun after =>
        { after with state := other.recordAccountRead (toAddressMasked word) }) := by
  rw [balanceStep_cons (evm := { evm with state := other }) stack, balanceStep_cons stack]
  by_cases berlin : fork ≥ .berlin <;>
    simp only [accessAddress, berlin, ↓reduceIte, Except.map] <;>
    split <;> simp_all

/-- Changing the state keeps SLOAD's result when the word it reads agrees.

On success, the other state receives exactly the storage read. -/
theorem sloadStep_congr_state {evm : Evm fork Meter} {word : U256} {rest : List U256}
    (stack : evm.stack.val = word :: rest) (other : State.TransactionState)
    (read : other.getStorage evm.message.currentTarget (U256.toBeBytes word) =
      evm.state.getStorage evm.message.currentTarget (U256.toBeBytes word)) :
    sloadStep { evm with state := other } =
      (sloadStep evm).map (fun after =>
        { after with
          state := other.recordStorageRead evm.message.currentTarget (U256.toBeBytes word) }) := by
  rw [sloadStep_cons (evm := { evm with state := other }) stack, sloadStep_cons stack]
  by_cases berlin : fork ≥ .berlin <;>
    simp only [accessStorageKey, berlin, ↓reduceIte, Except.map] <;>
    split <;> simp_all

/-- Changing the state keeps EXTCODEHASH's result when the account it reads agrees.

On success, the other state receives exactly the account read. -/
theorem extcodehashStep_congr_state {evm : Evm fork Meter} {word : U256} {rest : List U256}
    (stack : evm.stack.val = word :: rest) (other : State.TransactionState)
    (read : other.getAccount (toAddressMasked word) =
      evm.state.getAccount (toAddressMasked word)) :
    extcodehashStep { evm with state := other } =
      (extcodehashStep evm).map (fun after =>
        { after with state := other.recordAccountRead (toAddressMasked word) }) := by
  rw [extcodehashStep_cons (evm := { evm with state := other }) stack, extcodehashStep_cons stack]
  by_cases berlin : fork ≥ .berlin <;>
    simp only [accessAddress, berlin, ↓reduceIte, Except.map] <;>
    split <;> simp_all

/-! ## Frames whose states agree -/

/-- Two frames that differ only in their states, which agree on four sets.

The sets name addresses, whole storages, slots and code hashes, as for two transaction states. -/
structure FrameAgrees (account allStorage : Address → Prop) (slot : Address → Bytes32 → Prop)
    (code : Hash32 → Prop) (a b : Evm fork Meter) : Prop where
  /-- Apart from the state, the two frames are equal. -/
  rest : b = { a with state := b.state }
  /-- The two states agree on the four sets. -/
  state : AgreesOn account allStorage slot code a.state b.state

/-- Every read that a state records is in the sets.

Each account read is in the first set, and each storage read is in the second. -/
structure ReadsIn (account : Address → Prop) (slot : Address → Bytes32 → Prop)
    (tx : State.TransactionState) : Prop where
  /-- Each account that the state read. -/
  account : ∀ address, address ∈ tx.accountReads → account address
  /-- Each storage key that the state read, with its address. -/
  slot : ∀ address key, key ∈ tx.storageReads.getD address ∅ → slot address key

/-- The code hash of each account in the first set is empty, written, or in the second set. -/
def CodesIn (account : Address → Prop) (code : Hash32 → Prop)
    (tx : State.TransactionState) : Prop :=
  ∀ address, account address →
    (tx.getAccount address).codeHash = EMPTY_CODE_HASH ∨
      (tx.getAccount address).codeHash ∈ tx.codeWrites ∨ code (tx.getAccount address).codeHash

/-! ## Steps that never touch the state -/

/-- A step that neither reads nor writes the state.

Replacing the state before the step replaces it after the step. -/
private def StateFree (run : Evm fork Meter → Except EvmError (Evm fork Meter)) : Prop :=
  ∀ evm other, run { evm with state := other } =
    (fun after => { after with state := other }) <$> run evm

omit [GasMeter Meter] in
private theorem popWord_withState (evm : Evm fork Meter) (other : State.TransactionState) :
    popWord { evm with state := other } =
      (fun p => (p.1, { p.2 with state := other })) <$> popWord evm := by
  simp only [popWord]
  cases evm.stack.pop <;> rfl

omit [GasMeter Meter] in
private theorem pushWord_withState (evm : Evm fork Meter) (other : State.TransactionState)
    (x : U256) :
    pushWord { evm with state := other } x =
      (fun after => { after with state := other }) <$> pushWord evm x := by
  simp only [pushWord]
  cases evm.stack.push x <;> rfl

private theorem chargeGas_withState (evm : Evm fork Meter) (other : State.TransactionState)
    (amount : Nat) :
    chargeGas { evm with state := other } amount =
      (fun after => { after with state := other }) <$> chargeGas evm amount := by
  simp only [chargeGas]
  cases GasMeter.charge evm.gas amount <;> rfl

private theorem chargeGasAndMemory_withState (evm : Evm fork Meter)
    (other : State.TransactionState) (cost : Nat) (ranges : List (U256 × U256)) :
    chargeGasAndMemory { evm with state := other } cost ranges =
      (fun after => { after with state := other }) <$> chargeGasAndMemory evm cost ranges := by
  simp only [chargeGasAndMemory, chargeGas_withState, bind_map_left, map_bind, map_pure]

omit [GasMeter Meter] in
private theorem popTopics_withState (evm : Evm fork Meter) (other : State.TransactionState)
    (n : Nat) :
    popTopics { evm with state := other } n =
      (fun p => (p.1, { p.2 with state := other })) <$> popTopics evm n := by
  induction n generalizing evm with
  | zero => rfl
  | succ k ih =>
    simp only [popTopics, popWord_withState, bind_map_left, map_bind, map_pure, ih]

/-- Unfold a step and move the replaced state through each of its parts. -/
local macro "state_free" : tactic =>
  `(tactic| (simp only [popWord_withState, pushWord_withState, chargeGas_withState,
               chargeGasAndMemory_withState, popTopics_withState, bind_map_left, map_bind,
               map_pure, advance, bind_assoc, pure_bind]
             repeat' (first
               | rfl
               | refine congrArg (fun k => _ >>= k) (funext fun _ => ?_)
               | (split <;> simp_all [map_pure, throw, throwThe, MonadExceptOf.throw]))))

private theorem unaryOp_stateFree (cost : Nat) (f : U256 → U256) :
    StateFree (unaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro evm other
  simp only [unaryOp]
  state_free

private theorem binaryOp_stateFree (cost : Nat) (f : U256 → U256 → U256) :
    StateFree (binaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro evm other
  simp only [binaryOp]
  state_free

private theorem ternaryOp_stateFree (cost : Nat) (f : U256 → U256 → U256 → U256) :
    StateFree (ternaryOp (fork := fork) (Meter := Meter) cost f) := by
  intro evm other
  simp only [ternaryOp]
  state_free

private theorem readFrame_stateFree (cost : Nat) (value : Evm fork Meter → U256)
    (hvalue : ∀ evm other, value { evm with state := other } = value evm) :
    StateFree (readFrame cost value) := by
  intro evm other
  simp only [readFrame]
  state_free
  simp only [hvalue]

private theorem expStep_stateFree : StateFree (expStep (Meter := Meter) fork) := by
  intro evm other
  simp only [expStep]
  state_free

private theorem keccak256Step_stateFree :
    StateFree (keccak256Step (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [keccak256Step]
  state_free

private theorem popStep_stateFree : StateFree (popStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [popStep]
  state_free

private theorem pushN_stateFree (n : Fin 33) :
    StateFree (pushN (fork := fork) (Meter := Meter) n) := by
  intro evm other
  simp only [pushN]
  state_free

private theorem dupN_stateFree (n : Fin 16) :
    StateFree (dupN (fork := fork) (Meter := Meter) n) := by
  intro evm other
  simp only [dupN]
  state_free

private theorem swapN_stateFree (n : Fin 16) :
    StateFree (swapN (fork := fork) (Meter := Meter) n) := by
  intro evm other
  simp only [swapN]
  state_free
  rename_i a
  rcases a with ⟨_, ⟨_ | ⟨top, rest⟩, h⟩⟩
  · rfl
  · dsimp only
    cases rest[n.val]? <;> rfl

private theorem dupnStep_stateFree : StateFree (dupnStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [dupnStep]
  state_free

private theorem swapnStep_stateFree : StateFree (swapnStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [swapnStep]
  state_free
  rename_i a
  cases decodeSingle (immediateByte a.code a.pc) with
  | none => rfl
  | some k =>
    dsimp only
    cases exchangeItems a.stack 0 k <;> rfl

private theorem exchangeStep_stateFree :
    StateFree (exchangeStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [exchangeStep]
  state_free
  rename_i a
  cases decodePair (immediateByte a.code a.pc) with
  | none => rfl
  | some k =>
    dsimp only
    cases exchangeItems a.stack k.1 k.2 <;> rfl

omit [GasMeter Meter] in
private theorem stopStep_stateFree : StateFree (stopStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [stopStep]
  state_free

private theorem jumpStep_stateFree : StateFree (jumpStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [jumpStep]
  state_free

private theorem jumpiStep_stateFree : StateFree (jumpiStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [jumpiStep]
  state_free

private theorem jumpdestStep_stateFree :
    StateFree (jumpdestStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [jumpdestStep]
  state_free

private theorem mloadStep_stateFree : StateFree (mloadStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [mloadStep]
  state_free

private theorem mstoreStep_stateFree : StateFree (mstoreStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [mstoreStep]
  state_free

private theorem mstore8Step_stateFree :
    StateFree (mstore8Step (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [mstore8Step]
  state_free

private theorem mcopyStep_stateFree : StateFree (mcopyStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [mcopyStep]
  state_free

private theorem calldataloadStep_stateFree :
    StateFree (calldataloadStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [calldataloadStep]
  state_free

private theorem copyToMemory_stateFree (base : Nat) (source : Evm fork Meter → ByteArray)
    (hsource : ∀ evm other, source { evm with state := other } = source evm) :
    StateFree (fun evm => copyToMemory base (source evm) evm) := by
  intro evm other
  simp only [copyToMemory, hsource]
  state_free

private theorem returndatacopyStep_stateFree :
    StateFree (returndatacopyStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [returndatacopyStep]
  state_free

private theorem returnStep_stateFree : StateFree (returnStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [returnStep, haltWithOutput]
  state_free

private theorem revertStep_stateFree : StateFree (revertStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [revertStep, haltWithOutput]
  state_free

private theorem blockhashStep_stateFree :
    StateFree (blockhashStep (fork := fork) (Meter := Meter)) := by
  intro evm other
  simp only [blockhashStep]
  state_free

private theorem blobhashStep_stateFree (h : .dencun ≤ fork) :
    StateFree (blobhashStep (Meter := Meter) h) := by
  intro evm other
  simp only [blobhashStep]
  state_free

private theorem logStep_stateFree (n : Nat) :
    StateFree (logStep (fork := fork) (Meter := Meter) n) := by
  intro evm other
  simp only [logStep]
  state_free

private theorem stackOnlyStep_stateFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : stackOnlyStep fork op = some run) : StateFree run := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | with_reducible exact unaryOp_stateFree _ _
    | with_reducible exact binaryOp_stateFree _ _
    | with_reducible exact ternaryOp_stateFree _ _
    | with_reducible exact expStep_stateFree
    | with_reducible exact keccak256Step_stateFree
    | with_reducible exact popStep_stateFree
    | with_reducible exact pushN_stateFree _
    | with_reducible exact dupN_stateFree _
    | with_reducible exact swapN_stateFree _
    | with_reducible exact dupnStep_stateFree
    | with_reducible exact swapnStep_stateFree
    | with_reducible exact exchangeStep_stateFree

private theorem controlFlowStep_stateFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : controlFlowStep op = some run) : StateFree run := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  · exact stopStep_stateFree
  · exact jumpStep_stateFree
  · exact jumpiStep_stateFree
  · exact readFrame_stateFree _ _ fun _ _ => rfl
  · exact readFrame_stateFree _ _ fun _ _ => rfl
  · exact jumpdestStep_stateFree

private theorem memoryDataStep_stateFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : memoryDataStep op = some run) : StateFree run := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  all_goals first
    | with_reducible exact mloadStep_stateFree
    | with_reducible exact mstoreStep_stateFree
    | with_reducible exact mstore8Step_stateFree
    | with_reducible exact mcopyStep_stateFree
    | with_reducible exact calldataloadStep_stateFree
    | with_reducible exact returndatacopyStep_stateFree
    | with_reducible exact readFrame_stateFree _ _ fun _ _ => rfl
    | with_reducible exact copyToMemory_stateFree _ (fun evm => evm.message.data) fun _ _ => rfl
    | with_reducible exact copyToMemory_stateFree _ (fun evm => evm.code) fun _ _ => rfl

private theorem returnOpStep_stateFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some run) : StateFree run := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  · subst hstep
    exact returnStep_stateFree
  · split at hstep
    · cases hstep
      exact revertStep_stateFree
    · cases hstep

private theorem environmentStep_stateFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : environmentStep fork op = some run) : StateFree run := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | with_reducible exact blockhashStep_stateFree
    | with_reducible exact blobhashStep_stateFree _
    | with_reducible exact readFrame_stateFree _ _ fun _ _ => rfl

private theorem logOpStep_stateFree {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : logOpStep op = some run) : StateFree run := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact logStep_stateFree _

/-! ## Steps that keep agreeing frames -/

/-- From agreeing frames, a step fails alike or gives agreeing frames.

The code of the first set and the current account must agree.

A failure that does not abort the run is the same in both frames.

A success with its reads in the sets gives agreeing frames. -/
private def KeepsAgreement (account allStorage : Address → Prop) (slot : Address → Bytes32 → Prop)
    (code : Hash32 → Prop) (run : Evm fork Meter → Except EvmError (Evm fork Meter)) : Prop :=
  ∀ e1 e2, FrameAgrees account allStorage slot code e1 e2 → CodesIn account code e1.state →
    account e1.message.currentTarget →
    (∀ err, run e1 = .error err → err.aborts = false → run e2 = .error err) ∧
      ∀ a1, run e1 = .ok a1 → ReadsIn account slot a1.state →
        ∃ a2, run e2 = .ok a2 ∧ FrameAgrees account allStorage slot code a1 a2

omit [GasMeter Meter] in
private theorem keepsAgreement_of_stateFree {account allStorage : Address → Prop}
    {slot : Address → Bytes32 → Prop} {code : Hash32 → Prop}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} (hfree : StateFree run)
    (hstate : ∀ {evm after}, run evm = .ok after → after.state = evm.state) :
    KeepsAgreement account allStorage slot code run := by
  intro e1 e2 hrel _ _
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  rw [hfree e1 s]
  refine ⟨fun err h _ => by rw [h]; rfl, fun a1 h _ => ⟨_, by rw [h]; rfl, rfl, ?_⟩⟩
  rw [hstate h]
  exact hrel.state

omit [GasMeter Meter] in
private theorem popWord_of_nil {evm : Evm fork Meter} (h : evm.stack.val = []) :
    popWord evm = .error .stackUnderflow := by
  have hstack : evm.stack = ⟨[], h ▸ evm.stack.property⟩ := Subtype.ext h
  simp [popWord, hstack, Stack.pop, bind, Except.bind]

variable {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
  {code : Hash32 → Prop}

private theorem balanceStep_keeps :
    KeepsAgreement account allStorage slot code (balanceStep (fork := fork) (Meter := Meter)) := by
  intro e1 e2 hrel _ _
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  rcases hs : e1.stack.val with _ | ⟨word, rest⟩
  · simp only [balanceStep, popWord_of_nil hs, popWord_of_nil (evm := { e1 with state := s }) hs]
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  refine ⟨fun err h _ => ?_, fun a1 h reads => ?_⟩
  · rw [balanceStep_cons hs] at h
    rw [balanceStep_cons (evm := { e1 with state := s }) hs]
    by_cases berlin : fork ≥ .berlin <;>
      simp only [accessAddress, berlin, ↓reduceIte, Except.map] at h ⊢ <;> split at h <;> simp_all
  · have hacc := reads.account _ (mem_accountReads_balanceStep hs h)
    have hread := hrel.state.getAccount_eq (.inr hacc)
    have self := balanceStep_congr_state hs e1.state rfl
    rw [h] at self
    have hst : a1.state = e1.state.recordAccountRead (toAddressMasked word) :=
      congrArg Evm.state (Except.ok.inj self)
    rw [balanceStep_congr_state hs s (by rw [hread]), h]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [hst]
    exact hrel.state.recordAccountRead _

private theorem extcodehashStep_keeps :
    KeepsAgreement account allStorage slot code
      (extcodehashStep (fork := fork) (Meter := Meter)) := by
  intro e1 e2 hrel _ _
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  rcases hs : e1.stack.val with _ | ⟨word, rest⟩
  · simp only [extcodehashStep, popWord_of_nil hs,
      popWord_of_nil (evm := { e1 with state := s }) hs]
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  refine ⟨fun err h _ => ?_, fun a1 h reads => ?_⟩
  · rw [extcodehashStep_cons hs] at h
    rw [extcodehashStep_cons (evm := { e1 with state := s }) hs]
    by_cases berlin : fork ≥ .berlin <;>
      simp only [accessAddress, berlin, ↓reduceIte, Except.map] at h ⊢ <;> split at h <;> simp_all
  · have hacc := reads.account _ (by
      rw [(reads_extcodehashStep hs h).1]
      exact Std.ExtTreeSet.mem_insert_self)
    have hread := hrel.state.getAccount_eq (.inr hacc)
    have self := extcodehashStep_congr_state hs e1.state rfl
    rw [h] at self
    have hst : a1.state = e1.state.recordAccountRead (toAddressMasked word) :=
      congrArg Evm.state (Except.ok.inj self)
    rw [extcodehashStep_congr_state hs s hread, h]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [hst]
    exact hrel.state.recordAccountRead _

private theorem sloadStep_keeps :
    KeepsAgreement account allStorage slot code (sloadStep (fork := fork) (Meter := Meter)) := by
  intro e1 e2 hrel _ _
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  rcases hs : e1.stack.val with _ | ⟨word, rest⟩
  · simp only [sloadStep, popWord_of_nil hs, popWord_of_nil (evm := { e1 with state := s }) hs]
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  refine ⟨fun err h _ => ?_, fun a1 h reads => ?_⟩
  · rw [sloadStep_cons hs] at h
    rw [sloadStep_cons (evm := { e1 with state := s }) hs]
    by_cases berlin : fork ≥ .berlin <;>
      simp only [accessStorageKey, berlin, ↓reduceIte, Except.map] at h ⊢ <;> split at h <;>
      simp_all
  · have hslot := reads.slot e1.message.currentTarget (U256.toBeBytes word) (by
      rw [(reads_sloadStep hs h).2, Std.ExtTreeMap.getD_insert_self]
      exact Std.ExtTreeSet.mem_insert_self)
    have hread := hrel.state.getStorage_eq (.inr (.inr (.inr hslot)))
    have self := sloadStep_congr_state hs e1.state rfl
    rw [h] at self
    have hst : a1.state =
        e1.state.recordStorageRead e1.message.currentTarget (U256.toBeBytes word) :=
      congrArg Evm.state (Except.ok.inj self)
    rw [sloadStep_congr_state hs s hread, h]
    refine ⟨_, rfl, rfl, ?_⟩
    rw [hst]
    exact hrel.state.recordStorageRead _ _

omit [GasMeter Meter] in
private theorem keepsAgreement_of_eq_map {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {e1 : Evm fork Meter} {other after : State.TransactionState}
    (heq : run { e1 with state := other } = (fun a => { a with state := after }) <$> run e1)
    (hstate : ∀ a1, run e1 = .ok a1 → ReadsIn account slot a1.state →
      AgreesOn account allStorage slot code a1.state after) :
    (∀ err, run e1 = .error err → err.aborts = false →
        run { e1 with state := other } = .error err) ∧
      ∀ a1, run e1 = .ok a1 → ReadsIn account slot a1.state →
        ∃ a2, run { e1 with state := other } = .ok a2 ∧
          FrameAgrees account allStorage slot code a1 a2 := by
  rw [heq]
  exact ⟨fun err h _ => by rw [h]; rfl,
    fun a1 h reads => ⟨_, by rw [h]; rfl, rfl, hstate a1 h reads⟩⟩

private theorem tloadStep_keeps :
    KeepsAgreement account allStorage slot code (tloadStep (fork := fork) (Meter := Meter)) := by
  intro e1 e2 hrel _ _
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  rcases hs : e1.stack.val with _ | ⟨word, rest⟩
  · simp only [tloadStep, popWord_of_nil hs, popWord_of_nil (evm := { e1 with state := s }) hs]
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  refine keepsAgreement_of_eq_map (after := s) ?_ fun a1 h _ => ?_
  · rw [tloadStep_cons hs, tloadStep_cons (evm := { e1 with state := s }) hs]
    simp only [hrel.state.getTransientStorage_eq]
    cases GasMeter.charge e1.gas GasCosts.OPCODE_TLOAD <;> rfl
  · rw [(tloadStep_sameContext h).state]
    exact hrel.state

private theorem tstoreStep_keeps :
    KeepsAgreement account allStorage slot code (tstoreStep (fork := fork) (Meter := Meter)) := by
  intro e1 e2 hrel _ _
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  rcases hs : e1.stack.val with _ | ⟨word, _ | ⟨value, rest⟩⟩
  · simp only [tstoreStep, popWord_of_nil hs, popWord_of_nil (evm := { e1 with state := s }) hs]
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  · have hstack : e1.stack = ⟨[word], hs ▸ e1.stack.property⟩ := Subtype.ext hs
    have h1 : ∀ s', tstoreStep { e1 with state := s' } = .error .stackUnderflow := fun s' => by
      simp [tstoreStep, popWord, hstack, Stack.pop, bind, Except.bind, pure, Except.pure]
    rw [show tstoreStep e1 = .error .stackUnderflow from h1 e1.state, h1 s]
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  · have hstack : e1.stack = ⟨word :: value :: rest, hs ▸ e1.stack.property⟩ := Subtype.ext hs
    have heq : ∀ s', tstoreStep { e1 with state := s' } =
        (fun a => { a with state :=
          s'.setTransientStorage e1.message.currentTarget (U256.toBeBytes word) value }) <$>
          tstoreStep e1 := fun s' => by
      simp only [tstoreStep, popWord, chargeGas, advance, hstack, Stack.pop, bind, Except.bind,
        pure, Except.pure]
      cases GasMeter.charge e1.gas GasCosts.OPCODE_TSTORE <;> simp only [] <;> (try split) <;> rfl
    refine keepsAgreement_of_eq_map (heq s) fun a1 h _ => ?_
    have self := heq e1.state
    rw [h] at self
    have hst : a1.state =
        e1.state.setTransientStorage e1.message.currentTarget (U256.toBeBytes word) value :=
      congrArg Evm.state (Except.ok.inj self)
    rw [hst]
    exact hrel.state.setTransientStorage _ _ _

private theorem selfbalance_keeps :
    KeepsAgreement account allStorage slot code (fun evm : Evm fork Meter =>
      readFrame GasCosts.OPCODE_SELFBALANCE
        (fun evm => (evm.state.getAccount evm.message.currentTarget).balance)
        (recordAccountRead evm evm.message.currentTarget)) := by
  intro e1 e2 hrel _ hcurrent
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  have heq : ∀ s', s'.getAccount e1.message.currentTarget =
      e1.state.getAccount e1.message.currentTarget →
      readFrame GasCosts.OPCODE_SELFBALANCE
          (fun evm => (evm.state.getAccount evm.message.currentTarget).balance)
          (recordAccountRead { e1 with state := s' } e1.message.currentTarget) =
        (fun a => { a with state := s'.recordAccountRead e1.message.currentTarget }) <$>
          readFrame GasCosts.OPCODE_SELFBALANCE
            (fun evm => (evm.state.getAccount evm.message.currentTarget).balance)
            (recordAccountRead e1 e1.message.currentTarget) := by
    intro s' hs'
    simp only [readFrame, recordAccountRead, chargeGas, pushWord, advance, bind, Except.bind,
      pure, Except.pure]
    cases GasMeter.charge e1.gas GasCosts.OPCODE_SELFBALANCE
    · rfl
    · dsimp only
      simp only [State.TransactionState.getAccount_recordAccountRead, hs']
      cases e1.stack.push (e1.state.getAccount e1.message.currentTarget).balance <;> rfl
  refine keepsAgreement_of_eq_map (heq s (hrel.state.getAccount_eq (.inr hcurrent)))
    fun a1 h _ => ?_
  have self := heq e1.state rfl
  rw [h] at self
  have hst : a1.state = e1.state.recordAccountRead e1.message.currentTarget :=
    congrArg Evm.state (Except.ok.inj self)
  rw [hst]
  exact hrel.state.recordAccountRead _

private theorem extcodesizeStep_keeps :
    KeepsAgreement account allStorage slot code
      (extcodesizeStep (fork := fork) (Meter := Meter)) := by
  intro e1 e2 hrel hcodes _
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  rcases hs : e1.stack.val with _ | ⟨word, rest⟩
  · simp only [extcodesizeStep, popWord_of_nil hs,
      popWord_of_nil (evm := { e1 with state := s }) hs]
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  have hstack : e1.stack = ⟨word :: rest, hs ▸ e1.stack.property⟩ := Subtype.ext hs
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := e1.stack.property
    rw [hs] at this
    simp only [List.length_cons] at this
    omega
  by_cases berlin : fork ≥ .berlin <;>
    simp only [extcodesizeStep, popWord, hstack, Stack.pop, accessAddress, berlin, ↓reduceIte,
      chargeGas, recordAccountRead, accountCode, pushWord, advance, bind, Except.bind, pure,
      Except.pure, Stack.push, State.TransactionState.getCode_recordAccountRead,
      State.TransactionState.getAccount_recordAccountRead]
  all_goals first
    | (have _ : fork ≥ .berlin := berlin
       generalize GasMeter.charge e1.gas (externalBaseCost fork
         (decide ¬Base.toAddressMasked word ∈ e1.substate.accessedAddresses)) = c)
    | generalize GasMeter.charge e1.gas (externalBaseCost fork false) = c
  all_goals
    cases c with
    | error e => exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
    | ok g =>
      dsimp only
      rcases hcode : e1.state.getCode
          (e1.state.getAccount (Base.toAddressMasked word)).codeHash with e | bytes
      · simp only [Except.mapError]
        refine ⟨fun err h nab => ?_, fun a1 h _ => by cases h⟩
        cases h
        simp [EvmError.aborts] at nab
      · refine ⟨fun err h _ => ?_, fun a1 h reads => ?_⟩
        · simp [Except.mapError, room] at h
        · simp [Except.mapError, room] at h
          have ha := reads.account (Base.toAddressMasked word)
            (by simp [← h, State.TransactionState.recordAccountRead])
          have hacc := hrel.state.getAccount_eq (.inr ha)
          have hc := hrel.state.getCode_eq (hcodes _ ha)
          refine ⟨{ a1 with state := s.recordAccountRead (Base.toAddressMasked word) }, ?_, rfl,
            ?_⟩
          · simp [← h, hacc, hc, hcode, Except.mapError, room]
          · rw [← h]
            exact hrel.state.recordAccountRead _

omit [GasMeter Meter] in
private theorem keeps_of_error {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {e1 : Evm fork Meter} {other : State.TransactionState} {error : EvmError}
    (h : ∀ s, run { e1 with state := s } = .error error) :
    (∀ err, run e1 = .error err → err.aborts = false →
        run { e1 with state := other } = .error err) ∧
      ∀ a1, run e1 = .ok a1 → ReadsIn account slot a1.state →
        ∃ a2, run { e1 with state := other } = .ok a2 ∧
          FrameAgrees account allStorage slot code a1 a2 := by
  have h1 : run e1 = .error error := h e1.state
  rw [h1, h other]
  exact ⟨fun _ h _ => h, fun _ h => by cases h⟩

private theorem extcodecopyStep_keeps :
    KeepsAgreement account allStorage slot code
      (extcodecopyStep (fork := fork) (Meter := Meter)) := by
  intro e1 e2 hrel hcodes _
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  rcases hs : e1.stack.val with _ | ⟨word, _ | ⟨start, _ | ⟨offset, _ | ⟨size, rest⟩⟩⟩⟩
  all_goals have hstack := Subtype.ext (a2 := ⟨_, hs ▸ e1.stack.property⟩) hs
  iterate 4
    exact keeps_of_error (error := .stackUnderflow) fun s' => by
      simp [extcodecopyStep, popWord, hstack, Stack.pop, bind, Except.bind, pure, Except.pure]
  by_cases berlin : fork ≥ .berlin <;>
    simp only [extcodecopyStep, popWord, hstack, Stack.pop, accessAddress, berlin, ↓reduceIte,
      chargeGasAndMemory, chargeGas, recordAccountRead, accountCode, advance, bind, Except.bind,
      pure, Except.pure, State.TransactionState.getCode_recordAccountRead,
      State.TransactionState.getAccount_recordAccountRead]
  all_goals first
    | (have _ : fork ≥ .berlin := berlin
       generalize GasMeter.charge e1.gas (externalBaseCost fork
         (decide ¬Base.toAddressMasked word ∈ e1.substate.accessedAddresses) +
           GasCosts.OPCODE_COPY_PER_WORD * wordCount size.toNat +
           (extendMemory e1.memory.size [(start, size)]).cost) = c)
    | generalize GasMeter.charge e1.gas (externalBaseCost fork false +
           GasCosts.OPCODE_COPY_PER_WORD * wordCount size.toNat +
           (extendMemory e1.memory.size [(start, size)]).cost) = c
  all_goals
    cases c with
    | error e => exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
    | ok g =>
      dsimp only
      rcases hcode : e1.state.getCode
          (e1.state.getAccount (Base.toAddressMasked word)).codeHash with e | bytes
      · simp only [Except.mapError]
        refine ⟨fun err h nab => ?_, fun a1 h _ => by cases h⟩
        cases h
        simp [EvmError.aborts] at nab
      · refine ⟨fun err h _ => ?_, fun a1 h reads => ?_⟩
        · simp [Except.mapError] at h
        · simp [Except.mapError] at h
          have ha := reads.account (Base.toAddressMasked word)
            (by simp [← h, State.TransactionState.recordAccountRead])
          have hacc := hrel.state.getAccount_eq (.inr ha)
          have hc := hrel.state.getCode_eq (hcodes _ ha)
          refine ⟨{ a1 with state := s.recordAccountRead (Base.toAddressMasked word) }, ?_, rfl,
            ?_⟩
          · simp [← h, hacc, hc, hcode, Except.mapError]
          · rw [← h]
            exact hrel.state.recordAccountRead _

/-- The write of SSTORE once it has read its slot: refill, pay, check the frame, write. -/
private def sstoreWrite (address : Address) (key : Bytes32) (original current new : U256)
    (cold : Bool) (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let evm := refillStateGas evm (sstoreStateRefill fork original current new)
  let evm ← chargeGas evm (sstoreCost fork original current new cold)
  let evm ← chargeStateGas evm (sstoreStateGas fork original current new)
  if evm.message.isStatic then
    throw .writeInStaticContext
  else
    let state ← (evm.state.setStorage address key new).mapError .state
    let refundCounter := evm.substate.refundCounter + sstoreRefund fork original current new
    return advance { evm with state, substate := { evm.substate with refundCounter } }

/-- The rest of SSTORE once it has popped its key and its word, and passed the gas check. -/
private def sstoreRest (word new : U256) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) :=
  let key := U256.toBeBytes word
  let address := evm.message.currentTarget
  let original := evm.state.getStorageOriginal address key
  let current := evm.state.getStorage address key
  let (cold, evm) := accessStorageKey evm address key
  let evm := recordStorageRead evm address key
  keepReads evm id (sstoreWrite address key original current new cold evm)

omit [GasMeter Meter] in
private theorem ok_bind {α β : Type} (x : α) (k : α → Except EvmError β) :
    (Except.ok x >>= k) = k x := rfl

omit [GasMeter Meter] in
private theorem map_ok {α β : Type} (f : α → β) (x : α) :
    (f <$> (Except.ok x : Except EvmError α)) = Except.ok (f x) := rfl

omit [GasMeter Meter] in
private theorem popWord_cons {evm : Evm fork Meter} {x : U256} {rest : List U256}
    (h : evm.stack.val = x :: rest) :
    ∃ after, popWord evm = .ok (x, after) ∧ after.stack.val = rest ∧ after.gas = evm.gas := by
  have hstack := Subtype.ext (a2 := ⟨_, h ▸ evm.stack.property⟩) h
  refine ⟨{ evm with stack := ⟨rest, ?_⟩ }, ?_, rfl, rfl⟩
  · have := evm.stack.property
    rw [h, List.length_cons] at this
    omega
  · simp [popWord, hstack, Stack.pop, bind, Except.bind, pure, Except.pure]

private theorem chargeStateGas_withState (evm : Evm fork Meter) (other : State.TransactionState)
    (amount : Nat) :
    chargeStateGas { evm with state := other } amount =
      (fun after => { after with state := other }) <$> chargeStateGas evm amount := by
  simp only [chargeStateGas]
  cases GasMeter.chargeState evm.gas amount <;> rfl

private theorem sstoreWrite_keeps {address : Address} {key : Bytes32} {original current new : U256}
    {cold : Bool} {evm : Evm fork Meter} {other : State.TransactionState}
    (hag : AgreesOn account allStorage slot code evm.state other)
    (ha : address ∈ evm.state.accountWrites ∨ account address) :
    (∀ err, sstoreWrite address key original current new cold evm = .error err →
        err.aborts = false →
        sstoreWrite address key original current new cold { evm with state := other } =
          .error err) ∧
      ∀ a1, sstoreWrite address key original current new cold evm = .ok a1 →
        ∃ a2, sstoreWrite address key original current new cold { evm with state := other } =
          .ok a2 ∧ FrameAgrees account allStorage slot code a1 a2 := by
  have hrefill : refillStateGas { evm with state := other }
      (sstoreStateRefill fork original current new) =
      { refillStateGas evm (sstoreStateRefill fork original current new) with state := other } :=
    rfl
  simp only [sstoreWrite, hrefill, chargeGas_withState, chargeStateGas_withState, bind_map_left]
  rcases h4 : chargeGas (refillStateGas evm (sstoreStateRefill fork original current new))
      (sstoreCost fork original current new cold) with e | f4
  · exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  have s4 : f4.state = evm.state := (chargeGas_sameContext h4).state
  simp only [ok_bind]
  rcases h5 : chargeStateGas f4 (sstoreStateGas fork original current new) with e | f5
  · exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  have s5 : f5.state = evm.state := (chargeStateGas_sameContext h5).state.trans s4
  simp only [ok_bind]
  by_cases static : f5.message.isStatic = true
  · simp only [static, ↓reduceIte]
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  simp only [static, s5, Bool.false_eq_true, ↓reduceIte]
  have hset := hag.setStorage ha key new
  rcases hs1 : evm.state.setStorage address key new with e | st1 <;>
    rcases hs2 : other.setStorage address key new with e' | st2 <;>
    rw [hs1, hs2] at hset <;> simp only [Base.ExceptRel] at hset
  · subst hset
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  · simp only [Except.mapError, ok_bind, pure, Except.pure]
    refine ⟨fun _ h _ => (by cases h), fun a1 h => ?_⟩
    cases h
    exact ⟨_, rfl, rfl, hset⟩

omit [GasMeter Meter] in
private theorem accessStorageKey_withState (evm : Evm fork Meter)
    (other : State.TransactionState) (address : Address) (key : Bytes32) :
    accessStorageKey { evm with state := other } address key =
      ((accessStorageKey evm address key).1,
        { (accessStorageKey evm address key).2 with state := other }) := by
  unfold accessStorageKey
  split <;> rfl

private theorem sstoreRest_error {word new : U256} {evm : Evm fork Meter} {err : EvmError}
    (h : sstoreRest word new evm = .error err) : err.aborts = true :=
  (keepReads_eq_error.mp h).2

private theorem keepReads_keeps {evm a1 : Evm fork Meter} {other : State.TransactionState}
    {x y : Except EvmError (Evm fork Meter)}
    (hag : AgreesOn account allStorage slot code evm.state other)
    (herr : ∀ err, x = .error err → err.aborts = false → y = .error err)
    (hok : ∀ a1, x = .ok a1 → ∃ a2, y = .ok a2 ∧ FrameAgrees account allStorage slot code a1 a2)
    (h : keepReads evm id x = .ok a1) :
    ∃ a2, keepReads { evm with state := other } id y = .ok a2 ∧
      FrameAgrees account allStorage slot code a1 a2 := by
  unfold keepReads at h ⊢
  rcases hx : x with e | r
  · rw [hx] at h
    by_cases hab : e.aborts = true
    · simp [hab] at h
    · simp only [hab] at h
      cases h
      rw [herr e hx (by simpa using hab)]
      exact ⟨exceptionalHalt { evm with state := other } e, by simp [hab], rfl, hag⟩
  · rw [hx] at h
    cases h
    obtain ⟨a2, hy, hfa⟩ := hok _ hx
    rw [hy]
    exact ⟨a2, rfl, hfa⟩

private theorem sstoreRest_ok {word new : U256} {evm a1 : Evm fork Meter}
    {other : State.TransactionState}
    (hag : AgreesOn account allStorage slot code evm.state other)
    (hcurrent : account evm.message.currentTarget)
    (hslot : slot evm.message.currentTarget (U256.toBeBytes word))
    (h : sstoreRest word new evm = .ok a1) :
    ∃ a2, sstoreRest word new { evm with state := other } = .ok a2 ∧
      FrameAgrees account allStorage slot code a1 a2 := by
  have horig := hag.getStorageOriginal_eq (.inr (.inr hslot))
  have hcur := hag.getStorage_eq (.inr (.inr (.inr hslot)))
  simp only [sstoreRest] at h ⊢
  simp only [horig, hcur, accessStorageKey_withState]
  rcases hacc : accessStorageKey evm evm.message.currentTarget (U256.toBeBytes word) with
    ⟨cold, g⟩
  simp only [hacc] at h ⊢
  have sg : g.state = evm.state := by
    have := state_accessStorageKey evm evm.message.currentTarget (U256.toBeBytes word)
    rwa [hacc] at this
  have hagE : AgreesOn account allStorage slot code
      (recordStorageRead g evm.message.currentTarget (U256.toBeBytes word)).state
      (other.recordStorageRead evm.message.currentTarget (U256.toBeBytes word)) := by
    simp only [recordStorageRead, sg]
    exact hag.recordStorageRead _ _
  obtain ⟨herr, hok⟩ := sstoreWrite_keeps (original :=
    evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes word))
    (current := evm.state.getStorage evm.message.currentTarget (U256.toBeBytes word))
    (new := new) (cold := cold) (key := U256.toBeBytes word) hagE (.inr hcurrent)
  have hrec : recordStorageRead { g with state := other } evm.message.currentTarget
      (U256.toBeBytes word) =
      { recordStorageRead g evm.message.currentTarget (U256.toBeBytes word) with
        state := other.recordStorageRead evm.message.currentTarget (U256.toBeBytes word) } := rfl
  rw [hrec]
  exact keepReads_keeps hagE herr hok h

private theorem sstoreStep_eq (evm : Evm fork Meter) : sstoreStep evm = (do
    if fork ≥ .glamsterdam ∧ evm.message.isStatic then throw .writeInStaticContext
    let (word, evm) ← popWord evm
    let (new, evm) ← popWord evm
    if fork ≥ .istanbul ∧ GasMeter.gasLeft evm.gas ≤ GasCosts.CALL_STIPEND then
      throw .outOfGas
    else sstoreRest word new evm) := rfl

private theorem sstoreStep_keeps :
    KeepsAgreement account allStorage slot code (sstoreStep (fork := fork) (Meter := Meter)) := by
  intro e1 e2 hrel _ hcurrent
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  by_cases static : fork ≥ .glamsterdam ∧ e1.message.isStatic = true
  · exact keeps_of_error (error := .writeInStaticContext) fun s' => by
      simp [sstoreStep, static, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  rcases hs : e1.stack.val with _ | ⟨word, _ | ⟨new, rest⟩⟩
  all_goals have hstack := Subtype.ext (a2 := ⟨_, hs ▸ e1.stack.property⟩) hs
  iterate 2
    exact keeps_of_error (error := .stackUnderflow) fun s' => by
      simp [sstoreStep, static, popWord, hstack, Stack.pop, bind, Except.bind, pure, Except.pure]
  by_cases stipend : fork ≥ .istanbul ∧ GasMeter.gasLeft e1.gas ≤ GasCosts.CALL_STIPEND
  · exact keeps_of_error (error := .outOfGas) fun s' => by
      simp [sstoreStep, static, stipend, popWord, hstack, Stack.pop, bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw]
  obtain ⟨f1, hp1, hs1, g1⟩ := popWord_cons hs
  obtain ⟨f2, hp2, -, g2⟩ := popWord_cons hs1
  have c2 := (popWord_sameContext hp1).trans (popWord_sameContext hp2)
  have stipend' : ¬(fork ≥ .istanbul ∧ GasMeter.gasLeft f2.gas ≤ GasCosts.CALL_STIPEND) := by
    rwa [g2, g1]
  have k1 : sstoreStep e1 = sstoreRest word new f2 := by
    rw [sstoreStep_eq]
    simp only [static, ↓reduceIte, hp1, hp2, stipend', ok_bind]
  have k2 : sstoreStep { e1 with state := s } = sstoreRest word new { f2 with state := s } := by
    rw [sstoreStep_eq]
    simp only [static, ↓reduceIte, popWord_withState, hp1, hp2, map_ok, stipend', ok_bind]
  refine ⟨fun err h nab => ?_, fun a1 h reads => ?_⟩
  · rw [k1] at h
    rw [sstoreRest_error h] at nab
    cases nab
  · have hslot := reads.slot _ _ (mem_storageReads_sstoreStep hs h)
    rw [k1] at h
    rw [k2]
    refine sstoreRest_ok (by rw [c2.state]; exact hrel.state) ?_ ?_ h
    · rw [c2.message]
      exact hcurrent
    · rw [c2.message]
      exact hslot

private theorem selfdestructTransfer_agrees {tx other : State.TransactionState}
    (hag : AgreesOn account allStorage slot code tx other) {originator beneficiary : Address}
    (ho : account originator) (hb : account beneficiary) :
    State.TransactionState.AgreesOnExcept account allStorage slot code
      (selfdestructTransfer fork tx originator beneficiary)
      (selfdestructTransfer fork other originator beneficiary) := by
  unfold selfdestructTransfer
  rw [hag.getAccount_eq (.inr ho)]
  split
  · refine (hag.moveEther fork (.inr ho) (.inr hb) _).bind fun hmid _ _ => ?_
    rw [hmid.tracker.createdAccounts]
    split
    · exact hmid.setAccountBalance fork (.inr ho) 0
    · exact hmid
  · exact (hag.createEther fork (.inr hb) _).bind fun hmid _ _ =>
      hmid.setAccountBalance fork (.inr ho) 0

omit [GasMeter Meter] in
private theorem finishSelfdestruct_keeps {beneficiary : Address} {refund : Nat}
    {evm : Evm fork Meter} {other : State.TransactionState}
    (hag : AgreesOn account allStorage slot code evm.state other)
    (ho : account evm.message.currentTarget) (hb : account beneficiary) :
    (∀ err, finishSelfdestruct fork beneficiary refund evm = .error err →
        finishSelfdestruct fork beneficiary refund { evm with state := other } = .error err) ∧
      ∀ a1, finishSelfdestruct fork beneficiary refund evm = .ok a1 →
        ∃ a2, finishSelfdestruct fork beneficiary refund { evm with state := other } = .ok a2 ∧
          FrameAgrees account allStorage slot code a1 a2 := by
  unfold finishSelfdestruct
  by_cases static : evm.message.isStatic = true
  · simp only [static, ↓reduceIte]
    exact ⟨fun _ h => h, fun _ h => by cases h⟩
  simp only [static, Bool.false_eq_true, ↓reduceIte, hag.getAccount_eq (.inr ho)]
  have ht := selfdestructTransfer_agrees (fork := fork) hag ho hb
  rcases ht1 : selfdestructTransfer fork evm.state evm.message.currentTarget beneficiary with
      e | st1 <;>
    rcases ht2 : selfdestructTransfer fork other evm.message.currentTarget beneficiary with
      e' | st2 <;>
    rw [ht1, ht2] at ht <;> simp only [Base.ExceptRel] at ht
  · subst ht
    exact ⟨fun _ h => h, fun _ h => by cases h⟩
  · simp only [Except.mapError, ok_bind, pure, Except.pure]
    refine ⟨fun _ h => (by cases h), fun a1 h => ?_⟩
    cases h
    rw [ht.tracker.createdAccounts, ht.accountExistsAndIsEmpty_eq (.inr hb)]
    exact ⟨_, rfl, rfl, ht⟩

/-- The rest of SELFDESTRUCT once it has read its beneficiary: price, pay, then finish. -/
private def selfdestructWrite (beneficiary : Address) (cold : Bool) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  let originator := evm.message.currentTarget
  let createsAccount := selfdestructCreatesAccount fork evm.state originator beneficiary
  let refund :=
    if originator ∈ evm.substate.accountsToDelete then 0
    else (gasSchedule fork).REFUND_SELF_DESTRUCT
  let evm ← chargeGas evm (selfdestructCost fork cold createsAccount)
  let evm ← chargeStateGas evm (selfdestructStateGas fork createsAccount)
  finishSelfdestruct fork beneficiary refund evm

private theorem selfdestructStep_eq (evm : Evm fork Meter) : selfdestructStep fork evm = (do
    if fork ≥ .glamsterdam ∧ evm.message.isStatic then throw .writeInStaticContext
    let (word, evm) ← popWord evm
    let (cold, evm) := accessAddress evm (toAddressMasked word)
    checkGas evm (selfdestructCost fork cold false)
    let evm := recordAccountRead evm (toAddressMasked word)
    keepReads evm id (selfdestructWrite (toAddressMasked word) cold evm)) := rfl

private theorem selfdestructWrite_keeps {beneficiary : Address} {cold : Bool}
    {evm : Evm fork Meter} {other : State.TransactionState}
    (hag : AgreesOn account allStorage slot code evm.state other)
    (ho : account evm.message.currentTarget) (hb : account beneficiary) :
    (∀ err, selfdestructWrite beneficiary cold evm = .error err →
        selfdestructWrite beneficiary cold { evm with state := other } = .error err) ∧
      ∀ a1, selfdestructWrite beneficiary cold evm = .ok a1 →
        ∃ a2, selfdestructWrite beneficiary cold { evm with state := other } = .ok a2 ∧
          FrameAgrees account allStorage slot code a1 a2 := by
  have hcreates : selfdestructCreatesAccount fork other evm.message.currentTarget beneficiary =
      selfdestructCreatesAccount fork evm.state evm.message.currentTarget beneficiary := by
    unfold selfdestructCreatesAccount
    rw [hag.isAccountAlive_eq (.inr hb), hag.getAccount_eq (.inr ho),
      hag.accountExists_eq (.inr hb)]
  simp only [selfdestructWrite, hcreates, chargeGas_withState, chargeStateGas_withState,
    bind_map_left]
  rcases h4 : chargeGas evm (selfdestructCost fork cold
      (selfdestructCreatesAccount fork evm.state evm.message.currentTarget beneficiary)) with
    e | f4
  · exact ⟨fun _ h => h, fun _ h => by cases h⟩
  simp only [ok_bind]
  rcases h5 : chargeStateGas f4 (selfdestructStateGas fork
      (selfdestructCreatesAccount fork evm.state evm.message.currentTarget beneficiary)) with
    e | f5
  · exact ⟨fun _ h => h, fun _ h => by cases h⟩
  simp only [ok_bind]
  have c5 := (chargeGas_sameContext h4).trans (chargeStateGas_sameContext h5)
  exact finishSelfdestruct_keeps (by rw [c5.state]; exact hag) (by rw [c5.message]; exact ho) hb

omit [GasMeter Meter] in
private theorem accessAddress_withState (evm : Evm fork Meter)
    (other : State.TransactionState) (address : Address) :
    accessAddress { evm with state := other } address =
      ((accessAddress evm address).1, { (accessAddress evm address).2 with state := other }) := by
  unfold accessAddress
  split <;> rfl

private theorem selfdestructStep_keeps :
    KeepsAgreement account allStorage slot code (selfdestructStep (Meter := Meter) fork) := by
  intro e1 e2 hrel _ hcurrent
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  by_cases static : fork ≥ .glamsterdam ∧ e1.message.isStatic = true
  · exact keeps_of_error (error := .writeInStaticContext) fun s' => by
      simp [selfdestructStep, static, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  rcases hs : e1.stack.val with _ | ⟨word, rest⟩
  · exact keeps_of_error (error := .stackUnderflow) fun s' => by
      simp [selfdestructStep_eq, static, popWord_of_nil (evm := { e1 with state := s' }) hs,
        bind, Except.bind]
  obtain ⟨f1, hp1, -, -⟩ := popWord_cons hs
  rcases hacc : accessAddress f1 (toAddressMasked word) with ⟨cold, g⟩
  have sg : g.state = e1.state ∧ g.message = e1.message := by
    obtain ⟨_, hg⟩ := accessAddress_snd f1 (toAddressMasked word)
    rw [hacc] at hg
    simp only at hg
    rw [hg]
    exact ⟨(popWord_sameContext hp1).state, (popWord_sameContext hp1).message⟩
  have hacc2 : accessAddress { f1 with state := s } (toAddressMasked word) =
      (cold, { g with state := s }) := by
    rw [accessAddress_withState, hacc]
  rcases hcheck : checkGas g (selfdestructCost fork cold false) with e | ⟨⟩
  · exact keeps_of_error (error := e) fun s' => by
      have hcheck2 : checkGas { g with state := s' } (selfdestructCost fork cold false) =
          .error e := hcheck
      rw [selfdestructStep_eq]
      simp only [static, ↓reduceIte, popWord_withState, hp1, map_ok, ok_bind,
        accessAddress_withState, hacc, hcheck2]
      rfl
  have hcheck2 : checkGas { g with state := s } (selfdestructCost fork cold false) = .ok () :=
    hcheck
  have k1 : selfdestructStep fork e1 = keepReads (recordAccountRead g (toAddressMasked word)) id
      (selfdestructWrite (toAddressMasked word) cold
        (recordAccountRead g (toAddressMasked word))) := by
    rw [selfdestructStep_eq]
    simp only [static, ↓reduceIte, hp1, ok_bind, hacc, hcheck]
  have k2 : selfdestructStep fork { e1 with state := s } =
      keepReads { recordAccountRead g (toAddressMasked word) with
          state := s.recordAccountRead (toAddressMasked word) } id
        (selfdestructWrite (toAddressMasked word) cold
          { recordAccountRead g (toAddressMasked word) with
            state := s.recordAccountRead (toAddressMasked word) }) := by
    rw [selfdestructStep_eq]
    simp only [static, ↓reduceIte, popWord_withState, hp1, map_ok, ok_bind,
      accessAddress_withState, hacc, hcheck2]
    rfl
  refine ⟨fun err h nab => ?_, fun a1 h reads => ?_⟩
  · rw [k1] at h
    rw [(keepReads_eq_error.mp h).2] at nab
    cases nab
  · have hb : account (toAddressMasked word) := by
      refine reads.account _ ?_
      rcases accountReads_selfdestructStep hs h with ⟨ha, -⟩ | ha <;> rw [ha] <;>
        simp [Std.ExtTreeSet.mem_insert]
    rw [k1] at h
    rw [k2]
    have hag : AgreesOn account allStorage slot code
        (recordAccountRead g (toAddressMasked word)).state
        (s.recordAccountRead (toAddressMasked word)) := by
      simp only [recordAccountRead, sg.1]
      exact hrel.state.recordAccountRead _
    obtain ⟨herr, hok⟩ := selfdestructWrite_keeps (cold := cold) hag
      (by simp only [recordAccountRead, sg.2]; exact hcurrent) hb
    exact keepReads_keeps hag (fun err h _ => herr err h) hok h

private theorem accountStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some run) : KeepsAgreement account allStorage slot code run := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | with_reducible exact balanceStep_keeps
    | with_reducible exact selfbalance_keeps
    | with_reducible exact extcodesizeStep_keeps
    | with_reducible exact extcodecopyStep_keeps
    | with_reducible exact extcodehashStep_keeps

private theorem storageStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some run) : KeepsAgreement account allStorage slot code run := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep
  · exact sloadStep_keeps
  · exact sstoreStep_keeps

private theorem transientStorageStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some run) :
    KeepsAgreement account allStorage slot code run := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep
  · exact tloadStep_keeps
  · exact tstoreStep_keeps

private theorem selfdestructOpStep_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some run) :
    KeepsAgreement account allStorage slot code run := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact selfdestructStep_keeps

private theorem instruction_keeps {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : instruction fork op = some run) : KeepsAgreement account allStorage slot code run := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact keepsAgreement_of_stateFree (stackOnlyStep_stateFree hf)
      fun h => (stackOnlyStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · exact keepsAgreement_of_stateFree (controlFlowStep_stateFree hf)
      fun h => (controlFlowStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · exact keepsAgreement_of_stateFree (memoryDataStep_stateFree hf)
      fun h => (memoryDataStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · refine keepsAgreement_of_stateFree (returnOpStep_stateFree hf) fun h => ?_
    cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hf
    · subst hf
      exact (returnStep_sameContext h).state
    · split at hf
      · cases hf
        exact (revertStep_sameContext h).state
      · cases hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact keepsAgreement_of_stateFree (environmentStep_stateFree hf)
      fun h => (environmentStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · exact accountStep_keeps hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact storageStep_keeps hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact transientStorageStep_keeps hf
  rcases orElse_eq_some hrun with hf | hf
  · refine keepsAgreement_of_stateFree (logOpStep_stateFree hf) fun h => ?_
    cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, -, -, hs, -⟩ := logStep_eq_ok h
    exact hs
  · exact selfdestructOpStep_keeps hf

/-- Each instruction of the dispatch gives agreeing frames when it starts from agreeing frames.

A failure that does not abort the run comes before any read, so both frames fail alike.

A success needs the reads of the frame it gives in the sets.

Each account of the first set needs its code hash empty, written, or in the code set.

The current account must be in the first set.

SELFDESTRUCT reads its balance to price a new account. -/
theorem instruction_agrees {account allStorage : Address → Prop}
    {slot : Address → Bytes32 → Prop} {code : Hash32 → Prop} {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : instruction fork op = some run) {e1 e2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code e1 e2)
    (hcodes : CodesIn account code e1.state) (hcurrent : account e1.message.currentTarget) :
    (∀ err, run e1 = .error err → err.aborts = false → run e2 = .error err) ∧
      ∀ a1, run e1 = .ok a1 → ReadsIn account slot a1.state →
        ∃ a2, run e2 = .ok a2 ∧ FrameAgrees account allStorage slot code a1 a2 :=
  instruction_keeps hrun e1 e2 hrel hcodes hcurrent

end EthLib.Execution.Evm
