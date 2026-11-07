module

public import EthLib.Execution.Evm.Instructions.TransientStorage
public import EthLib.Execution.Proofs.Evm.Step
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: `Evm.Instructions.TransientStorage`

After TSTORE, the transient word at its key is the word it wrote.

So a TLOAD of that key in the same frame reads it back.

TSTORE never succeeds in a static frame.

TLOAD pays its price.

Then it puts the transient word of the current account at the key in place of the key.

TLOAD and TSTORE exist exactly from Dencun, and keep memory.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- TLOAD on a key: pay, then put the transient word at the key in its place. -/
theorem tloadStep_cons {evm : Evm fork Meter} {word : U256} {rest : List U256}
    (h : evm.stack.val = word :: rest) :
    tloadStep evm = (GasMeter.charge evm.gas OPCODE_TLOAD).map fun gas =>
      { evm with
        stack := ⟨evm.state.getTransientStorage evm.message.currentTarget (U256.toBeBytes word) ::
            rest, length_cons_le (dropped := [word]) h (by simp)⟩,
        gas, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨word :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := length_cons_le (x := word) (dropped := [word]) h (by simp)
    simp only [List.length_cons] at this
    omega
  simp only [tloadStep, popWord, chargeGas, pushWord, advance, hstack, Stack.pop, Stack.push]
  rcases hc : GasMeter.charge evm.gas OPCODE_TLOAD with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, room]

/-- After TSTORE of `value` at `key`, the transient storage holds `value` at `key`. -/
theorem tstoreStep_getTransientStorage {evm after : Evm fork Meter} {key value : U256}
    {rest : List U256} (hs : evm.stack.val = key :: value :: rest)
    (h : tstoreStep evm = .ok after) :
    after.state.getTransientStorage evm.message.currentTarget (U256.toBeBytes key) = value := by
  have hstack : evm.stack = ⟨key :: value :: rest, hs ▸ evm.stack.property⟩ := Subtype.ext hs
  simp only [tstoreStep, popWord, hstack, Stack.pop, bind, Except.bind, pure, Except.pure] at h
  obtain ⟨e, hc, h⟩ := Base.bind_ok_iff.mp h
  have := chargeGas_sameContext hc
  split at h
  · cases h
  · cases h
    simp only [advance, this.message, this.state]
    exact State.TransactionState.getTransientStorage_setTransientStorage_self _ _ _ _

/-- TSTORE never succeeds in a static frame. -/
theorem tstoreStep_ne_ok_of_isStatic {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) : tstoreStep evm ≠ .ok after := by
  intro h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  have m : e3.message = evm.message := (chargeGas_sameContext h3).message.trans
    ((popWord_sameContext h2).message.trans (popWord_sameContext h1).message)
  simp [m, static, throw, throwThe, MonadExceptOf.throw] at h

/-- TLOAD keeps the message, the state, the substate and the code. -/
theorem tloadStep_sameContext {evm after : Evm fork Meter} (h : tloadStep evm = .ok after) :
    SameContext evm after := by
  obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (((popWord_sameContext h1).trans (chargeGas_sameContext h2)).trans
    (pushWord_sameContext h3)).advance

/-- The opcodes of transient storage have an instruction exactly from Dencun. -/
theorem isSome_transientStorageStep {op : Op} :
    (transientStorageStep (Meter := Meter) fork op).isSome ↔
      op ∈ [.tload, .tstore] ∧ op.since ≤ fork := by
  cases op <;> simp [transientStorageStep, Op.since] <;> split <;> simp_all

/-- Each instruction of transient storage keeps memory. -/
theorem memory_transientStorageStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : after.memory = evm.memory := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep
  case tload =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    simp only [advance, memory_pushWord h3, memory_chargeGas h2, (popWord_eq_ok h1).2.1]
  case tstore =>
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, _⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · cases h
    · cases h
      simp only [advance, memory_chargeGas h3, (popWord_eq_ok h2).2.1, (popWord_eq_ok h1).2.1]

end EthLib.Execution.Evm
