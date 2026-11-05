module

public import EthLib.Execution.Evm.Instructions.TransientStorage
public import EthLib.Execution.Proofs.Evm.Step
public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: `Evm.Instructions.TransientStorage`

After TSTORE, the transient word at its key is the word it wrote.

So a TLOAD of that key in the same frame reads it back.

TSTORE never succeeds in a static frame.

TLOAD and TSTORE exist exactly from Dencun.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

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

/-- TLOAD keeps the message, the state and the substate. -/
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

end EthLib.Execution.Evm
