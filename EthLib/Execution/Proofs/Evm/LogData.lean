module

public import EthLib.Execution.Evm.LogData
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.LogData`

A LOG instruction appends exactly one log to the logs of the substate.

That log has the address of the current account and as many topics as the opcode names.

The message, the state and the rest of the substate stay as they are.

A LOG instruction never succeeds in a static frame.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork Hash32 U256)
open EthLib.Execution.Blocks (Log)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

omit [GasMeter Meter] in
/-- Popping topics gives as many topics as asked, and keeps the context of the frame. -/
theorem popTopics_eq_ok {evm after : Evm fork Meter} {n : Nat} {topics : List Hash32}
    (h : popTopics evm n = .ok (topics, after)) :
    topics.length = n ∧ SameContext evm after := by
  induction n generalizing evm topics with
  | zero =>
    cases h
    exact ⟨rfl, SameContext.refl _⟩
  | succ k ih =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨ts, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    obtain ⟨hlen, hctx⟩ := ih h2
    exact ⟨by simp [hlen], (popWord_sameContext h1).trans hctx⟩

/-- LOGn appends one log of the current account with `n` topics, and changes nothing else. -/
theorem logStep_eq_ok {n : Nat} {evm after : Evm fork Meter} (h : logStep n evm = .ok after) :
    ∃ log : Log, log.address = evm.message.currentTarget ∧ log.topics.length = n ∧
      after.message = evm.message ∧ after.state = evm.state ∧
      after.substate = { evm.substate with logs := evm.substate.logs.push log } := by
  obtain ⟨⟨st, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨sz, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨topics, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨hlen, c3⟩ := popTopics_eq_ok h3
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  have c := (((popWord_sameContext h1).trans (popWord_sameContext h2)).trans c3).trans
    (chargeGasAndMemory_sameContext h4)
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    refine ⟨⟨e4.message.currentTarget, topics, memoryReadBytes e4.memory st.toNat sz.toNat⟩,
      by rw [c.message], hlen, c.message, c.state, ?_⟩
    simp only [advance, c.substate]

/-- LOGn never succeeds in a static frame. -/
theorem logStep_ne_ok_of_isStatic {n : Nat} {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) : logStep n evm ≠ .ok after := by
  intro h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  have c := (((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
    (popTopics_eq_ok h3).2).trans (chargeGasAndMemory_sameContext h4)
  simp [c.message, static, throw, throwThe, MonadExceptOf.throw] at h

end EthLib.Execution.Evm
