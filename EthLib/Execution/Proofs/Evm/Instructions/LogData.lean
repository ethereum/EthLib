module

public import EthLib.Execution.Evm.Instructions.LogData
public import EthLib.Execution.Proofs.Evm.Machine.Memory
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.Instructions.LogData`

A LOG instruction appends exactly one log to the logs of the substate.

That log has the address of the current account and as many topics as the opcode names.

The message, the state and the rest of the substate stay as they are.

A LOG instruction never succeeds in a static frame.

The data of the log holds the bytes of memory in its range.

A LOG instruction keeps the size of memory a multiple of 32.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork Hash32 U256 byteAt byteAt_of_size_le)
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

omit [GasMeter Meter] in
/-- Popping topics keeps memory. -/
theorem popTopics_memory {evm after : Evm fork Meter} {n : Nat} {topics : List Hash32}
    (h : popTopics evm n = .ok (topics, after)) : after.memory = evm.memory := by
  induction n generalizing evm topics with
  | zero =>
    cases h
    rfl
  | succ k ih =>
    obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨ts, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    cases h
    rw [ih h2, (popWord_eq_ok h1).2.1]

/-- LOGn appends one log whose data is the range of memory it names.

The data has `size` bytes, and each is the byte of memory at its place from `start`.

Memory must start at a size that is a multiple of 32. -/
theorem logStep_data {n : Nat} {evm after : Evm fork Meter} {start size : U256}
    {rest : List U256} (hstack : evm.stack.val = start :: size :: rest)
    (hmod : evm.memory.size % 32 = 0) (h : logStep n evm = .ok after) :
    ∃ log : Log, after.substate.logs = evm.substate.logs.push log ∧
      log.data.size = size.toNat ∧ ∀ i,
        byteAt log.data i = if i < size.toNat then byteAt evm.memory (start.toNat + i) else 0 := by
  obtain ⟨⟨st, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨sz, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨topics, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨s1, m1, -⟩ := popWord_eq_ok h1
  obtain ⟨s2, m2, -⟩ := popWord_eq_ok h2
  rw [hstack] at s1
  obtain ⟨rfl, r1⟩ := List.cons.inj s1
  rw [← r1] at s2
  obtain ⟨rfl, -⟩ := List.cons.inj s2
  have c := (((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
    (popTopics_eq_ok h3).2).trans (chargeGasAndMemory_sameContext h4)
  have hm3 : e3.memory = evm.memory := by rw [popTopics_memory h3, m2, m1]
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    refine ⟨⟨e4.message.currentTarget, topics, memoryReadBytes e4.memory start.toNat size.toNat⟩,
      by simp only [advance, c.substate], ?_⟩
    by_cases hz : size = 0
    · subst hz
      have he : memoryReadBytes e4.memory start.toNat (0 : U256).toNat = .empty := by
        simp [memoryReadBytes]
      simp only [he]
      refine ⟨rfl, fun i => ?_⟩
      rw [byteAt_of_size_le (by simp), ite_eq_right_iff.mpr (fun hi => absurd hi (by simp))]
    · have fit := le_size_chargeGasAndMemory (by rw [hm3]; exact hmod) h4 (start, size)
        (by simp) hz
      simp only at fit
      refine ⟨size_memoryReadBytes fit, fun i => ?_⟩
      rw [byteAt_memoryReadBytes fit, byteAt_chargeGasAndMemory h4, hm3]

/-- LOGn keeps the size of memory a multiple of 32. -/
theorem size_logStep_mod {n : Nat} {evm after : Evm fork Meter}
    (hmod : evm.memory.size % 32 = 0) (h : logStep n evm = .ok after) :
    after.memory.size % 32 = 0 := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  have m4 := size_chargeGasAndMemory_mod (by
    rw [popTopics_memory h3, (popWord_eq_ok h2).2.1, (popWord_eq_ok h1).2.1]; exact hmod) h4
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    exact m4

end EthLib.Execution.Evm
