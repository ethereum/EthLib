module

public import EthLib.Execution.Rpc.Eip3155

/-!
# Proofs: the trace of a transaction in the lines of EIP-3155

The line of a step has the required fields in the order of the EIP, then the optional ones.

Each entry that a step adds holds the size of the memory before that step, and its opcode byte.

Under the configuration of the lines, each such entry holds its stack and its return data.

A trace has one line for each entry of the logger, and one summary line.
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base

/-- The keys of the line of a step: the required ones in the order of the EIP, then the others.

The name of the opcode is always there.

The error, the memory and the storage are there exactly when the logger recorded them. -/
theorem eip3155Fields_keys (e : StructLog) :
    (eip3155Fields e).map Prod.fst =
      ["pc", "op", "gas", "gasCost", "memSize", "stack", "depth", "returnData", "refund",
        "opName"] ++
      (if e.error.isSome then ["error"] else []) ++ (if e.memory.isSome then ["memory"] else []) ++
      (if e.storage.isSome then ["storage"] else []) := by
  cases h₁ : e.error <;> cases h₂ : e.memory <;> cases h₃ : e.storage <;>
    simp [eip3155Fields, h₁, h₂, h₃]

/-- The line of a step holds the memory size of its entry. -/
theorem eip3155Fields_memSize (e : StructLog) :
    ("memSize", Json.num e.memSize) ∈ eip3155Fields e := by
  simp [eip3155Fields]

/-- Each entry that a step of the logger adds has the size of the memory before that step.

It also has the byte of the code at its position, or 0 past the end of the code.

Every other entry was there before the step. -/
theorem record_memSize {config : TraceConfig} {fork : Fork} {Meter : Type}
    [Evm.GasMeter Meter] {evm : Evm.Evm fork Meter}
    {result : Except Evm.EvmError (Evm.StepResult fork Meter)} {tracer : Tracer} {e : StructLog}
    (h : e ∈ (tracer.record config evm result).logs) :
    e ∈ tracer.logs ∨ (e.pc = evm.pc ∧ e.memSize = evm.memory.size ∧
      e.opcode = if h : evm.pc < evm.code.size then evm.code[evm.pc].toNat else 0) := by
  unfold Tracer.record at h
  split at h
  · exact .inl h
  · rcases Array.mem_push.mp h with old | new
    · exact .inl old
    · exact .inr (by subst new; exact ⟨rfl, rfl, rfl⟩)

/-- Under the configuration of the lines, each entry that a step adds has its stack and its return
data. -/
theorem record_eip3155Config {fork : Fork} {Meter : Type} [Evm.GasMeter Meter]
    {evm : Evm.Evm fork Meter} {result : Except Evm.EvmError (Evm.StepResult fork Meter)}
    {tracer : Tracer} {e : StructLog} (h : e ∈ (tracer.record eip3155Config evm result).logs) :
    e ∈ tracer.logs ∨ (e.stack.isSome ∧ e.returnData.isSome) := by
  unfold Tracer.record at h
  split at h
  · exact .inl h
  · rcases Array.mem_push.mp h with old | new
    · exact .inl old
    · exact .inr (by subst new; simp [eip3155Config])

/-- A trace has one line for each entry of the logger, and one summary line. -/
theorem eip3155Lines_length (fork : Fork) (trace : TransactionTrace) (stateRoot : Hash32) :
    (eip3155Lines fork trace stateRoot).length = trace.structLogs.size + 1 := by
  simp [eip3155Lines]

end EthLib.Execution.Rpc
