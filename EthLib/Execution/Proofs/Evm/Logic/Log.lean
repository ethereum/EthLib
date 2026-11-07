module

public import EthLib.Execution.Proofs.Evm.Logic.Rules
public import EthLib.Execution.Proofs.Evm.Instructions.LogData

/-!
# Proofs: a rule for LOG0 to LOG4

LOGn appends one log to the substate of the frame.

The log holds the current address, `n` topics, and a range of memory as its data.

The rule holds at every fork, with one counter of gas, the meter of the forks before Glamsterdam.

It pays 375, 8 for each byte of data, 375 for each topic, and the growth of memory.

The frame must be one that may change the state, since LOGn fails in a static frame.

The rule says nothing of the order of the logs of several frames.

It says nothing either of a log that a later revert of the frame or of a caller drops.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

omit [GasMeter Meter] in
/-- The pops of the topics take the words on top of the stack, in order, as the topics. -/
theorem popTopics_append {evm : Evm fork Meter} {words rest : List U256}
    (h : evm.stack.val = words ++ rest) :
    popTopics evm words.length = .ok (words.map U256.toBeBytes, { evm with stack := ⟨rest, by
      have := evm.stack.property; rw [h] at this; simp at this; omega⟩ }) := by
  induction words generalizing evm with
  | nil =>
    simp only [List.nil_append] at h
    simp only [popTopics, List.map_nil, List.length_nil]
    rcases evm with ⟨pc, ⟨l, hl⟩⟩
    simp only at h
    subst h
    rfl
  | cons w words ih =>
    simp only [List.cons_append] at h
    have hs : evm.stack = ⟨w :: (words ++ rest), h ▸ evm.stack.property⟩ := Subtype.ext h
    simp only [List.length_cons, popTopics, popWord, hs, Stack.pop, bind, Except.bind, pure,
      Except.pure]
    rw [ih (evm := { evm with stack := ⟨words ++ rest, _⟩ }) rfl]
    rfl

variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
  {state : State.TransactionState} {substate : Substate}

/-- LOGn runs the append of a log with `n` topics. -/
theorem instruction_log (n : Fin 5) :
    instruction (Meter := Nat) fork (.log n) = some (logStep n.val) := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
    HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- The price of LOGn with `size` bytes of data: 375, 8 for each byte, and 375 for each topic. -/
def logCost (n : Nat) (size : U256) : Nat :=
  OPCODE_LOG_BASE + OPCODE_LOG_DATA_PER_BYTE * size.toNat + OPCODE_LOG_TOPIC * n

/-- LOGn appends a log of the current address, with the `n` words below the range as its topics.

The data of the log is the range of memory from `start`, after memory grows to hold it.

It pays the price of the log and the growth of memory, in a frame that may change the state. -/
theorem log {n : Fin 5} {byte : UInt8} {start size : U256} {words rest : List U256}
    (hlen : words.length = n.val) (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.decode byte = some (.log n)) (hstatic : message.isStatic = false)
    (hgas : logCost n.val size + (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    Hoare fork (At code message pc (start :: size :: (words ++ rest)) memory gas state substate)
      (At code message (pc + 1) rest
        (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
        (gas - (logCost n.val size + (extendMemory memory.size [(start, size)]).cost)) state
        { substate with
          logs := substate.logs.push
            { address := message.currentTarget
              topics := words.map U256.toBeBytes
              data := memoryReadBytes
                (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
                start.toNat size.toNat } }) := by
  apply At.rule hlt hbyte (ofByte_of_decode decoded (Fork.frontier_le _)) (instruction_log n)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hs, hss⟩
  subst hm hg hs hss hmem
  have hl := evm.stack.property
  rw [hst] at hl
  have hlr : (words ++ rest).length ≤ STACK_LIMIT := by simp at hl ⊢; omega
  have hs : evm.stack = ⟨start :: size :: (words ++ rest), hst ▸ evm.stack.property⟩ :=
    Subtype.ext hst
  have htop := popTopics_append (evm := { evm with stack := ⟨words ++ rest, hlr⟩ })
    (words := words) (rest := rest) rfl
  rw [hlen] at htop
  simp only [logStep, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  rw [htop]
  simp only [chargeGasAndMemory, chargeGas, GasMeter.charge, logCost] at hgas ⊢
  simp only [Nat.not_lt.mpr hgas, ite_false, bind, Except.bind, pure, Except.pure, hstatic,
    Bool.false_eq_true]
  exact ⟨_, rfl, hcode, hj, rfl, by simp [advance, hpc], rfl, rfl, rfl, hrun, herr, rfl, rfl⟩

end EthLib.Execution.Evm.Logic
