module

public import EthLib.Execution.Proofs.Evm.Logic.Log

/-!
# Proofs: a static frame does not write storage or emit a log

A message that STATICCALL sends is static.

In a static frame, SSTORE and LOG0 to LOG4 do not complete.

Every step of such a frame at one of these opcodes stops the frame.

A failed step that aborts the run gives no step at all, so it is not covered here.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)

variable {fork : Fork}

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- In a static frame, a step at SSTORE stops the frame. -/
theorem running_eq_false_of_sstore_of_isStatic (hlt : pc < code.size) (hbyte : code[pc] = 0x55)
    (hstatic : message.isStatic = true) {evm after : Evm fork Nat}
    (hat : At code message pc stack memory gas state substate evm) (hs : Step fork evm after) :
    after.running = false := by
  obtain ⟨hc, -, hm, hpc, -⟩ := hat
  cases hs with
  | next _ hstep =>
    have hin : evm.pc < evm.code.size := by rw [hc, hpc]; exact hlt
    have hdec : Op.ofByte fork evm.code[evm.pc] = some .sstore := by
      simp only [hc, hpc, hbyte]
      exact ofByte_of_decode rfl (Fork.frontier_le _)
    rw [step_of_instruction hin hdec instruction_sstore] at hstep
    rcases hss : sstoreStep evm with _ | after'
    · rw [hss] at hstep
      cases hstep
    · rw [hss] at hstep
      cases hstep
      exact (sstoreStep_halts_of_isStatic (by rw [hm]; exact hstatic) hss).1
  | halt => rfl

/-- In a static frame, a step at LOGn stops the frame. -/
theorem running_eq_false_of_log_of_isStatic {n : Fin 5} {byte : UInt8} (hlt : pc < code.size)
    (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.log n))
    (hstatic : message.isStatic = true) {evm after : Evm fork Nat}
    (hat : At code message pc stack memory gas state substate evm) (hs : Step fork evm after) :
    after.running = false := by
  obtain ⟨hc, -, hm, hpc, -⟩ := hat
  cases hs with
  | next _ hstep =>
    have hin : evm.pc < evm.code.size := by rw [hc, hpc]; exact hlt
    have hdec : Op.ofByte fork evm.code[evm.pc] = some (.log n) := by
      simp only [hc, hpc, hbyte]
      exact ofByte_of_decode decoded (Fork.frontier_le _)
    rw [step_of_instruction hin hdec (instruction_log n)] at hstep
    rcases hls : logStep n.val evm with _ | after'
    · rw [hls] at hstep
      cases hstep
    · exact absurd hls (logStep_ne_ok_of_isStatic (by rw [hm]; exact hstatic))
  | halt => rfl

end EthLib.Execution.Evm.Logic
