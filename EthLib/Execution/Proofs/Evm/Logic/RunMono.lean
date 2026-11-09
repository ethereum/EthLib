module

public import EthLib.Execution.Proofs.Evm.Logic.GasMono
public import EthLib.Execution.Proofs.Evm.Instructions.MemoryData
public import EthLib.Execution.Proofs.Evm.Instructions.ControlFlow
public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.Evm.Instructions.Return
public import EthLib.Execution.Proofs.Evm.Instructions.EnvironmentData
public import EthLib.Execution.Proofs.Evm.Instructions.LogData

/-!
# Proofs: instructions that are monotone in gas

The facts here are for the meter of one counter of gas, the meter of every fork before Glamsterdam.

At a later fork they hold of that meter, not of the meter of the fork.

Each instruction here is monotone in gas.

On a frame with less gas it fails, or it gives the same frame with the same less gas.

Its failure is an error, or a halt with an error.

The rules of the opcodes over the steps from frames that are monotone in gas rest on these facts.

An instruction that pushes a word of the frame is monotone when the word does not depend on gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-- A charge of `cost` from `gas`, then `F` of the gas left, fails or follows with `k` more gas.

`F` must give its frame with `k` more gas when its argument has `k` more. -/
theorem follows_map_charge {k gas cost : Nat} {F : Nat → Evm fork Nat}
    (hF : ∀ g, F (g + k) = addGas k (F g)) :
    Follows k ((GasMeter.charge gas cost).map F) ((GasMeter.charge (gas + k) cost).map F) := by
  simp only [GasMeter.charge]
  by_cases h : gas < cost
  · exact .inl (.inl ⟨.outOfGas, by simp [h, Except.map]⟩)
  · have h' : ¬gas + k < cost := by omega
    refine .inr ⟨F (gas - cost), by simp [h, Except.map], ?_⟩
    simp only [h', ↓reduceIte, Except.map]
    rw [show gas + k - cost = (gas - cost) + k by omega, hF]

/-- A charge of gas keeps the stack. -/
theorem stack_of_chargeGas {evm after : Evm fork Nat} {cost : Nat}
    (h : chargeGas evm cost = .ok after) : after.stack = evm.stack := by
  rw [(chargeGas_eq_ok_iff.mp h).2]

/-- A push on a full stack fails. -/
theorem pushWord_of_length_eq {evm : Evm fork Nat} (h : evm.stack.val.length = STACK_LIMIT)
    (x : U256) : pushWord evm x = .error .stackOverflow := by
  simp [pushWord, Stack.push, h, bind, Except.bind]

/-- A two-operand instruction of the stack is monotone in gas. -/
theorem runMono_binaryOp (cost : Nat) (f : U256 → U256 → U256) :
    RunMono (fork := fork) (binaryOp cost f) := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [binaryOp, popWord, Stack.pop, hs, bind, Except.bind]
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [binaryOp, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · have h : evm.stack.val = x :: y :: rest := by rw [hs]
    rw [binaryOp_cons h, binaryOp_cons (evm := addGas k evm) h]
    exact follows_map_charge fun _ => rfl

/-- A one-operand instruction of the stack is monotone in gas. -/
theorem runMono_unaryOp (cost : Nat) (f : U256 → U256) :
    RunMono (fork := fork) (unaryOp cost f) := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [unaryOp, popWord, Stack.pop, hs, bind, Except.bind]
  · have h : evm.stack.val = x :: rest := by rw [hs]
    rw [unaryOp_cons h, unaryOp_cons (evm := addGas k evm) h]
    exact follows_map_charge fun _ => rfl

/-- A three-operand instruction of the stack is monotone in gas. -/
theorem runMono_ternaryOp (cost : Nat) (f : U256 → U256 → U256 → U256) :
    RunMono (fork := fork) (ternaryOp cost f) := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [ternaryOp, popWord, Stack.pop, hs, bind, Except.bind]
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [ternaryOp, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [ternaryOp, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · have h : evm.stack.val = x :: y :: z :: rest := by rw [hs]
    rw [ternaryOp_cons h, ternaryOp_cons (evm := addGas k evm) h]
    exact follows_map_charge fun _ => rfl

/-- CALLDATALOAD is monotone in gas. -/
theorem runMono_calldataload : RunMono (fork := fork) calldataloadStep := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [calldataloadStep, popWord, Stack.pop, hs, bind, Except.bind]
  · have h : evm.stack.val = x :: rest := by rw [hs]
    rw [calldataloadStep_cons h, calldataloadStep_cons (evm := addGas k evm) h]
    exact follows_map_charge fun _ => rfl

/-- MSTORE is monotone in gas. -/
theorem runMono_mstore : RunMono (fork := fork) mstoreStep := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [mstoreStep, popWord, Stack.pop, hs, bind, Except.bind]
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [mstoreStep, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · have h : evm.stack.val = x :: y :: rest := by rw [hs]
    rw [mstoreStep_cons h, mstoreStep_cons (evm := addGas k evm) h]
    exact follows_map_charge fun _ => rfl

/-- MLOAD is monotone in gas. -/
theorem runMono_mload : RunMono (fork := fork) mloadStep := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [mloadStep, popWord, Stack.pop, hs, bind, Except.bind]
  · have h : evm.stack.val = x :: rest := by rw [hs]
    rw [mloadStep_cons h, mloadStep_cons (evm := addGas k evm) h]
    exact follows_map_charge fun _ => rfl

/-- KECCAK256 is monotone in gas. -/
theorem runMono_keccak256 : RunMono (fork := fork) keccak256Step := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [keccak256Step, popWord, Stack.pop, hs, bind, Except.bind]
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [keccak256Step, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · have h : evm.stack.val = x :: y :: rest := by rw [hs]
    rw [keccak256Step_cons h, keccak256Step_cons (evm := addGas k evm) h]
    exact follows_map_charge fun _ => rfl

/-- RETURN is monotone in gas. -/
theorem runMono_return : RunMono (fork := fork) returnStep := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [returnStep, haltWithOutput, popWord, Stack.pop, hs, bind, Except.bind]
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [returnStep, haltWithOutput, popWord, Stack.pop, hs, bind, Except.bind, pure,
      Except.pure]
  · have h : evm.stack.val = x :: y :: rest := by rw [hs]
    rw [returnStep_cons h, returnStep_cons (evm := addGas k evm) h]
    exact follows_map_charge fun _ => rfl

/-- REVERT is monotone in gas, since it always fails.

It gives an error, or halts the frame with the error of a revert. -/
theorem runMono_revert : RunMono (fork := fork) revertStep := by
  intro evm k
  rw [revertStep_eq]
  rcases hr : returnStep evm with e | c
  · exact .inl (.inl ⟨e, rfl⟩)
  · exact .inl (.inr ⟨_, rfl, (haltWithOutput_stops hr).2, by simp⟩)

/-- STOP is monotone in gas. -/
theorem runMono_stop : RunMono (fork := fork) stopStep := by
  intro evm k
  rw [stopStep_eq, stopStep_eq]
  exact .inr ⟨_, rfl, rfl⟩

/-- JUMPDEST is monotone in gas. -/
theorem runMono_jumpdest : RunMono (fork := fork) jumpdestStep := by
  intro evm k
  rw [jumpdestStep_eq, jumpdestStep_eq]
  exact follows_map_charge fun _ => rfl

/-- POP is monotone in gas. -/
theorem runMono_pop : RunMono (fork := fork) popStep := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [popStep, popWord, Stack.pop, hs, bind, Except.bind]
  · have h : evm.stack.val = x :: rest := by rw [hs]
    rw [popStep_cons h, popStep_cons (evm := addGas k evm) h]
    exact follows_map_charge fun _ => rfl

/-- EXP is monotone in gas. -/
theorem runMono_exp : RunMono (fork := fork) (expStep fork) := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, _ | ⟨y, rest⟩⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [expStep, popWord, Stack.pop, hs, bind, Except.bind]
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [expStep, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · have h : evm.stack.val = x :: y :: rest := by rw [hs]
    rw [expStep_of_cons h, expStep_of_cons (evm := addGas k evm) h]
    exact follows_map_charge fun _ => rfl

/-- An instruction that pushes a word of the frame follows its run with `k` more gas.

The word it reads must not depend on the gas of the frame. -/
theorem follows_readFrame (cost : Nat) (f : Evm fork Nat → U256) {evm : Evm fork Nat} {k : Nat}
    (hf : ∀ gas, f { evm with gas := gas } = f evm) :
    Follows k (readFrame cost f evm) (readFrame cost f (addGas k evm)) := by
  by_cases room : evm.stack.val.length < STACK_LIMIT
  · rw [readFrame_of_length_lt room, readFrame_of_length_lt (evm := addGas k evm) room]
    refine follows_map_charge fun g => ?_
    simp only [addGas, hf]
  · refine .inl (.inl ?_)
    simp only [readFrame, bind, Except.bind]
    split
    · exact ⟨_, rfl⟩
    · rename_i b hb
      rw [pushWord_of_length_eq (by rw [stack_of_chargeGas hb]; have := evm.stack.property; omega)]
      exact ⟨_, rfl⟩

/-- An instruction that pushes a word of the frame is monotone when the word ignores the gas. -/
theorem runMono_readFrame (cost : Nat) (f : Evm fork Nat → U256)
    (hf : ∀ (evm : Evm fork Nat) gas, f { evm with gas := gas } = f evm) :
    RunMono (readFrame cost f) :=
  fun evm _ => follows_readFrame cost f (hf evm)

/-- Each of PUSH0 to PUSH32 is monotone in gas. -/
theorem runMono_pushN (n : Fin 33) : RunMono (fork := fork) (pushN n) := by
  intro evm k
  by_cases room : evm.stack.val.length < STACK_LIMIT
  · rw [pushN_of_length_lt room, pushN_of_length_lt (evm := addGas k evm) room]
    exact follows_map_charge fun _ => rfl
  · refine .inl (.inl ?_)
    simp only [pushN, bind, Except.bind]
    split
    · exact ⟨_, rfl⟩
    · rename_i b hb
      rw [pushWord_of_length_eq (by rw [stack_of_chargeGas hb]; have := evm.stack.property; omega)]
      exact ⟨_, rfl⟩

/-- Each of DUP1 to DUP16 is monotone in gas. -/
theorem runMono_dupN (n : Fin 16) : RunMono (fork := fork) (dupN n) := by
  intro evm k
  by_cases hroom : evm.stack.val.length < STACK_LIMIT ∧ ∃ x, evm.stack.val[n.val]? = some x
  · obtain ⟨room, x, hx⟩ := hroom
    rw [dupN_of_getElem? hx room, dupN_of_getElem? (evm := addGas k evm) hx room]
    exact follows_map_charge fun _ => rfl
  · refine .inl (.inl ?_)
    simp only [dupN, bind, Except.bind]
    split
    · exact ⟨_, rfl⟩
    · rename_i b hb
      have hs := stack_of_chargeGas hb
      split
      · exact ⟨_, rfl⟩
      · rename_i x hx
        rw [hs] at hx
        have room : ¬evm.stack.val.length < STACK_LIMIT := fun r => hroom ⟨r, x, hx⟩
        rw [pushWord_of_length_eq (by rw [hs]; have := evm.stack.property; omega)]
        exact ⟨_, rfl⟩

/-- Each of SWAP1 to SWAP16 is monotone in gas. -/
theorem runMono_swapN (n : Fin 16) : RunMono (fork := fork) (swapN n) := by
  intro evm k
  have fails : ∀ {e : EvmError}, (∀ g, GasMeter.charge evm.gas OPCODE_SWAP = .ok g →
      swapN n evm = .error e) → ∃ e', swapN n evm = .error e' := by
    intro e h
    rcases hc : GasMeter.charge evm.gas OPCODE_SWAP with e' | g
    · exact ⟨e', by simp [swapN, chargeGas, hc, bind, Except.bind]⟩
    · exact ⟨e, h g hc⟩
  rcases hs : evm.stack with ⟨_ | ⟨top, rest⟩, hp⟩
  · exact .inl (.inl (fails fun _ hc => swapN_of_length_le hc (by rw [hs]; simp)))
  · have h : evm.stack.val = top :: rest := by rw [hs]
    rcases hx : rest[n.val]? with _ | x
    · exact .inl (.inl (fails fun _ hc => swapN_of_length_le hc (by
        rw [h, List.length_cons]; have := List.getElem?_eq_none_iff.mp hx; omega)))
    · rw [swapN_of_getElem? h hx, swapN_of_getElem? (evm := addGas k evm) h hx]
      exact follows_map_charge fun _ => rfl

/-- JUMP is monotone in gas. -/
theorem runMono_jump : RunMono (fork := fork) jumpStep := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨d, rest⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [jumpStep, popWord, Stack.pop, hs, bind, Except.bind]
  · simp only [jumpStep, popWord, Stack.pop, hs, chargeGas, bind, Except.bind, pure,
      Except.pure, addGas, GasMeter.charge]
    by_cases hg : evm.gas < OPCODE_JUMP
    · exact .inl (.inl ⟨.outOfGas, by simp [hg]⟩)
    · have hg' : ¬evm.gas + k < OPCODE_JUMP := by omega
      have he : evm.gas + k - OPCODE_JUMP = evm.gas - OPCODE_JUMP + k := by omega
      simp only [hg, hg', ↓reduceIte, he]
      split
      · exact .inr ⟨_, rfl, rfl⟩
      · exact .inl (.inl ⟨_, rfl⟩)

/-- JUMPI is monotone in gas. -/
theorem runMono_jumpi : RunMono (fork := fork) jumpiStep := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨d, _ | ⟨c, rest⟩⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [jumpiStep, popWord, Stack.pop, hs, bind, Except.bind]
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [jumpiStep, popWord, Stack.pop, hs, bind, Except.bind, pure, Except.pure]
  · simp only [jumpiStep, popWord, Stack.pop, hs, chargeGas, bind, Except.bind, pure,
      Except.pure, addGas, GasMeter.charge]
    by_cases hg : evm.gas < OPCODE_JUMPI
    · exact .inl (.inl ⟨.outOfGas, by simp [hg]⟩)
    · have hg' : ¬evm.gas + k < OPCODE_JUMPI := by omega
      have he : evm.gas + k - OPCODE_JUMPI = evm.gas - OPCODE_JUMPI + k := by omega
      simp only [hg, hg', ↓reduceIte, he]
      by_cases hc : c = 0
      · simp only [hc, ↓reduceIte]
        exact .inr ⟨_, rfl, rfl⟩
      · simp only [hc, ↓reduceIte]
        split
        · exact .inr ⟨_, rfl, rfl⟩
        · exact .inl (.inl ⟨_, rfl⟩)

/-- SLOAD is monotone in gas. -/
theorem runMono_sload : RunMono (fork := fork) sloadStep := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [sloadStep, popWord, Stack.pop, hs, bind, Except.bind]
  · have h : evm.stack.val = x :: rest := by rw [hs]
    rw [sloadStep_cons h, sloadStep_cons (evm := addGas k evm) h]
    simp only [accessStorageKey]
    split <;> exact follows_map_charge fun _ => rfl

@[simp] theorem message_addGas (k : Nat) (evm : Evm fork Nat) :
    (addGas k evm).message = evm.message := rfl

@[simp] theorem state_addGas (k : Nat) (evm : Evm fork Nat) : (addGas k evm).state = evm.state :=
  rfl

/-- A pop from a frame with `k` more gas pops the same word, from the frame with `k` more gas. -/
theorem popWord_addGas (evm : Evm fork Nat) (k : Nat) :
    popWord (addGas k evm) = (popWord evm).map fun p => (p.1, addGas k p.2) := by
  rcases evm with ⟨pc, ⟨_ | ⟨x, rest⟩, hp⟩⟩ <;> rfl

/-- The pops of the topics from a frame with `k` more gas pop the same topics. -/
theorem popTopics_addGas (n : Nat) : ∀ (evm : Evm fork Nat) (k : Nat),
    popTopics (addGas k evm) n = (popTopics evm n).map fun p => (p.1, addGas k p.2) := by
  induction n with
  | zero => intro evm k; rfl
  | succ n ih =>
    intro evm k
    simp only [popTopics]
    rw [popWord_addGas]
    rcases popWord evm with e | ⟨w, b⟩
    · rfl
    · simp only [Except.map, bind, Except.bind]
      rw [ih]
      rcases popTopics b n with e | ⟨t, c⟩ <;> rfl

/-- LOGn is monotone in gas. -/
theorem runMono_log (n : Nat) : RunMono (fork := fork) (logStep n) := by
  intro evm k
  simp only [logStep, bind, Except.bind]
  rw [popWord_addGas]
  rcases popWord evm with e | ⟨start, a1⟩
  · exact .inl (.inl ⟨e, rfl⟩)
  simp only [Except.map]
  rw [popWord_addGas]
  rcases popWord a1 with e | ⟨size, a2⟩
  · exact .inl (.inl ⟨e, rfl⟩)
  simp only [Except.map]
  rw [popTopics_addGas]
  rcases popTopics a2 n with e | ⟨topics, a3⟩
  · exact .inl (.inl ⟨e, rfl⟩)
  simp only [Except.map, chargeGasAndMemory, chargeGas, GasMeter.charge, bind, Except.bind,
    pure, Except.pure, gas_addGas]
  have hm : (addGas k a3).memory = a3.memory := rfl
  rw [hm]
  generalize logCost n size + (extendMemory a3.memory.size [(start, size)]).cost = c
  by_cases hg : a3.gas < c
  · exact .inl (.inl ⟨.outOfGas, by simp [hg]⟩)
  · have hg' : ¬a3.gas + k < c := by omega
    have he : a3.gas + k - c = a3.gas - c + k := by omega
    simp only [hg, hg', ↓reduceIte, he]
    by_cases hst : a3.message.isStatic = true
    · exact .inl (.inl ⟨_, by simp [hst]; rfl⟩)
    · have hst' : (addGas k a3).message.isStatic = false := by simpa using hst
      simp only [hst, hst', Bool.false_eq_true, ↓reduceIte]
      exact .inr ⟨_, rfl, rfl⟩

/-- A failure after the reads gives an error, or halts the frame with an error. -/
theorem fails_keepReads {evm : Evm fork Nat} {err : EvmError} :
    Fails (keepReads evm id (.error err)) := by
  simp only [keepReads]
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl, rfl, by simp [exceptionalHalt]⟩

/-- A charge that the gas covers succeeds, and with `k` more gas it gives `k` more gas. -/
theorem chargeGas_addGas {evm : Evm fork Nat} {cost k : Nat} (h : ¬evm.gas < cost) :
    chargeGas evm cost = .ok { evm with gas := evm.gas - cost } ∧
      chargeGas (addGas k evm) cost = .ok (addGas k { evm with gas := evm.gas - cost }) := by
  have h' : ¬evm.gas + k < cost := by omega
  simp only [chargeGas, GasMeter.charge, bind, Except.bind, h, h', ↓reduceIte, pure,
    Except.pure, addGas]
  refine ⟨trivial, ?_⟩
  congr 2
  omega

/-- A charge of state gas that the gas covers succeeds, and with `k` more gas it gives `k` more. -/
theorem chargeStateGas_addGas {evm : Evm fork Nat} {cost k : Nat} (h : ¬evm.gas < cost) :
    chargeStateGas evm cost = .ok { evm with gas := evm.gas - cost } ∧
      chargeStateGas (addGas k evm) cost =
        .ok (addGas k { evm with gas := evm.gas - cost }) := by
  have h' : ¬evm.gas + k < cost := by omega
  simp only [chargeStateGas, GasMeter.chargeState, bind, Except.bind, h, h',
    ↓reduceIte, pure, Except.pure, addGas]
  refine ⟨trivial, ?_⟩
  congr 2
  omega

/-- SSTORE is monotone in gas. -/
theorem runMono_sstore : RunMono (fork := fork) sstoreStep := by
  intro evm k
  simp only [sstoreStep, bind, Except.bind]
  rw [message_addGas]
  split
  · exact .inl (.inl ⟨_, rfl⟩)
  rw [popWord_addGas]
  rcases popWord evm with e | ⟨word, a1⟩
  · exact .inl (.inl ⟨e, rfl⟩)
  simp only [Except.map]
  rw [popWord_addGas]
  rcases popWord a1 with e | ⟨new, a2⟩
  · exact .inl (.inl ⟨e, rfl⟩)
  simp only [Except.map, gas_addGas, message_addGas, state_addGas]
  by_cases hstip : fork ≥ Fork.istanbul ∧ GasMeter.gasLeft a2.gas ≤ CALL_STIPEND
  · simp only [hstip, and_self, ↓reduceIte]
    exact .inl (.inl ⟨_, rfl⟩)
  have hstip' : ¬(fork ≥ Fork.istanbul ∧ GasMeter.gasLeft (a2.gas + k) ≤ CALL_STIPEND) := by
    rintro ⟨h1, h2⟩
    exact hstip ⟨h1, by simp only [GasMeter.gasLeft] at h2 ⊢; omega⟩
  simp only [hstip, hstip', ↓reduceIte]
  have hacc : accessStorageKey (addGas k a2) a2.message.currentTarget word.toBeBytes =
      ((accessStorageKey a2 a2.message.currentTarget word.toBeBytes).1,
        addGas k (accessStorageKey a2 a2.message.currentTarget word.toBeBytes).2) := by
    simp only [accessStorageKey]
    split <;> rfl
  rw [hacc]
  generalize accessStorageKey a2 a2.message.currentTarget word.toBeBytes = p
  rcases p with ⟨cold, b0⟩
  have hrec : recordStorageRead (addGas k b0) a2.message.currentTarget word.toBeBytes =
      addGas k (recordStorageRead b0 a2.message.currentTarget word.toBeBytes) := rfl
  simp only [hrec]
  generalize recordStorageRead b0 a2.message.currentTarget word.toBeBytes = b
  have hrefill : ∀ x, refillStateGas (addGas k b) x = addGas k (refillStateGas b x) :=
    fun _ => rfl
  simp only [hrefill]
  have hrefill' : ∀ x, refillStateGas b x = b := fun _ => rfl
  simp only [hrefill']
  generalize sstoreCost fork
    (a2.state.getStorageOriginal a2.message.currentTarget word.toBeBytes)
    (a2.state.getStorage a2.message.currentTarget word.toBeBytes) new cold = c
  by_cases hc : b.gas < c
  · rw [(chargeGas_eq_error_iff).mpr ⟨hc, rfl⟩]
    exact .inl fails_keepReads
  obtain ⟨h1, h2⟩ := chargeGas_addGas (k := k) hc
  rw [h1, h2]
  simp only
  generalize sstoreStateGas fork
    (a2.state.getStorageOriginal a2.message.currentTarget word.toBeBytes)
    (a2.state.getStorage a2.message.currentTarget word.toBeBytes) new = d
  by_cases hd : ({ b with gas := b.gas - c } : Evm fork Nat).gas < d
  · rw [show chargeStateGas { b with gas := b.gas - c } d = .error .outOfGas by
      simp [chargeStateGas, GasMeter.chargeState, bind, Except.bind, hd]]
    exact .inl fails_keepReads
  obtain ⟨h3, h4⟩ := chargeStateGas_addGas (k := k) hd
  rw [h3, h4]
  simp only [message_addGas, state_addGas]
  by_cases hs : b.message.isStatic = true
  · simp only [hs, ↓reduceIte]
    exact .inl fails_keepReads
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  split
  · exact .inl fails_keepReads
  · exact .inr ⟨_, rfl, rfl⟩

end EthLib.Execution.Evm.Logic
