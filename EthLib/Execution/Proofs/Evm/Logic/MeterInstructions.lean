module

public import EthLib.Execution.Proofs.Evm.Logic.MeterSimulation

/-!
# Proofs: each instruction under the state gas meter

Each instruction that sends no message and pays no state gas, other than GAS, runs alike.

It runs under the state gas meter as it runs under one counter.

The run under the state gas meter starts with at least as much execution gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

set_option hygiene false in
/-- Close a relation of two frames whose fields agree, from the relation that holds before. -/
local macro "keep" : tactic =>
  `(tactic| exact ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩)

set_option hygiene false in
/-- Take the relation of two frames apart, so the second is the first with a state gas meter. -/
local macro "split_tracks" t:term : tactic =>
  `(tactic| obtain ⟨⟨meter, below, rfl⟩, hc, hf, hp, he⟩ := $t)

/-! ## The instructions of the stack -/

/-- A one-operand instruction of the stack runs alike under the state gas meter. -/
theorem unaryOp_bridge (cost : Nat) (f : U256 → U256) :
    Bridge (fork := fork) 1 (unaryOp cost f) (unaryOp cost f) := .of_sim fun _ _ below => by
  unfold unaryOp
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun _ _ t => ?_
  refine (t.pushWord _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- A two-operand instruction of the stack runs alike under the state gas meter. -/
theorem binaryOp_bridge (cost : Nat) (f : U256 → U256 → U256) :
    Bridge (fork := fork) 1 (binaryOp cost f) (binaryOp cost f) := .of_sim fun _ _ below => by
  unfold binaryOp
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun _ _ t => ?_
  refine (t.pushWord _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- A three-operand instruction of the stack runs alike under the state gas meter. -/
theorem ternaryOp_bridge (cost : Nat) (f : U256 → U256 → U256 → U256) :
    Bridge (fork := fork) 1 (ternaryOp cost f) (ternaryOp cost f) := .of_sim fun _ _ below => by
  unfold ternaryOp
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨z, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun _ _ t => ?_
  refine (t.pushWord _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- EXP runs alike under the state gas meter. -/
theorem expStep_bridge : Bridge (fork := fork) 1 (expStep fork) (expStep fork) :=
  .of_sim fun _ _ below => by
  unfold expStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun _ _ t => ?_
  refine (t.pushWord _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- KECCAK256 runs alike under the state gas meter. -/
theorem keccak256Step_bridge : Bridge (fork := fork) 1 keccak256Step keccak256Step :=
  .of_sim fun _ _ below => by
  unfold keccak256Step
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGasAndMemory _ _).bind fun _ _ t => ?_
  split_tracks t
  refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- POP runs alike under the state gas meter. -/
theorem popStep_bridge : Bridge (fork := fork) 1 popStep popStep := .of_sim fun _ _ below => by
  unfold popStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- PUSH runs alike under the state gas meter. -/
theorem pushN_bridge (n : Fin 33) :
    Bridge (fork := fork) (1 + n.val) (pushN n) (pushN n) := .of_sim fun _ _ below => by
  unfold pushN
  refine ((Tracks.init below).chargeGas _).bind fun _ _ t => ?_
  split_tracks t
  refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance _)

/-- DUP runs alike under the state gas meter. -/
theorem dupN_bridge (n : Fin 16) : Bridge (fork := fork) 1 (dupN n) (dupN n) :=
  .of_sim fun _ _ below => by
  unfold dupN
  refine ((Tracks.init below).chargeGas _).bind fun l _ t => ?_
  split_tracks t
  simp only [stack_withStateGas]
  cases l.stack.val[n.val]? with
  | none => exact Sim.error
  | some x =>
    refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
    exact Sim.pure (t.advance 1)

/-- SWAP runs alike under the state gas meter. -/
theorem swapN_bridge (n : Fin 16) : Bridge (fork := fork) 1 (swapN n) (swapN n) :=
  .of_sim fun _ _ below => by
  unfold swapN
  refine ((Tracks.init below).chargeGas _).bind fun l _ t => ?_
  split_tracks t
  simp only [stack_withStateGas]
  rcases l with ⟨pc, ⟨_ | ⟨top, rest⟩, hs⟩, memory, code, flags, gas, running, message, output,
    returnData, state, substate, error⟩
  · exact Sim.error
  · dsimp only
    cases rest[n.val]? with
    | none => exact Sim.error
    | some x => exact Sim.pure (Tracks.advance (by keep) 1)

/-- DUPN runs alike under the state gas meter, and moves past its immediate byte. -/
theorem dupnStep_bridge : Bridge (fork := fork) 2 dupnStep dupnStep :=
  .of_sim fun _ _ below => by
  unfold dupnStep
  refine ((Tracks.init below).chargeGas _).bind fun l _ t => ?_
  split_tracks t
  simp only [code_withStateGas, pc_withStateGas, stack_withStateGas]
  cases decodeSingle (immediateByte l.code l.pc) with
  | none => exact Sim.error
  | some n =>
    dsimp only
    cases l.stack.val[n - 1]? with
    | none => exact Sim.error
    | some x =>
      refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
      exact Sim.pure (t.advance 2)

/-- SWAPN runs alike under the state gas meter, and moves past its immediate byte. -/
theorem swapnStep_bridge : Bridge (fork := fork) 2 swapnStep swapnStep :=
  .of_sim fun _ _ below => by
  unfold swapnStep
  refine ((Tracks.init below).chargeGas _).bind fun l _ t => ?_
  split_tracks t
  simp only [code_withStateGas, pc_withStateGas, stack_withStateGas]
  cases decodeSingle (immediateByte l.code l.pc) with
  | none => exact Sim.error
  | some n =>
    dsimp only
    cases exchangeItems l.stack 0 n with
    | none => exact Sim.error
    | some stack => exact Sim.pure (Tracks.advance (low := { l with stack }) (by keep) 2)

/-- EXCHANGE runs alike under the state gas meter, and moves past its immediate byte. -/
theorem exchangeStep_bridge : Bridge (fork := fork) 2 exchangeStep exchangeStep :=
  .of_sim fun _ _ below => by
  unfold exchangeStep
  refine ((Tracks.init below).chargeGas _).bind fun l _ t => ?_
  split_tracks t
  simp only [code_withStateGas, pc_withStateGas, stack_withStateGas]
  cases decodePair (immediateByte l.code l.pc) with
  | none => exact Sim.error
  | some p =>
    obtain ⟨n, m⟩ := p
    dsimp only
    cases exchangeItems l.stack n m with
    | none => exact Sim.error
    | some stack => exact Sim.pure (Tracks.advance (low := { l with stack }) (by keep) 2)

/-! ## The instructions of control flow -/

/-- STOP runs alike under the state gas meter. -/
theorem stopStep_bridge : Bridge (fork := fork) 1 stopStep stopStep :=
  .of_sim fun _ _ below =>
    Sim.ok ⟨⟨_, below, rfl⟩, rfl, rfl, fun h => by simp [advance] at h, id,
      fun h => by simp [advance] at h⟩

/-- JUMP runs alike under the state gas meter. -/
theorem jumpStep_bridge : Bridge (fork := fork) 1 jumpStep jumpStep :=
  .of_sim fun _ _ below => by
  unfold jumpStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨d, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun l _ t => ?_
  split_tracks t
  simp only [validJumpDestinations_withStateGas]
  exact Sim.ite (fun valid => Sim.pure ⟨⟨meter, below, rfl⟩, hc, hf,
    fun _ => .inr (hf ▸ valid), fun h => he ▸ h, fun _ => he⟩) fun _ => Sim.error

/-- JUMPI runs alike under the state gas meter. -/
theorem jumpiStep_bridge : Bridge (fork := fork) 1 jumpiStep jumpiStep :=
  .of_sim fun _ _ below => by
  unfold jumpiStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨d, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨c, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun l _ t => ?_
  split_tracks t
  simp only [validJumpDestinations_withStateGas]
  exact Sim.ite (fun _ => Sim.pure (Tracks.advance (by keep) 1)) fun _ =>
    Sim.ite (fun valid => Sim.pure ⟨⟨meter, below, rfl⟩, hc, hf,
      fun _ => .inr (hf ▸ valid), fun h => he ▸ h, fun _ => he⟩) fun _ => Sim.error

/-- JUMPDEST runs alike under the state gas meter. -/
theorem jumpdestStep_bridge : Bridge (fork := fork) 1 jumpdestStep jumpdestStep :=
  .of_sim fun _ _ below => by
  unfold jumpdestStep
  refine ((Tracks.init below).chargeGas _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- A read of a value of the frame other than its gas, under each meter. -/
theorem readFrame_sim {cost : Nat} {value : Evm fork Nat → U256}
    {highValue : Evm fork StateGasMeter → U256}
    (values : ∀ evm meter, highValue (withStateGas evm meter) = value evm)
    {start : Evm fork Nat} {meter : StateGasMeter} (below : start.gas ≤ meter.gasLeft) :
    Sim (Lands start (start.pc + 1)) (readFrame cost value start)
      (readFrame cost highValue (withStateGas start meter)) := by
  unfold readFrame
  refine ((Tracks.init below).chargeGas _).bind fun l _ t => ?_
  split_tracks t
  rw [values]
  refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- A read of a field of the frame other than its gas runs alike under the state gas meter. -/
theorem readFrame_bridge {cost : Nat} {value : Evm fork Nat → U256}
    {highValue : Evm fork StateGasMeter → U256}
    (values : ∀ evm meter, highValue (withStateGas evm meter) = value evm) :
    Bridge 1 (readFrame cost value) (readFrame cost highValue) :=
  .of_sim fun _ _ below => readFrame_sim values below

/-- A read of a number from the environment, under each meter. -/
theorem readNumber_bridge {cost : Nat} {value : Evm fork Nat → Nat}
    {highValue : Evm fork StateGasMeter → Nat}
    (values : ∀ evm meter, highValue (withStateGas evm meter) = value evm) :
    Bridge 1 (readNumber cost value) (readNumber cost highValue) :=
  .of_sim fun _ _ below => by
  unfold readNumber
  rw [values]
  refine Sim.ite (fun _ => readFrame_sim (fun _ _ => rfl) below) fun _ => ?_
  exact ((Tracks.init below).chargeGas _).bind fun _ _ _ => Sim.error

/-! ## The instructions of memory and data -/

/-- MLOAD runs alike under the state gas meter. -/
theorem mloadStep_bridge : Bridge (fork := fork) 1 mloadStep mloadStep :=
  .of_sim fun _ _ below => by
  unfold mloadStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGasAndMemory _ _).bind fun _ _ t => ?_
  split_tracks t
  refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- MSTORE runs alike under the state gas meter. -/
theorem mstoreStep_bridge : Bridge (fork := fork) 1 mstoreStep mstoreStep :=
  .of_sim fun _ _ below => by
  unfold mstoreStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGasAndMemory _ _).bind fun _ _ t => ?_
  split_tracks t
  exact Sim.pure (Tracks.advance (by keep) 1)

/-- MSTORE8 runs alike under the state gas meter. -/
theorem mstore8Step_bridge : Bridge (fork := fork) 1 mstore8Step mstore8Step :=
  .of_sim fun _ _ below => by
  unfold mstore8Step
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGasAndMemory _ _).bind fun _ _ t => ?_
  split_tracks t
  exact Sim.pure (Tracks.advance (by keep) 1)

/-- MCOPY runs alike under the state gas meter. -/
theorem mcopyStep_bridge : Bridge (fork := fork) 1 mcopyStep mcopyStep :=
  .of_sim fun _ _ below => by
  unfold mcopyStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨z, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGasAndMemory _ _).bind fun _ _ t => ?_
  split_tracks t
  exact Sim.pure (Tracks.advance (by keep) 1)

/-- CALLDATALOAD runs alike under the state gas meter. -/
theorem calldataloadStep_bridge : Bridge (fork := fork) 1 calldataloadStep calldataloadStep :=
  .of_sim fun _ _ below => by
  unfold calldataloadStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun _ _ t => ?_
  split_tracks t
  refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- A copy of bytes of the frame to memory runs alike under the state gas meter. -/
theorem copyToMemory_bridge (base : Nat) (source : Evm fork Nat → ByteArray)
    (highSource : Evm fork StateGasMeter → ByteArray)
    (sources : ∀ evm meter, highSource (withStateGas evm meter) = source evm) :
    Bridge 1 (fun evm => copyToMemory base (source evm) evm)
      (fun evm => copyToMemory base (highSource evm) evm) :=
  .of_sim fun _ _ below => by
  rw [sources]
  unfold copyToMemory
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨z, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGasAndMemory _ _).bind fun _ _ t => ?_
  split_tracks t
  exact Sim.pure (Tracks.advance (by keep) 1)

/-- RETURNDATACOPY runs alike under the state gas meter. -/
theorem returndatacopyStep_bridge : Bridge (fork := fork) 1 returndatacopyStep returndatacopyStep :=
  .of_sim fun _ _ below => by
  unfold returndatacopyStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨z, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  split_tracks t
  refine (Tracks.chargeGas (by keep) _).bind fun _ _ t => ?_
  split_tracks t
  exact Sim.ite (fun _ => Sim.error) fun _ => Sim.pure (Tracks.advance (by keep) 1)

/-! ## The halts with output -/

private theorem haltWithOutput_sim {start : Evm fork Nat} {meter : StateGasMeter} {next : Nat}
    (below : start.gas ≤ meter.gasLeft) :
    Sim (fun a b => Lands start next a b ∧ a.running = false)
      (haltWithOutput start) (haltWithOutput (withStateGas start meter)) := by
  unfold haltWithOutput
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGasAndMemory _ _).bind fun _ _ t => ?_
  split_tracks t
  exact Sim.pure ⟨⟨⟨meter, below, rfl⟩, hc, hf, fun h => by simp at h, fun h => he ▸ h,
    fun h => by simp at h⟩, rfl⟩

/-- RETURN runs alike under the state gas meter. -/
theorem returnStep_bridge : Bridge (fork := fork) 1 returnStep returnStep :=
  .of_sim fun _ _ below => (haltWithOutput_sim below).mono fun _ _ h => h.1

/-- REVERT keeps the code and the flags, and the bridge asks nothing more of its result. -/
theorem revertStep_bridge : Bridge (fork := fork) 1 revertStep revertStep :=
  .of_sim fun start _ below => by
  unfold revertStep
  refine (haltWithOutput_sim (next := start.pc + 1) below).bind ?_
  rintro a _ ⟨⟨⟨meter, below, rfl⟩, hc, hf, -, -, -⟩, running⟩
  exact Sim.pure ⟨⟨meter, below, rfl⟩, hc, hf, fun h => by simp_all, fun h => (nomatch h),
    fun h => by simp_all⟩

/-! ## The instructions of the environment -/

/-- BLOCKHASH runs alike under the state gas meter. -/
theorem blockhashStep_bridge : Bridge (fork := fork) 1 blockhashStep blockhashStep :=
  .of_sim fun _ _ below => by
  unfold blockhashStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun _ _ t => ?_
  split_tracks t
  refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- BLOBHASH runs alike under the state gas meter. -/
theorem blobhashStep_bridge (h : .dencun ≤ fork) :
    Bridge (fork := fork) 1 (blobhashStep h) (blobhashStep h) :=
  .of_sim fun _ _ below => by
  unfold blobhashStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun _ _ t => ?_
  split_tracks t
  refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-! ## The instructions of accounts -/

/-- BALANCE runs alike under the state gas meter. -/
theorem balanceStep_bridge : Bridge (fork := fork) 1 balanceStep balanceStep :=
  .of_sim fun _ _ below => by
  unfold balanceStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨w, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  split_tracks t
  by_cases hb : fork ≥ .berlin <;> simp only [accessAddress, hb, ↓reduceIte] <;>
  · refine (Tracks.chargeGas (by keep) _).bind fun _ _ t => ?_
    split_tracks t
    refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
    exact Sim.pure (t.advance 1)

/-- EXTCODESIZE runs alike under the state gas meter. -/
theorem extcodesizeStep_bridge : Bridge (fork := fork) 1 extcodesizeStep extcodesizeStep :=
  .of_sim fun _ _ below => by
  unfold extcodesizeStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨w, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  split_tracks t
  by_cases hb : fork ≥ .berlin <;> simp only [accessAddress, hb, ↓reduceIte] <;>
  · refine (Tracks.chargeGas (by keep) _).bind fun _ _ t => ?_
    split_tracks t
    refine Sim.ofState.bind ?_
    rintro c _ rfl
    refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
    exact Sim.pure (t.advance 1)

/-- EXTCODECOPY runs alike under the state gas meter. -/
theorem extcodecopyStep_bridge : Bridge (fork := fork) 1 extcodecopyStep extcodecopyStep :=
  .of_sim fun _ _ below => by
  unfold extcodecopyStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨w, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨z, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  split_tracks t
  by_cases hb : fork ≥ .berlin <;> simp only [accessAddress, hb, ↓reduceIte] <;>
  · refine (Tracks.chargeGasAndMemory (by keep) _ _).bind fun _ _ t => ?_
    split_tracks t
    refine Sim.ofState.bind ?_
    rintro c _ rfl
    exact Sim.pure (Tracks.advance (by keep) 1)

/-- EXTCODEHASH runs alike under the state gas meter. -/
theorem extcodehashStep_bridge : Bridge (fork := fork) 1 extcodehashStep extcodehashStep :=
  .of_sim fun _ _ below => by
  unfold extcodehashStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨w, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  split_tracks t
  by_cases hb : fork ≥ .berlin <;> simp only [accessAddress, hb, ↓reduceIte] <;>
  · refine (Tracks.chargeGas (by keep) _).bind fun _ _ t => ?_
    split_tracks t
    refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
    exact Sim.pure (t.advance 1)

/-- SELFBALANCE runs alike under the state gas meter. -/
theorem selfbalance_bridge :
    Bridge (fork := fork) 1
      (fun evm => readFrame OPCODE_SELFBALANCE
        (fun evm => (evm.state.getAccount evm.message.currentTarget).balance)
        (recordAccountRead evm evm.message.currentTarget))
      (fun evm => readFrame OPCODE_SELFBALANCE
        (fun evm => (evm.state.getAccount evm.message.currentTarget).balance)
        (recordAccountRead evm evm.message.currentTarget)) :=
  .of_sim fun _ _ below => readFrame_sim (fun _ _ => rfl) below

/-! ## The instructions of storage, transient storage and logs -/

/-- SLOAD runs alike under the state gas meter. -/
theorem sloadStep_bridge : Bridge (fork := fork) 1 sloadStep sloadStep :=
  .of_sim fun _ _ below => by
  unfold sloadStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨w, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  split_tracks t
  by_cases hb : fork ≥ .berlin <;> simp only [accessStorageKey, hb, ↓reduceIte] <;>
  · refine (Tracks.chargeGas (by keep) _).bind fun _ _ t => ?_
    split_tracks t
    refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
    exact Sim.pure (t.advance 1)

/-- TLOAD runs alike under the state gas meter. -/
theorem tloadStep_bridge : Bridge (fork := fork) 1 tloadStep tloadStep :=
  .of_sim fun _ _ below => by
  unfold tloadStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨w, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun _ _ t => ?_
  split_tracks t
  refine (Tracks.pushWord (by keep) _).bind fun _ _ t => ?_
  exact Sim.pure (t.advance 1)

/-- TSTORE runs alike under the state gas meter. -/
theorem tstoreStep_bridge : Bridge (fork := fork) 1 tstoreStep tstoreStep :=
  .of_sim fun _ _ below => by
  unfold tstoreStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨w, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨v, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGas _).bind fun _ _ t => ?_
  split_tracks t
  simp only [message_withStateGas]
  exact Sim.ite (fun _ => Sim.error) fun _ => Sim.pure (Tracks.advance (by keep) 1)

/-- LOG runs alike under the state gas meter. -/
theorem logStep_bridge (n : Nat) : Bridge (fork := fork) 1 (logStep n) (logStep n) :=
  .of_sim fun _ _ below => by
  unfold logStep
  refine (Tracks.init below).popWord.bind ?_
  rintro ⟨x, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine t.popWord.bind ?_
  rintro ⟨y, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.popTopics n).bind ?_
  rintro ⟨ts, _⟩ ⟨_, _⟩ ⟨rfl, t⟩
  refine (t.chargeGasAndMemory _ _).bind fun _ _ t => ?_
  split_tracks t
  simp only [message_withStateGas]
  exact Sim.ite (fun _ => Sim.error) fun _ => Sim.pure (Tracks.advance (by keep) 1)

end EthLib.Execution.Evm.Logic
