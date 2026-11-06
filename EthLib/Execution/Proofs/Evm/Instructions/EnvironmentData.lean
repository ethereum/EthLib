module

public import EthLib.Base.Proofs.Fork
public import EthLib.Execution.Evm.Instructions.EnvironmentData
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.Instructions.EnvironmentData`

An instruction that reads the frame pays its price, then pushes its value on a stack with room.

BLOCKHASH gives the parent's hash for the block before, and 0 out of the 256 blocks before.

A list of hashes too short to reach a block gives 0 for it, never another hash.

BLOBHASH gives the hash at its index, and 0 past the end of the list.

BLOCKHASH pays its price, and so does BLOBHASH, which exists from Dencun.

Then BLOCKHASH puts the hash of the block in place of the number.

BLOBHASH puts the versioned hash in place of the index.

SLOTNUM pays the base price and pushes the slot of the block, from Glamsterdam on.

Each instruction exists exactly from the fork that adds its opcode.

None of these instructions changes the message, the state or the substate of the frame.

None of them changes memory either.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork Hash32 U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- An instruction that reads the frame, on a stack with room: pay, then push the value. -/
theorem readFrame_of_length_lt {cost : Nat} {value : Evm fork Meter → U256}
    {evm : Evm fork Meter} (room : evm.stack.val.length < STACK_LIMIT) :
    readFrame cost value evm = (GasMeter.charge evm.gas cost).map fun gas =>
      { evm with
        gas
        stack := ⟨value { evm with gas } :: evm.stack.val, room⟩
        pc := evm.pc + 1 } := by
  have full : ¬(evm.stack.val.length = STACK_LIMIT) := by omega
  simp only [readFrame, chargeGas, pushWord, advance, Stack.push]
  rcases hc : GasMeter.charge evm.gas cost with _ | _ <;>
    simp [bind, Except.bind, pure, Except.pure, Except.map, full]

/-- BLOCKHASH on a block number: pay, then put the hash of that block in its place. -/
theorem blockhashStep_cons {evm : Evm fork Meter} {number : U256} {rest : List U256}
    (h : evm.stack.val = number :: rest) :
    blockhashStep evm = (GasMeter.charge evm.gas OPCODE_BLOCKHASH).map fun gas =>
      { evm with
        stack := ⟨blockHash evm.message.blockEnv.blockHashes evm.message.blockEnv.number
            number.toNat :: rest, length_cons_le (dropped := [number]) h (by simp)⟩,
        gas, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨number :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := length_cons_le (x := number) (dropped := [number]) h (by simp)
    simp only [List.length_cons] at this
    omega
  simp only [blockhashStep, popWord, chargeGas, pushWord, advance, hstack, Stack.pop, Stack.push]
  rcases hc : GasMeter.charge evm.gas OPCODE_BLOCKHASH with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, room]

/-- BLOBHASH on an index, from Dencun: pay, then put the versioned hash of that index in place. -/
theorem blobhashStep_cons (hfork : .dencun ≤ fork) {evm : Evm fork Meter} {index : U256}
    {rest : List U256} (h : evm.stack.val = index :: rest) :
    blobhashStep hfork evm = (GasMeter.charge evm.gas OPCODE_BLOBHASH).map fun gas =>
      { evm with
        stack := ⟨blobHash (evm.message.txEnv.blobVersionedHashes hfork) index :: rest,
          length_cons_le (dropped := [index]) h (by simp)⟩,
        gas, pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨index :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := length_cons_le (x := index) (dropped := [index]) h (by simp)
    simp only [List.length_cons] at this
    omega
  simp only [blobhashStep, popWord, chargeGas, pushWord, advance, hstack, Stack.pop, Stack.push]
  rcases hc : GasMeter.charge evm.gas OPCODE_BLOBHASH with _ | _ <;>
    simp [hc, bind, Except.bind, pure, Except.pure, Except.map, room]

/-- A block out of the 256 blocks before the current one has hash 0. -/
theorem blockHash_of_not_mem {hashes : List Hash32} {current n : Nat}
    (h : ¬(n < current ∧ current ≤ n + 256)) : blockHash hashes current n = 0 := by
  simp [blockHash, h]

/-- The block before the current one has the last hash of the list, the parent's. -/
theorem blockHash_parent {hashes : List Hash32} {current : Nat} (pos : 0 < current)
    (nonempty : hashes ≠ []) :
    blockHash hashes current (current - 1) = U256.fromBeBytes (hashes.getLast nonempty) := by
  have hlen : 0 < hashes.reverse.length := by simpa using List.length_pos_iff.mpr nonempty
  simp only [blockHash, show current - 1 < current ∧ current ≤ current - 1 + 256 by omega,
    and_self, ite_true, show current - (current - 1) - 1 = 0 by omega,
    List.getElem?_eq_getElem hlen, List.getElem_zero, List.head_reverse]

/-- A list too short to reach block `n` gives 0, never the hash of another block. -/
theorem blockHash_of_length_lt {hashes : List Hash32} {current n : Nat}
    (h : hashes.length < current - n) : blockHash hashes current n = 0 := by
  unfold blockHash
  split
  · rw [List.getElem?_eq_none (by simp; omega)]
  · rfl

/-- A blob index past the end of the list has hash 0. -/
theorem blobHash_of_le {hashes : List Hash32} {index : U256} (h : hashes.length ≤ index.toNat) :
    blobHash hashes index = 0 := by
  simp [blobHash, List.getElem?_eq_none h]

/-- A blob index within the list has the hash at that index, read big-endian. -/
theorem blobHash_of_lt {hashes : List Hash32} {index : U256} (h : index.toNat < hashes.length) :
    blobHash hashes index = U256.fromBeBytes hashes[index.toNat] := by
  simp [blobHash, List.getElem?_eq_getElem h]

/-- An opcode of the environment has an instruction exactly from the fork that adds it.

No other opcode has one. -/
theorem isSome_environmentStep {op : Op} :
    (environmentStep (Meter := Meter) fork op).isSome ↔
      op ∈ [.address, .origin, .caller, .callvalue, .gasprice, .blockhash, .coinbase, .timestamp,
        .number, .prevrandao, .gaslimit, .chainid, .basefee, .blobhash, .blobbasefee,
        .slotnum] ∧
      op.since ≤ fork := by
  cases op <;> simp [environmentStep, Op.since, Fork.frontier_le] <;> split <;>
    simp_all

/-- SLOTNUM, from Glamsterdam, on a stack with room: pay the base price, push the slot.

Its price is the base price, 2 gas, as EIP-7843 gives. -/
theorem environmentStep_slotnum (h : .glamsterdam ≤ fork) {evm : Evm fork Meter}
    (room : evm.stack.val.length < STACK_LIMIT) :
    ∃ step, environmentStep fork .slotnum = some step ∧
      step evm = (GasMeter.charge evm.gas GasCosts.BASE).map fun gas =>
        { evm with
          gas
          stack := ⟨BitVec.ofNat 256 (evm.message.blockEnv.slotNumber h).toNat :: evm.stack.val,
            room⟩
          pc := evm.pc + 1 } :=
  ⟨readFrame GasCosts.OPCODE_SLOTNUM fun evm =>
      BitVec.ofNat 256 (evm.message.blockEnv.slotNumber h).toNat,
    by simp [environmentStep, h], readFrame_of_length_lt room⟩

/-- Before Glamsterdam, SLOTNUM has no instruction. -/
theorem environmentStep_slotnum_of_lt (h : fork < .glamsterdam) :
    environmentStep (Meter := Meter) fork .slotnum = none := by
  have hNot : ¬ .glamsterdam ≤ fork := fun hle => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hle)
  simp [environmentStep, hNot]

/-- Each instruction of the environment keeps the message, the state, the substate and the code. -/
theorem environmentStep_sameContext {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : environmentStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : SameContext evm after := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals first
    | (subst hstep; exact readFrame_sameContext h)
    | skip
  case prevrandao =>
    split at hstep <;> (simp only [Option.some.injEq] at hstep; subst hstep) <;>
      exact readFrame_sameContext h
  case chainid | basefee | blobbasefee | slotnum =>
    split at hstep
    · simp only [Option.some.injEq] at hstep
      subst hstep
      exact readFrame_sameContext h
    · cases hstep
  case blobhash =>
    split at hstep
    · simp only [Option.some.injEq] at hstep
      subst hstep
      obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact (((popWord_sameContext h1).trans (chargeGas_sameContext h2)).trans
        (pushWord_sameContext h3)).advance
    · cases hstep
  case blockhash =>
    subst hstep
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (((popWord_sameContext h1).trans (chargeGas_sameContext h2)).trans
      (pushWord_sameContext h3)).advance

/-- Each instruction of the environment keeps memory. -/
theorem memory_environmentStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : environmentStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : after.memory = evm.memory := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals first
    | (subst hstep; exact memory_readFrame h)
    | skip
  case prevrandao =>
    split at hstep <;> (simp only [Option.some.injEq] at hstep; subst hstep) <;>
      exact memory_readFrame h
  case chainid | basefee | blobbasefee | slotnum =>
    split at hstep
    · simp only [Option.some.injEq] at hstep
      subst hstep
      exact memory_readFrame h
    · cases hstep
  case blobhash =>
    split at hstep
    · simp only [Option.some.injEq] at hstep
      subst hstep
      obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
      cases h
      simp only [advance, memory_pushWord h3, memory_chargeGas h2, (popWord_eq_ok h1).2.1]
    · cases hstep
  case blockhash =>
    subst hstep
    obtain ⟨⟨_, _⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    simp only [advance, memory_pushWord h3, memory_chargeGas h2, (popWord_eq_ok h1).2.1]

end EthLib.Execution.Evm
