module

public import EthLib.Execution.Proofs.Evm.Logic.Rules

/-!
# Proofs: rules for the opcodes that read the block and the transaction

Each opcode here pushes a word that the message holds, and pays its price.

Each rule goes from one running frame to the next, at every fork where its opcode exists.

The rules work out the charge of one counter of gas.

An opcode that reads a number aborts when the number fits no word, so its rule asks that it fits.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork}

/-! ## The instruction table -/

section Table

variable {Meter : Type} [GasMeter Meter]

/-- From Istanbul, CHAINID runs the read of the chain id of the block. -/
theorem instruction_chainid (h : .istanbul ≤ fork) :
    instruction (Meter := Meter) fork .chainid = some (readFrame OPCODE_CHAINID fun evm =>
      BitVec.ofNat 256 evm.message.blockEnv.chainId.toNat) := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From London, BASEFEE runs the read of the base fee of the block. -/
theorem instruction_basefee (h : .london ≤ fork) :
    instruction (Meter := Meter) fork .basefee = some (readNumber OPCODE_BASEFEE fun evm =>
      evm.message.blockEnv.baseFeePerGas h) := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From Dencun, BLOBBASEFEE runs the read of the blob base fee of the block. -/
theorem instruction_blobbasefee (h : .dencun ≤ fork) :
    instruction (Meter := Meter) fork .blobbasefee = some (readNumber OPCODE_BLOBBASEFEE fun evm =>
      evm.message.blockEnv.blobBaseFee h) := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From Paris, PREVRANDAO runs the read of the randomness of the beacon chain. -/
theorem instruction_prevrandao (h : .paris ≤ fork) :
    instruction (Meter := Meter) fork .prevrandao = some (readFrame OPCODE_PREVRANDAO fun evm =>
      U256.fromBeBytes (evm.message.blockEnv.prevRandao h)) := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- Before Paris, the opcode `0x44` runs the read of the difficulty of the block. -/
theorem instruction_difficulty (h : fork < .paris) :
    instruction (Meter := Meter) fork .prevrandao = some (readNumber OPCODE_PREVRANDAO fun evm =>
      evm.message.blockEnv.difficulty) := by
  have hn : ¬.paris ≤ fork := Nat.not_le_of_lt h
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, hn, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From Glamsterdam, SLOTNUM runs the read of the slot number of the block. -/
theorem instruction_slotnum (h : .glamsterdam ≤ fork) :
    instruction (Meter := Meter) fork .slotnum = some (readFrame OPCODE_SLOTNUM fun evm =>
      BitVec.ofNat 256 (evm.message.blockEnv.slotNumber h).toNat) := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

end Table

variable {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-! ## Words of the block -/

/-- COINBASE pushes the address of the beneficiary of the block as a word, for 2 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem coinbase_ruleG (hlt : pc < code.size) (hbyte : code[pc] = 0x41) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.blockEnv.coinbase.toU256 :: stack) memory (gas - 2)
        state substate returnData) :=
  push_of_readFrameG hlt hbyte (ofByte_of_decode (op := .coinbase) rfl (Fork.frontier_le _)) rfl
    (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- COINBASE pushes the address of the beneficiary of the block as a word, for 2 gas. -/
theorem coinbase_rule (hlt : pc < code.size) (hbyte : code[pc] = 0x41) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.blockEnv.coinbase.toU256 :: stack) memory (gas - 2)
        state substate returnData) :=
  (coinbase_ruleG hlt hbyte hgas hstack).toHoare

/-- TIMESTAMP pushes the timestamp of the block, for 2 gas.

It holds over the steps from frames that are monotone in gas. -/
theorem timestamp_ruleG (hlt : pc < code.size) (hbyte : code[pc] = 0x42) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.blockEnv.timestamp :: stack) memory (gas - 2)
        state substate returnData) :=
  push_of_readFrameG hlt hbyte (ofByte_of_decode (op := .timestamp) rfl (Fork.frontier_le _)) rfl
    (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- TIMESTAMP pushes the timestamp of the block, for 2 gas. -/
theorem timestamp_rule (hlt : pc < code.size) (hbyte : code[pc] = 0x42) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (message.blockEnv.timestamp :: stack) memory (gas - 2)
        state substate returnData) :=
  (timestamp_ruleG hlt hbyte hgas hstack).toHoare

/-- NUMBER pushes the number of the block, for 2 gas.

The number must fit a word.

It holds over the steps from frames that are monotone in gas. -/
theorem number_ruleG (hlt : pc < code.size) (hbyte : code[pc] = 0x43)
    (hfit : message.blockEnv.number < 2 ^ 256) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.blockEnv.number :: stack) memory
        (gas - 2) state substate returnData) :=
  push_of_readNumberG hlt hbyte (ofByte_of_decode (op := .number) rfl (Fork.frontier_le _)) rfl
    (fun _ _ hm _ _ => by rw [hm]) hfit hgas hstack

/-- NUMBER pushes the number of the block, for 2 gas.

The number must fit a word. -/
theorem number_rule (hlt : pc < code.size) (hbyte : code[pc] = 0x43)
    (hfit : message.blockEnv.number < 2 ^ 256) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.blockEnv.number :: stack) memory
        (gas - 2) state substate returnData) :=
  (number_ruleG hlt hbyte hfit hgas hstack).toHoare

/-- GASLIMIT pushes the gas limit of the block, for 2 gas.

The limit must fit a word.

It holds over the steps from frames that are monotone in gas. -/
theorem gaslimit_ruleG (hlt : pc < code.size) (hbyte : code[pc] = 0x45)
    (hfit : message.blockEnv.gasLimit < 2 ^ 256) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.blockEnv.gasLimit :: stack) memory
        (gas - 2) state substate returnData) :=
  push_of_readNumberG hlt hbyte (ofByte_of_decode (op := .gaslimit) rfl (Fork.frontier_le _)) rfl
    (fun _ _ hm _ _ => by rw [hm]) hfit hgas hstack

/-- GASLIMIT pushes the gas limit of the block, for 2 gas.

The limit must fit a word. -/
theorem gaslimit_rule (hlt : pc < code.size) (hbyte : code[pc] = 0x45)
    (hfit : message.blockEnv.gasLimit < 2 ^ 256) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.blockEnv.gasLimit :: stack) memory
        (gas - 2) state substate returnData) :=
  (gaslimit_ruleG hlt hbyte hfit hgas hstack).toHoare

/-- From Paris, PREVRANDAO pushes the randomness of the beacon chain, for 2 gas, by EIP-4399.

It holds over the steps from frames that are monotone in gas. -/
theorem prevrandao_ruleG (hfork : .paris ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x44) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (U256.fromBeBytes (message.blockEnv.prevRandao hfork) :: stack)
        memory (gas - 2) state substate returnData) :=
  push_of_readFrameG hlt hbyte
    (ofByte_of_decode (op := .prevrandao) rfl (Fork.frontier_le _))
    (instruction_prevrandao hfork) (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- From Paris, PREVRANDAO pushes the randomness of the beacon chain, for 2 gas, by EIP-4399. -/
theorem prevrandao_rule (hfork : .paris ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x44) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (U256.fromBeBytes (message.blockEnv.prevRandao hfork) :: stack)
        memory (gas - 2) state substate returnData) :=
  (prevrandao_ruleG hfork hlt hbyte hgas hstack).toHoare

/-- Before Paris, the opcode `0x44` pushes the difficulty of the block, for 2 gas.

The difficulty must fit a word.

It holds over the steps from frames that are monotone in gas. -/
theorem difficulty_ruleG (hfork : fork < .paris) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x44) (hfit : message.blockEnv.difficulty < 2 ^ 256) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.blockEnv.difficulty :: stack) memory
        (gas - 2) state substate returnData) :=
  push_of_readNumberG hlt hbyte (ofByte_of_decode (op := .prevrandao) rfl (Fork.frontier_le _))
    (instruction_difficulty hfork) (fun _ _ hm _ _ => by rw [hm]) hfit hgas hstack

/-- Before Paris, the opcode `0x44` pushes the difficulty of the block, for 2 gas.

The difficulty must fit a word. -/
theorem difficulty_rule (hfork : fork < .paris) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x44) (hfit : message.blockEnv.difficulty < 2 ^ 256) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.blockEnv.difficulty :: stack) memory
        (gas - 2) state substate returnData) :=
  (difficulty_ruleG hfork hlt hbyte hfit hgas hstack).toHoare

/-- From Istanbul, CHAINID pushes the chain id of the block, for 2 gas, by EIP-1344.

It holds over the steps from frames that are monotone in gas. -/
theorem chainid_ruleG (hfork : .istanbul ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x46) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.blockEnv.chainId.toNat :: stack) memory
        (gas - 2) state substate returnData) :=
  push_of_readFrameG hlt hbyte (ofByte_of_decode (op := .chainid) rfl hfork)
    (instruction_chainid hfork) (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- From Istanbul, CHAINID pushes the chain id of the block, for 2 gas, by EIP-1344. -/
theorem chainid_rule (hfork : .istanbul ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x46) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.blockEnv.chainId.toNat :: stack) memory
        (gas - 2) state substate returnData) :=
  (chainid_ruleG hfork hlt hbyte hgas hstack).toHoare

/-- From London, BASEFEE pushes the base fee of the block, for 2 gas, by EIP-3198.

The base fee must fit a word.

It holds over the steps from frames that are monotone in gas. -/
theorem basefee_ruleG (hfork : .london ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x48) (hfit : message.blockEnv.baseFeePerGas hfork < 2 ^ 256)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 (message.blockEnv.baseFeePerGas hfork) :: stack)
        memory (gas - 2) state substate returnData) :=
  push_of_readNumberG hlt hbyte (ofByte_of_decode (op := .basefee) rfl hfork)
    (instruction_basefee hfork) (fun _ _ hm _ _ => by rw [hm]) hfit hgas hstack

/-- From London, BASEFEE pushes the base fee of the block, for 2 gas, by EIP-3198.

The base fee must fit a word. -/
theorem basefee_rule (hfork : .london ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x48) (hfit : message.blockEnv.baseFeePerGas hfork < 2 ^ 256)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 (message.blockEnv.baseFeePerGas hfork) :: stack)
        memory (gas - 2) state substate returnData) :=
  (basefee_ruleG hfork hlt hbyte hfit hgas hstack).toHoare

/-- From Dencun, BLOBBASEFEE pushes the blob base fee of the block, for 2 gas, by EIP-7516.

The fee must fit a word.

It holds over the steps from frames that are monotone in gas. -/
theorem blobbasefee_ruleG (hfork : .dencun ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x4a) (hfit : message.blockEnv.blobBaseFee hfork < 2 ^ 256)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 (message.blockEnv.blobBaseFee hfork) :: stack)
        memory (gas - 2) state substate returnData) :=
  push_of_readNumberG hlt hbyte (ofByte_of_decode (op := .blobbasefee) rfl hfork)
    (instruction_blobbasefee hfork) (fun _ _ hm _ _ => by rw [hm]) hfit hgas hstack

/-- From Dencun, BLOBBASEFEE pushes the blob base fee of the block, for 2 gas, by EIP-7516.

The fee must fit a word. -/
theorem blobbasefee_rule (hfork : .dencun ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x4a) (hfit : message.blockEnv.blobBaseFee hfork < 2 ^ 256)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 (message.blockEnv.blobBaseFee hfork) :: stack)
        memory (gas - 2) state substate returnData) :=
  (blobbasefee_ruleG hfork hlt hbyte hfit hgas hstack).toHoare

/-- From Glamsterdam, SLOTNUM pushes the slot number of the block, for 2 gas, by EIP-7843.

It holds over the steps from frames that are monotone in gas. -/
theorem slotnum_ruleG (hfork : .glamsterdam ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x4b) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1)
        (BitVec.ofNat 256 (message.blockEnv.slotNumber hfork).toNat :: stack) memory (gas - 2)
        state substate returnData) :=
  push_of_readFrameG hlt hbyte (ofByte_of_decode (op := .slotnum) rfl hfork)
    (instruction_slotnum hfork) (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- From Glamsterdam, SLOTNUM pushes the slot number of the block, for 2 gas, by EIP-7843. -/
theorem slotnum_rule (hfork : .glamsterdam ≤ fork) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x4b) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1)
        (BitVec.ofNat 256 (message.blockEnv.slotNumber hfork).toNat :: stack) memory (gas - 2)
        state substate returnData) :=
  (slotnum_ruleG hfork hlt hbyte hgas hstack).toHoare

/-! ## Words of the transaction -/

/-- GASPRICE pushes the gas price of the transaction, for 2 gas.

The price must fit a word.

It holds over the steps from frames that are monotone in gas. -/
theorem gasprice_ruleG (hlt : pc < code.size) (hbyte : code[pc] = 0x3a)
    (hfit : message.txEnv.gasPrice < 2 ^ 256) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    HoareG fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.txEnv.gasPrice :: stack) memory
        (gas - 2) state substate returnData) :=
  push_of_readNumberG hlt hbyte (ofByte_of_decode (op := .gasprice) rfl (Fork.frontier_le _)) rfl
    (fun _ _ hm _ _ => by rw [hm]) hfit hgas hstack

/-- GASPRICE pushes the gas price of the transaction, for 2 gas.

The price must fit a word. -/
theorem gasprice_rule (hlt : pc < code.size) (hbyte : code[pc] = 0x3a)
    (hfit : message.txEnv.gasPrice < 2 ^ 256) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (BitVec.ofNat 256 message.txEnv.gasPrice :: stack) memory
        (gas - 2) state substate returnData) :=
  (gasprice_ruleG hlt hbyte hfit hgas hstack).toHoare

end EthLib.Execution.Evm.Logic
