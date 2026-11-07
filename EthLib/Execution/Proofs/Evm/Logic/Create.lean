module

public import EthLib.Execution.Proofs.Evm.Logic.Call
public import EthLib.Execution.Proofs.Evm.Call.Create

/-!
# Proofs: rules for CREATE and CREATE2

CREATE and CREATE2 send a message that runs init code from memory at a new address.

The rules here hold from Berlin to the fork before Glamsterdam, with one counter of gas.

The creation pays 32000, the growth of memory, and from Shanghai 2 gas per word of init code.

The price of init code and its limit of 49152 bytes come from EIP-3860, from Shanghai.

CREATE2, from Constantinople, also pays 6 gas per word to hash the init code, by EIP-1014.

The new address is the one that the specification derives.

For CREATE it hashes the sender and its nonce.

For CREATE2 it hashes the sender, the salt and the init code.

The address must hold no code and a nonce of 0, as EIP-684 asks.

The creation accesses the new address, by EIP-2929.

The nonce of the current account grows by one.

It passes on all but one 64th of the gas left, by EIP-150.

The message has no target, no data and the value, and it is not static.

The callee runs arbitrary init code, so the rule takes an assumption on the frame that ends it.

The caller then pushes the new address when that frame ends with no error, and 0 otherwise.

Out of scope: a creation that runs no message, a creation in a static frame, and the deposit.

Sources: EIP-150, EIP-684, EIP-1014, EIP-2929 and EIP-3860.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Address Fork U256)
open GasCosts

variable {fork : Fork}

/-- The step of CREATE, or of CREATE2 with the salt `salt`, sends a message that runs init code.

The init code is the range of memory that the operands name, once memory grows for it.

The caller has paid the price of the creation, the growth of memory and the gas it passes on.

It passes on the gas that a creation passes on, from the gas it has left after the price.

It has accessed the new address, recorded the reads, and its state is the one with its nonce grown.

It keeps its output.

The message runs the init code at the new address, from the current account, with the value.

It has no target and no data, and it is not static. -/
theorem createStep_child (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {create2 : Bool}
    {evm : Evm fork Nat} {value start size salt : U256} {rest : List U256} {address : Address}
    (hst : evm.stack.val =
      value :: start :: size :: ((if create2 then [salt] else []) ++ rest))
    (hstatic : evm.message.isStatic = false)
    (hinit : .shapella ≤ fork → size.toNat ≤ maxInitCodeSize fork)
    (hbal : value ≤ (evm.state.getAccount evm.message.currentTarget).balance)
    (hnonce : (evm.state.getAccount evm.message.currentTarget).nonce ≠ MAX_NONCE)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (haddr : creationAddress evm.message.currentTarget
      (evm.state.getAccount evm.message.currentTarget).nonce
      (if create2 then some salt else none)
      (memoryReadBytes (memoryExtend evm.memory
        (extendMemory evm.memory.size [(start, size)]).expandBy) start.toNat size.toNat) =
        .ok address)
    (hdeploy : evm.state.accountDeployable address = true)
    (hgas : createBaseCost fork +
        (if create2 then OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0) +
        (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
      (extendMemory evm.memory.size [(start, size)]).cost ≤ evm.gas) :
    ∃ caller msg,
      createStep create2 evm = .ok (.child caller msg (resumeCreate fork caller 0 address)) ∧
      caller.code = evm.code ∧ caller.validJumpDestinations = evm.validJumpDestinations ∧
      caller.message = evm.message ∧ caller.pc = evm.pc ∧ caller.stack.val = rest ∧
      caller.memory = memoryExtend evm.memory
        (extendMemory evm.memory.size [(start, size)]).expandBy ∧
      caller.gas = evm.gas - (createBaseCost fork +
          (if create2 then OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0) +
          (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
        (extendMemory evm.memory.size [(start, size)]).cost) -
        createMessageGas fork (evm.gas - (createBaseCost fork +
          (if create2 then OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0) +
          (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
        (extendMemory evm.memory.size [(start, size)]).cost)) ∧
      caller.running = evm.running ∧ caller.error = evm.error ∧ caller.output = evm.output ∧
      ((evm.state.recordAccountRead evm.message.currentTarget).recordAccountRead
        address).incrementNonce fork evm.message.currentTarget = .ok caller.state ∧
      caller.substate = { evm.substate with
        accessedAddresses := evm.substate.accessedAddresses.insert address } ∧
      msg.gas = createMessageGas fork (evm.gas - (createBaseCost fork +
          (if create2 then OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0) +
          (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
        (extendMemory evm.memory.size [(start, size)]).cost)) ∧
      msg.caller = evm.message.currentTarget ∧ msg.target = none ∧
      msg.currentTarget = address ∧ msg.codeAddress = none ∧
      msg.code = memoryReadBytes (memoryExtend evm.memory
        (extendMemory evm.memory.size [(start, size)]).expandBy) start.toNat size.toNat ∧
      msg.data = .empty ∧ msg.value = value ∧ msg.depth = evm.message.depth + 1 ∧
      msg.isStatic = false := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hmg : ∀ g, ¬g < createMessageGas fork g := by
    intro g
    simp only [createMessageGas, htw, ite_true, maxMessageCallGas]
    omega
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hgd : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).accountDeployable y = tx.accountDeployable y := fun _ _ _ => rfl
  have hread : (memoryReadBytes (memoryExtend evm.memory
      (extendMemory evm.memory.size [(start, size)]).expandBy) start.toNat size.toNat).size ≤
      size.toNat := by
    unfold memoryReadBytes
    split
    · simp
    · simp only [ByteArray.size_extract]
      omega
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst hstatic hbal hnonce hdepth haddr hdeploy hgas hread ⊢
  subst hst
  have hlim : ¬(Fork.shapella ≤ fork ∧ maxInitCodeSize fork < (memoryReadBytes (memoryExtend memory
      (extendMemory memory.size [(start, size)]).expandBy) start.toNat size.toNat).size) := by
    rintro ⟨hs, hlt⟩
    have := hinit hs
    omega
  obtain ⟨state', hinc⟩ := State.TransactionState.incrementNonce_isOk fork
    ((state.recordAccountRead message.currentTarget).recordAccountRead address)
    message.currentTarget
  cases create2 <;>
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, ge_iff_le,
    List.nil_append, List.cons_append] at haddr hgas ⊢ <;>
  simp [createStep, hng, popWord, Stack.pop, popSalt, bind, Except.bind, pure, Except.pure,
    chargeGasAndMemory, chargeGas, GasMeter.charge, Nat.not_lt.mpr hgas, genericCreate, hlim,
    hstatic, launchCreate, recordAccountRead, hga, hgd, BitVec.not_lt.mpr hbal, hnonce,
    Nat.not_lt.mpr hdepth, haddr, accessAddress, hfork, keepReads, createNewAccountStateGas,
    chargeStateGas, GasMeter.chargeState, hmg, hdeploy, hinc, Except.mapError, GasMeter.gasLeft,
    GasMeter.drain, GasMeter.reservoir] <;>
  exact ⟨_, _, ⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- From Tangerine Whistle, a creation passes on all but one 64th of the gas left, by EIP-150. -/
theorem createMessageGas_of_tangerineWhistle (hfork : .tangerineWhistle ≤ fork) (gas : Nat) :
    createMessageGas fork gas = gas - gas / 64 := by
  simp [createMessageGas, hfork, maxMessageCallGas]

/-- A creator with room on its stack resumes from every frame that ends the creation.

It pushes the new address for a frame with no error and 0 otherwise.

It gets back the gas of the frame, and keeps its memory and its output. -/
theorem resumeCreate_eq {caller child : Evm fork Nat} {address : Address}
    (hlen : caller.stack.val.length < STACK_LIMIT) :
    ∃ after, resumeCreate fork caller 0 address child = .ok after ∧
      after.code = caller.code ∧ after.validJumpDestinations = caller.validJumpDestinations ∧
      after.message = caller.message ∧ after.pc = caller.pc + 1 ∧
      after.stack.val = (if child.error.isNone then address.toU256 else 0) :: caller.stack.val ∧
      after.memory = caller.memory ∧ after.gas = caller.gas + child.gas ∧
      after.running = caller.running ∧ after.error = caller.error ∧ after.output = caller.output ∧
      after.state = (incorporateChild fork caller child).state ∧
      after.substate = (incorporateChild fork caller child).substate := by
  have hne : caller.stack.val.length ≠ STACK_LIMIT := Nat.ne_of_lt hlen
  unfold resumeCreate incorporateChild
  by_cases h : child.error.isNone <;>
    simp [pushWord, Stack.push, bind, Except.bind, pure, Except.pure, advance, refillStateGas,
      GasMeter.refill, GasMeter.absorb, *]

/-- CREATE is no instruction of the frame alone: it sends a message. -/
theorem instruction_create : instruction (Meter := Nat) fork .create = none := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
    selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- CREATE2 is no instruction of the frame alone: it sends a message. -/
theorem instruction_create2 : instruction (Meter := Nat) fork .create2 = none := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
    selfdestructOpStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- CREATE runs the step of a creation. -/
theorem messageInstruction_create :
    messageInstruction (Meter := Nat) fork .create = some (createStep false) := by
  simp [messageInstruction, callInstruction, createInstruction, HOrElse.hOrElse, OrElse.orElse,
    Option.orElse]

/-- From Constantinople, CREATE2 runs the step of a creation with a salt. -/
theorem messageInstruction_create2 (hfork : .constantinople ≤ fork) :
    messageInstruction (Meter := Nat) fork .create2 = some (createStep true) := by
  simp [messageInstruction, callInstruction, createInstruction, HOrElse.hOrElse, OrElse.orElse,
    Option.orElse, hfork]

variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
  {state : State.TransactionState} {substate : Substate}

/-- From Berlin to before Glamsterdam, CREATE, or CREATE2 with a salt, of init code in memory.

The opcode at the program counter runs the step of that creation.

The frame may change the state, holds the value, and its nonce is below the greatest.

Its depth leaves room for one more frame.

From Shanghai, the init code is at most the greatest size, by EIP-3860.

The new address is the one that the specification derives, and holds no code and a nonce of 0.

The creation pays its price and the growth of memory, and it accesses the new address.

The message runs the init code at the new address, from the current account, with the value.

It has no target and no data, and it is not static.

The state of the creator is the one with its nonce grown, after the reads of both accounts.

The rule holds for every frame that ends the message and meets the assumption.

The creator pushes the new address when that frame ends with no error, and 0 otherwise.

It gets back the gas that the frame leaves, and its state and substate come from the frame.

The rule says nothing more of them, since the init code is arbitrary. -/
theorem createKindWith (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {create2 : Bool}
    {byte : UInt8} {op : Op} {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {value start size salt : U256} {rest : List U256} {address : Address}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hnone : instruction (Meter := Nat) fork op = none)
    (hrun : messageInstruction (Meter := Nat) fork op = some (createStep create2))
    (hstatic : message.isStatic = false)
    (hinit : .shapella ≤ fork → size.toNat ≤ maxInitCodeSize fork)
    (hbal : value ≤ (state.getAccount message.currentTarget).balance)
    (hnonce : (state.getAccount message.currentTarget).nonce ≠ MAX_NONCE)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (haddr : creationAddress message.currentTarget (state.getAccount message.currentTarget).nonce
      (if create2 then some salt else none)
      (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
        start.toNat size.toNat) = .ok address)
    (hdeploy : state.accountDeployable address = true)
    (hgas : createBaseCost fork +
        (if create2 then OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0) +
        (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
      (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    HoareUnder fork callee
      (At code message pc (value :: start :: size :: ((if create2 then [salt] else []) ++ rest))
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        ((state.recordAccountRead message.currentTarget).recordAccountRead address).incrementNonce
          fork message.currentTarget = .ok caller.state ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert address } ∧
        msg.gas = createMessageGas fork (gas - (createBaseCost fork +
            (if create2 then OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0) +
            (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
          (extendMemory memory.size [(start, size)]).cost)) ∧
        msg.caller = message.currentTarget ∧ msg.target = none ∧ msg.currentTarget = address ∧
        msg.codeAddress = none ∧
        msg.code = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(start, size)]).expandBy) start.toNat size.toNat ∧
        msg.data = .empty ∧ msg.value = value ∧ msg.depth = message.depth + 1 ∧
        msg.isStatic = false ∧
        At code message (pc + 1) ((if child.error.isNone then address.toU256 else 0) :: rest)
          (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          (gas - (createBaseCost fork +
              (if create2 then OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0) +
              (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
            (extendMemory memory.size [(start, size)]).cost) -
            createMessageGas fork (gas - (createBaseCost fork +
              (if create2 then OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0) +
              (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
            (extendMemory memory.size [(start, size)]).cost)) + child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  apply HoareUnder.of_child
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun', herr, hout, hs, hss⟩
  subst hm hg hs hss hmem
  obtain ⟨caller, msg, hstep, c1, c2, c3, c4, c5, c6, c7, c8, c9, co, c10, c11, m1, m2, m3, m4,
      m5, m6, m7, m8, m9, m10⟩ :=
    createStep_child hfork hglam hst hstatic hinit hbal hnonce hdepth haddr hdeploy hgas
  refine ⟨hrun', caller, msg, resumeCreate fork caller 0 address, ?_, ?_⟩
  · rw [step_of_messageInstruction (by rw [hc, hpc]; exact hlt)
      (by simp only [hc, hpc, hbyte]; exact decoded) hnone hrun]
    exact hstep
  · intro child hchild hcallee
    have hlen : caller.stack.val.length < STACK_LIMIT := by
      have := evm.stack.property
      rw [hst] at this
      rw [c5]
      cases create2 <;> simp at this <;> omega
    obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11⟩ :=
      resumeCreate_eq (child := child) (address := address) hlen
    refine .inl ⟨after, hres, caller, msg, child, hcallee, hchild, c10, c11, m1, m2, m3, m4, m5,
      m6, m7, m8, m9, m10, ?_⟩
    exact ⟨by rw [a1, c1, hc], by rw [a2, c2, hj], by rw [a3, c3], by rw [a4, c4, hpc],
      by rw [a5, c5], by rw [a6, c6], by rw [a7, c7], by rw [a8, c8, hrun'], by rw [a9, c9, herr],
      by rw [ao, co, hout], a10, a11⟩

/-- From Berlin to before Glamsterdam, CREATE of the init code in memory.

The new address is the one that the specification derives from the sender and its nonce.

The rule holds for every frame that ends the message and meets the assumption.

The creator pushes the new address when that frame ends with no error, and 0 otherwise. -/
theorem createWith (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {value start size : U256} {rest : List U256} {address : Address}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf0)
    (hstatic : message.isStatic = false)
    (hinit : .shapella ≤ fork → size.toNat ≤ maxInitCodeSize fork)
    (hbal : value ≤ (state.getAccount message.currentTarget).balance)
    (hnonce : (state.getAccount message.currentTarget).nonce ≠ MAX_NONCE)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (haddr : creationAddress message.currentTarget (state.getAccount message.currentTarget).nonce
      none
      (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
        start.toNat size.toNat) = .ok address)
    (hdeploy : state.accountDeployable address = true)
    (hgas : createBaseCost fork +
        (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
      (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    HoareUnder fork callee
      (At code message pc (value :: start :: size :: rest)
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        ((state.recordAccountRead message.currentTarget).recordAccountRead address).incrementNonce
          fork message.currentTarget = .ok caller.state ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert address } ∧
        msg.gas = createMessageGas fork (gas - (createBaseCost fork +
            (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
          (extendMemory memory.size [(start, size)]).cost)) ∧
        msg.caller = message.currentTarget ∧ msg.target = none ∧ msg.currentTarget = address ∧
        msg.codeAddress = none ∧
        msg.code = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(start, size)]).expandBy) start.toNat size.toNat ∧
        msg.data = .empty ∧ msg.value = value ∧ msg.depth = message.depth + 1 ∧
        msg.isStatic = false ∧
        At code message (pc + 1) ((if child.error.isNone then address.toU256 else 0) :: rest)
          (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          (gas - (createBaseCost fork +
              (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
            (extendMemory memory.size [(start, size)]).cost) -
            createMessageGas fork (gas - (createBaseCost fork +
              (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
            (extendMemory memory.size [(start, size)]).cost)) + child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after :=
  createKindWith (create2 := false) (salt := 0) hfork hglam hlt hbyte
    (ofByte_of_decode (op := .create) rfl (Fork.frontier_le _)) instruction_create
    messageInstruction_create hstatic hinit hbal hnonce hdepth haddr hdeploy hgas

/-- From Berlin to before Glamsterdam, CREATE2 with the salt `salt`, of the init code in memory.

The new address is the one that the specification derives from the sender, the salt and the code.

The rule holds for every frame that ends the message and meets the assumption.

The creator pushes the new address when that frame ends with no error, and 0 otherwise. -/
theorem create2With (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {value start size salt : U256} {rest : List U256} {address : Address}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf5)
    (hstatic : message.isStatic = false)
    (hinit : .shapella ≤ fork → size.toNat ≤ maxInitCodeSize fork)
    (hbal : value ≤ (state.getAccount message.currentTarget).balance)
    (hnonce : (state.getAccount message.currentTarget).nonce ≠ MAX_NONCE)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (haddr : creationAddress message.currentTarget (state.getAccount message.currentTarget).nonce
      (some salt)
      (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
        start.toNat size.toNat) = .ok address)
    (hdeploy : state.accountDeployable address = true)
    (hgas : createBaseCost fork +
        OPCODE_KECCAK256_PER_WORD * wordCount size.toNat +
        (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
      (extendMemory memory.size [(start, size)]).cost ≤ gas) :
    HoareUnder fork callee
      (At code message pc (value :: start :: size :: salt :: rest)
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧
        child.gas ≤ msg.gas ∧
        ((state.recordAccountRead message.currentTarget).recordAccountRead address).incrementNonce
          fork message.currentTarget = .ok caller.state ∧
        caller.substate = { substate with
          accessedAddresses := substate.accessedAddresses.insert address } ∧
        msg.gas = createMessageGas fork (gas - (createBaseCost fork +
            OPCODE_KECCAK256_PER_WORD * wordCount size.toNat +
            (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
          (extendMemory memory.size [(start, size)]).cost)) ∧
        msg.caller = message.currentTarget ∧ msg.target = none ∧ msg.currentTarget = address ∧
        msg.codeAddress = none ∧
        msg.code = memoryReadBytes (memoryExtend memory
          (extendMemory memory.size [(start, size)]).expandBy) start.toNat size.toNat ∧
        msg.data = .empty ∧ msg.value = value ∧ msg.depth = message.depth + 1 ∧
        msg.isStatic = false ∧
        At code message (pc + 1) ((if child.error.isNone then address.toU256 else 0) :: rest)
          (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          (gas - (createBaseCost fork +
              OPCODE_KECCAK256_PER_WORD * wordCount size.toNat +
              (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
            (extendMemory memory.size [(start, size)]).cost) -
            createMessageGas fork (gas - (createBaseCost fork +
              OPCODE_KECCAK256_PER_WORD * wordCount size.toNat +
              (if fork ≥ .shapella then initCodeCost size.toNat else 0) +
            (extendMemory memory.size [(start, size)]).cost)) + child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after :=
  createKindWith (create2 := true) hfork hglam hlt hbyte
    (ofByte_of_decode (op := .create2) rfl (Nat.le_trans (by decide) hfork)) instruction_create2
    (messageInstruction_create2 (Nat.le_trans (by decide) hfork)) hstatic hinit hbal hnonce hdepth
    haddr hdeploy hgas

end EthLib.Execution.Evm.Logic
