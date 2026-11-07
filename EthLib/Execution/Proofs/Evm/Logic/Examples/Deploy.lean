module

public import EthLib.Execution.Proofs.Evm.Logic.Deposit
public import EthLib.Execution.Proofs.Evm.Call.StaticStep
public import EthLib.Base.Proofs.Address

/-!
# Proofs: a contract that deploys a contract and reads the size of its code

This example composes the rule for CREATE, the deposit of code and the rule for EXTCODESIZE.

The init code `0x60016000f3` returns one byte of fresh memory, the byte 0.

- At 0, `60 01` pushes the size 1.
- At 2, `60 00` pushes the start 0.
- At 4, `f3` is RETURN.

It costs 9 gas: two pushes of 3, and the growth of memory to one word for 3.

The creator writes the init code to memory, creates a contract from it, and reads its code size.

- At 0, `64 60 01 60 00 f3` pushes the init code as a word.
- At 6, `60 00 52` writes that word at offset 0 of memory, so the init code is at offsets 27 to 31.
- At 9, `60 05 60 1b 60 00` pushes the size 5, the start 27 and the value 0.
- At 15, `f0` is CREATE.
- At 16, `3b` is EXTCODESIZE of the word that CREATE pushed.
- At 17, `60 00 52` writes that size at offset 0 of memory.
- At 20, `60 20 60 00 f3` returns those 32 bytes.

The assumption on the creation asks for a message with at least 209 gas.

That is the 9 gas of the init code and the 200 gas of the deposit of one byte.

The runner of the interpreter meets that assumption.

The rules are those of one counter of gas, from Berlin to the fork before Glamsterdam.

The frame of the creator may change the state, and its nonce is below the greatest.

Its depth leaves room for one more frame.

The new address is the one that CREATE derives, and it holds no code and a nonce of 0.

With at least 32344 gas, the creator then stops with no error and returns the word 1.

Or the run aborts.

When it returns, the new account holds the code of that byte.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.Deploy

open EthLib.Base (Address Fork U256 toAddressMasked toAddressMasked_toU256)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- The init code: it returns one byte of fresh memory. -/
def INIT : ByteArray := ⟨#[0x60, 0x01, 0x60, 0x00, 0xf3]⟩

/-- The code that the init code deploys: the byte 0. -/
def DEPLOYED : ByteArray := ⟨#[0x00]⟩

/-- The bytecode of the creator. -/
def CODE : ByteArray := ⟨#[0x64, 0x60, 0x01, 0x60, 0x00, 0xf3, 0x60, 0x00, 0x52, 0x60, 0x05,
  0x60, 0x1b, 0x60, 0x00, 0xf0, 0x3b, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]⟩

/-- The memory of the creator after its first MSTORE: the init code ends the word at offset 0. -/
def MEMORY : ByteArray := memoryWrite (memoryExtend .empty 32) 0 (wordBytes 0x60016000f3)

/-! ## The init code -/

/-- What a run of the init code ends with, for a message `message`.

It halts normally, returns the byte 0, and keeps its message, its state and its substate. -/
def Returned (message : Message fork) (gas : Nat) (state : TransactionState) (substate : Substate)
    (evm : Evm fork Nat) : Prop :=
  Halted false DEPLOYED gas state substate evm ∧ evm.message = message

variable {message : Message fork} {state : TransactionState} {substate : Substate}

/-- The RETURN of the init code stops the frame with the byte 0, for the growth of memory.

The frame keeps its message, which the rule for RETURN does not state, so this runs the step. -/
theorem returnInit {gas : Nat} (hgas : 3 ≤ gas) :
    Spec fork (At INIT message 4 [0, 1] .empty gas state substate)
      (Returned message (gas - 3) state substate) := by
  -- Memory grows from no word to one word, for 3 gas.
  have hext : extendMemory ByteArray.empty.size [((0 : U256), (1 : U256))] = ⟨3, 32⟩ := by
    decide
  have hread : memoryReadBytes (memoryExtend .empty 32) (0 : U256).toNat (1 : U256).toNat =
      DEPLOYED := by
    decide
  apply At.rule (by decide) rfl (ofByte_of_decode (op := .«return») rfl (Fork.frontier_le _))
    instruction_return
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [returnStep_cons hst]
  dsimp only
  rw [hmem, hg, hext, charge_nat hgas]
  exact ⟨_, rfl, rfl, ⟨rfl, herr, hread, rfl, hs, hss⟩, hm⟩

/-- The specification of the init code: with at least 9 gas, it returns the byte 0.

It keeps 9 gas less, its message, its state and its substate. -/
theorem specInit {gas : Nat} (hgas : 9 ≤ gas) :
    Spec fork (At INIT message 0 [] .empty gas state substate)
      (Returned message (gas - 9) state substate) := by
  have p1 := push1 (code := INIT) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas)
    (byte := 0x01) (by decide) rfl rfl (by omega) (by decide)
  have p2 := push1 (code := INIT) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 2) (stack := [1]) (memory := .empty) (gas := gas - 3)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have r := returnInit (fork := fork) (message := message) (state := state)
    (substate := substate) (gas := gas - 3 - 3) (by omega)
  have hsum : gas - 3 - 3 - 3 = gas - 9 := by omega
  rw [hsum] at r
  exact Spec.seq (p1.seq p2) r

/-! ## The creator -/

/-- The code writes the init code to memory and pushes the operands of CREATE, for 21 gas. -/
theorem operands {gas : Nat} (hgas : 21 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 15 [0, 27, 5] MEMORY (gas - 21) state substate) := by
  have h1 := Logic.push (fork := fork) (code := CODE) (message := message) (pc := 0)
    (stack := []) (memory := .empty) (gas := gas) (state := state) (substate := substate) (n := 5)
    (word := 0x60016000f3) (by decide) (by decide) rfl rfl (by decide) (by omega) (by decide)
  have h2 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 6) (stack := [0x60016000f3]) (memory := .empty)
    (gas := gas - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  -- Memory grows from no word to one word, for 3 gas.
  have hext : extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have h3 := Logic.mstore (fork := fork) (code := CODE) (message := message) (pc := 8)
    (start := 0) (value := 0x60016000f3) (rest := []) (memory := .empty) (gas := gas - 3 - 3)
    (state := state) (substate := substate) (by decide) rfl (by rw [hext]; dsimp only; omega)
  rw [hext] at h3
  have h4 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 9) (stack := []) (memory := MEMORY)
    (gas := gas - 3 - 3 - (3 + 3)) (byte := 0x05) (by decide) rfl rfl (by omega) (by decide)
  have h5 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 11) (stack := [5]) (memory := MEMORY)
    (gas := gas - 3 - 3 - (3 + 3) - 3) (byte := 0x1b) (by decide) rfl rfl (by omega) (by decide)
  have h6 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 13) (stack := [27, 5]) (memory := MEMORY)
    (gas := gas - 3 - 3 - (3 + 3) - 3 - 3) (byte := 0x00) (by decide) rfl rfl (by omega)
    (by decide)
  have hg : gas - 3 - 3 - (3 + 3) - 3 - 3 - 3 = gas - 21 := by omega
  have h := ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6
  rw [hg] at h
  exact h

/-- Memory holds the init code at offsets 27 to 31, so CREATE grows nothing. -/
theorem extendMemory_init :
    extendMemory MEMORY.size [((27 : U256), (5 : U256))] = ⟨0, 0⟩ := by
  decide

/-- The init code that CREATE reads from memory. -/
theorem memoryReadBytes_init :
    memoryReadBytes
      (memoryExtend MEMORY (extendMemory MEMORY.size [((27 : U256), (5 : U256))]).expandBy)
      (27 : U256).toNat (5 : U256).toNat = INIT := by
  decide

/-- Before Glamsterdam, the creation of the 5 bytes of init code costs at most 32002.

That is 32000, and from Shanghai 2 gas for the word of init code. -/
theorem createPrice_le (hglam : fork < .glamsterdam) :
    createBaseCost fork + (if fork ≥ .shapella then initCodeCost (5 : U256).toNat else 0) ≤
      32002 := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  split <;> simp [createBaseCost, hng, OPCODE_CREATE_BASE, initCodeCost, CODE_INIT_PER_WORD,
    wordCount, ceil32, WORD_BYTES]

/-- From Berlin to before Glamsterdam, the code after CREATE returns the code size at the word.

It reads that size, writes it to memory and returns it.

The address of the word is warm, and its account holds the code `c`.

It costs 112 gas. -/
theorem finish (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {word : U256}
    {c : ByteArray} {gas : Nat}
    (hcode : state.getCode (state.getAccount (toAddressMasked word)).codeHash = .ok c)
    (hwarm : decide (toAddressMasked word ∉ substate.accessedAddresses) = false)
    (hgas : 112 ≤ gas) :
    Spec fork (At CODE message 16 [word] MEMORY gas state substate)
      (Halted false (wordBytes (BitVec.ofNat 256 c.size)) (gas - 112)
        (state.recordAccountRead (toAddressMasked word))
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked word) }) := by
  have h1 := extcodesize (fork := fork) (code := CODE) (message := message) (pc := 16)
    (memory := MEMORY) (gas := gas) (state := state) (substate := substate) (rest := [])
    hfork hglam (by decide) rfl hcode hwarm (by simp only [Bool.false_eq_true, ite_false]; omega)
  simp only [Bool.false_eq_true, ite_false] at h1
  have h2 := push1 (code := CODE) (fork := fork) (message := message)
    (state := state.recordAccountRead (toAddressMasked word))
    (substate := { substate with
      accessedAddresses := substate.accessedAddresses.insert (toAddressMasked word) })
    (pc := 17) (stack := [BitVec.ofNat 256 c.size]) (memory := MEMORY) (gas := gas - 100)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  -- Memory already holds one word, so it does not grow.
  have hext : extendMemory MEMORY.size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    decide
  have h3 := Logic.mstore (fork := fork) (code := CODE) (message := message) (pc := 19)
    (start := 0) (value := BitVec.ofNat 256 c.size) (rest := []) (memory := MEMORY)
    (gas := gas - 100 - 3) (state := state.recordAccountRead (toAddressMasked word))
    (substate := { substate with
      accessedAddresses := substate.accessedAddresses.insert (toAddressMasked word) })
    (by decide) rfl (by rw [hext]; dsimp only; omega)
  have hwrite : memoryWrite (memoryExtend MEMORY (extendMemory MEMORY.size
      [((0 : U256), (32 : U256))]).expandBy) (0 : U256).toNat
      (wordBytes (BitVec.ofNat 256 c.size)) = wordBytes (BitVec.ofNat 256 c.size) := by
    rw [hext, memoryExtend_zero]
    exact memoryWrite_whole (by rw [size_wordBytes]; decide)
  rw [hwrite, hext] at h3
  have h4 := push1 (code := CODE) (fork := fork) (message := message)
    (state := state.recordAccountRead (toAddressMasked word))
    (substate := { substate with
      accessedAddresses := substate.accessedAddresses.insert (toAddressMasked word) })
    (pc := 20) (stack := []) (memory := wordBytes (BitVec.ofNat 256 c.size))
    (gas := gas - 100 - 3 - (3 + 0)) (byte := 0x20) (by decide) rfl rfl (by omega) (by decide)
  have h5 := push1 (code := CODE) (fork := fork) (message := message)
    (state := state.recordAccountRead (toAddressMasked word))
    (substate := { substate with
      accessedAddresses := substate.accessedAddresses.insert (toAddressMasked word) })
    (pc := 22) (stack := [32]) (memory := wordBytes (BitVec.ofNat 256 c.size))
    (gas := gas - 100 - 3 - (3 + 0) - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  -- Memory already holds the word, so RETURN grows nothing.
  have hext' : extendMemory (wordBytes (BitVec.ofNat 256 c.size)).size
      [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_wordBytes]
    decide
  have h6 := Logic.«return» (fork := fork) (code := CODE) (message := message) (pc := 24)
    (start := 0) (size := 32) (rest := []) (memory := wordBytes (BitVec.ofNat 256 c.size))
    (gas := gas - 100 - 3 - (3 + 0) - 3 - 3)
    (state := state.recordAccountRead (toAddressMasked word))
    (substate := { substate with
      accessedAddresses := substate.accessedAddresses.insert (toAddressMasked word) })
    (by decide) rfl (by rw [hext']; exact Nat.zero_le _)
  have hread : memoryReadBytes (memoryExtend (wordBytes (BitVec.ofNat 256 c.size)) 0)
      (0 : U256).toNat (32 : U256).toNat = wordBytes (BitVec.ofNat 256 c.size) := by
    rw [memoryExtend_zero]
    have := memoryReadBytes_whole (memory := wordBytes (BitVec.ofNat 256 c.size))
    rwa [size_wordBytes] at this
  rw [hext'] at h6
  have hg : gas - 100 - 3 - (3 + 0) - 3 - 3 - 0 = gas - 112 := by omega
  exact Spec.seq ((((h1.seq h2).seq h3).seq h4).seq h5) (h6.consequence (fun _ hp => hp)
    fun _ hq => by
      rw [hread, hg] at hq
      exact hq)

/-! ## The creation, through the runner of the interpreter -/

/-- The assumption that the creation runs the init code, as its specification says.

The frame that ends the creation is the deposit of the frame that ends the init code. -/
abbrev Creates : Evm fork Nat → Message fork → Evm fork Nat → Prop :=
  CreatesAs INIT (fun message _ _ => 209 ≤ message.gas) fun message state substate =>
    Returned message (message.gas - 9) (startState fork message state) substate

/-- The runner of the interpreter meets the assumption, for every bound. -/
theorem meets (bound : Nat) : Meets (Creates (fork := fork)) (processRunner fork bound) :=
  meets_of_spec_create (fun _ _ _ _ hg => specInit (by omega)) bound

/-- What the run ends with: no error, the word 1, and the code of the byte 0 at the address. -/
def Deployed (address : Address) (evm : Evm fork Nat) : Prop :=
  evm.error = none ∧ evm.output = wordBytes 1 ∧
    evm.state.getCode (evm.state.getAccount address).codeHash = .ok DEPLOYED

/-- The specification of the creator, under the assumption that the creation deposits the byte.

It holds from Berlin to before Glamsterdam.

The frame may change the state, its nonce is below the greatest, and its depth leaves room.

The new address is the one that the specification derives from the current account and its nonce.

It holds no code and a nonce of 0, and the frame has at least 32344 gas. -/
theorem spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hnonce : (state.getAccount message.currentTarget).nonce ≠ MAX_NONCE)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {address : Address}
    (haddr : creationAddress message.currentTarget (state.getAccount message.currentTarget).nonce
      none INIT = .ok address)
    (hdeploy : state.accountDeployable address = true) {gas : Nat} (hgas : 32344 ≤ gas) :
    SpecUnder fork Creates (At CODE message 0 [] .empty gas state substate)
      (Deployed address) := by
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hcost := createPrice_le hglam
  have hcreate := createWith (fork := fork) (code := CODE) (message := message) (pc := 15)
    (memory := MEMORY) (gas := gas - 21) (state := state) (substate := substate)
    (callee := Creates) (value := 0) (start := 27) (size := 5) (rest := []) (address := address)
    hfork hglam (by decide) rfl hstatic (fun _ => by unfold maxInitCodeSize; split <;> decide)
    (by simp [BitVec.le_def]) hnonce hdepth (by rw [memoryReadBytes_init]; exact haddr) hdeploy
    (by rw [extendMemory_init]; dsimp only; omega)
  refine SpecUnder.seq (HoareUnder.of_hoare (operands (by omega))) (HoareUnder.seq hcreate ?_)
  apply HoareUnder.of_hoare
  rintro evm ⟨caller, msg, child, hcallee, -, -, hcss, hmg, -, hmt, hmtg, hmca, hmcode, -, hmv, -,
    -, hat⟩
  rw [extendMemory_init] at hmg hat
  dsimp only at hmg hat
  have hmsg : 209 ≤ msg.gas := by
    rw [hmg, createMessageGas_of_tangerineWhistle htw]
    omega
  obtain ⟨prepared, hprep⟩ : ∃ prepared,
      prepareCreation fork caller.state msg.currentTarget = .ok prepared := by
    obtain ⟨prepared, hp⟩ := State.TransactionState.incrementNonce_isOk fork
      ((caller.state.destroyStorage msg.currentTarget).markAccountCreated msg.currentTarget)
      msg.currentTarget
    exact ⟨prepared, by simp [prepareCreation, hsd, hp, Except.mapError]⟩
  obtain ⟨stopped, ⟨⟨-, hserr, hsout, hsgas, -, hsss⟩, hsm⟩, hdep⟩ :=
    hcallee (by rw [hmcode, memoryReadBytes_init]) hmt (by simp [hmv])
      (by simp [precompileAddress, hmca]) prepared hprep hmsg
  have herr : stopped.error = none := by simpa using hserr
  have hsize : stopped.output.size = 1 := by rw [hsout]; rfl
  rw [rollbackOnError_of_error_eq_none herr] at hdep
  obtain ⟨state', hset, hdep'⟩ := depositCode_of_ok (snapshot := caller.state) hfork hglam herr
    (fun _ => by rw [hsout]; decide) (by rw [hsize]; decide)
    (by rw [hsize, hsgas]; simp only [CODE_DEPOSIT_PER_BYTE]; omega)
  cases hdep.symm.trans hdep'
  rw [hsm, hmtg, hsout] at hset
  have hne : Cryptography.Hash.Keccak.keccak256 DEPLOYED ≠ State.EMPTY_CODE_HASH := by
    unfold State.EMPTY_CODE_HASH DEPLOYED
    decide +kernel
  have hcodeAt : state'.getCode (state'.getAccount address).codeHash = .ok DEPLOYED := by
    rw [(State.TransactionState.getAccount_setCode hset).1]
    exact State.TransactionState.getCode_setCode_self hset hne
  have hwarm : decide (toAddressMasked address.toU256 ∉
      (incorporateChild fork caller { stopped with
        gas := stopped.gas - stopped.output.size * CODE_DEPOSIT_PER_BYTE,
        state := state' }).substate.accessedAddresses) = false := by
    simp [toAddressMasked_toU256, incorporateChild, herr, hsss, Substate.child, hcss]
  simp only [herr, Option.isNone_none, ite_true, memoryExtend_zero, state_incorporateChild]
    at hat hwarm
  have hleft : 112 ≤ gas - 21 - (createBaseCost fork +
      (if fork ≥ .shapella then initCodeCost (5 : U256).toNat else 0) + 0) -
      createMessageGas fork (gas - 21 - (createBaseCost fork +
        (if fork ≥ .shapella then initCodeCost (5 : U256).toNat else 0) + 0)) +
      (stopped.gas - stopped.output.size * CODE_DEPOSIT_PER_BYTE) := by
    rw [hsize, hsgas, hmg, createMessageGas_of_tangerineWhistle htw]
    simp only [CODE_DEPOSIT_PER_BYTE]
    omega
  obtain ⟨ended, hreach, halted, hq⟩ := finish (word := address.toU256) (c := DEPLOYED)
    hfork hglam (by rw [toAddressMasked_toU256]; exact hcodeAt) hwarm hleft evm hat
  refine ⟨ended, hreach, halted, hq.2.1, by rw [hq.2.2.1]; rfl, ?_⟩
  rw [hq.2.2.2.2.1, toAddressMasked_toU256]
  exact hcodeAt

/-- The loop of the interpreter runs the creator to its specification, or the run aborts.

It holds from Berlin to before Glamsterdam, with at least 32344 gas.

With the runner of messages of the interpreter, the creator stops with no error and returns 1.

The new account then holds the code of the byte 0.

The run aborts only when the runner fails on the message, with an error that aborts the run. -/
theorem runFrame_process (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hnonce : (state.getAccount message.currentTarget).nonce ≠ MAX_NONCE)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) {address : Address}
    (haddr : creationAddress message.currentTarget (state.getAccount message.currentTarget).nonce
      none INIT = .ok address)
    (hdeploy : state.accountDeployable address = true) {gas : Nat} (hgas : 32344 ≤ gas)
    {bound : Nat} {evm : Evm fork Nat} (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok stopped ∧ Deployed address stopped) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm within =
      .error e ∧ e.aborts = true :=
  (spec hfork hglam hstatic hnonce hdepth haddr hdeploy hgas).runFrame (meets bound) start within

end EthLib.Execution.Evm.Logic.Deploy
