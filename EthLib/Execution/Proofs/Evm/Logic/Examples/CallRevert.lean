module

public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Evm.Logic.Examples.CallEcho
public import EthLib.Execution.Proofs.Evm.Instructions.Storage
public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: a contract that calls a callee that writes its storage and then reverts

This example proves a call to a callee that reverts, with the runner of the interpreter.

The callee writes a word of its storage, then reverts with a word as its output.

- At 0, `60 01 60 00 55` writes 1 to the slot at key 0 of the current account.
- At 5, `60 2a 60 00 52` writes the word 42 at offset 0 of memory.
- At 10, `60 20 60 00 fd` reverts with those 32 bytes, by EIP-140 from Byzantium.

The caller calls the address in the first word of its call data, with no value and no input.

- At 0, `60 20 60 00 60 00 60 00 60 00` pushes an output range of 32 bytes at 0, and no input.
- At 10, `60 00 35` reads the address, the word of call data at offset 0.
- At 13, `61 ff ff f1` asks to pass on 65535 gas and calls.
- At 17, `60 20 52` writes the word that CALL pushes at offset 32 of memory.
- At 20, `60 40 60 00 f3` returns the 64 bytes of memory from offset 0.

The caller then returns the word 42, then the word 0, or the run aborts.

Every word of storage then reads as before the call.

The address holds the code of the callee and is no precompile, and the frame may change the state.

Its depth leaves room for one more frame, and it holds the gas of the run.

Nothing is stated of the gas that the callee leaves.

The rules are those of one counter of gas, from Berlin to the fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.CallRevert

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution.State (TransactionState EMPTY_ACCOUNT)
open GasCosts

variable {fork : Fork}

/-- The bytecode of the callee, which writes a word of its storage and then reverts. -/
def REVERTER : ByteArray := ⟨#[0x60, 0x01, 0x60, 0x00, 0x55, 0x60, 0x2a, 0x60, 0x00, 0x52, 0x60,
  0x20, 0x60, 0x00, 0xfd]⟩

/-- The bytecode of the caller. -/
def CODE : ByteArray := ⟨#[0x60, 0x20, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00,
  0x35, 0x61, 0xff, 0xff, 0xf1, 0x60, 0x20, 0x52, 0x60, 0x40, 0x60, 0x00, 0xf3]⟩

/-- The address that the caller calls: the first word of its call data. -/
def target (data : ByteArray) : U256 := loadWord data 0 32

/-- The gas that the callee needs: 24, a cold access and the price to fill a slot. -/
def CALLEE_GAS : Nat := 24 + COLD_STORAGE_ACCESS + STORAGE_SET

/-- The callee reverts with the word 42, in a state of the same block.

The frame may change the state, has the account of the current address, and holds the gas. -/
theorem reverter (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {message : Message fork}
    {state : TransactionState} {substate : Substate} (hstatic : message.isStatic = false)
    (hacc : (state.getAccountOptional message.currentTarget).isSome) {gas : Nat}
    (hgas : CALLEE_GAS ≤ gas) :
    Spec fork (At REVERTER message 0 [] .empty gas state substate) fun evm =>
      evm.error = some .revert ∧ evm.output = wordBytes 42 ∧ evm.state.parent = state.parent := by
  have hW := sstoreCost_le hfork hglam
    (state.getStorageOriginal message.currentTarget
      (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat)))
    (state.getStorage message.currentTarget (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat)))
    (BitVec.ofNat 256 (1 : UInt8).toNat)
    (decide (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat) ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅))
  simp only [CALLEE_GAS, COLD_STORAGE_ACCESS, STORAGE_SET] at hgas hW
  -- The write succeeds, since the current address has an account.
  cases hset : (state.recordStorageRead message.currentTarget
      (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat))).setStorage message.currentTarget
      (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat)) (BitVec.ofNat 256 (1 : UInt8).toNat)
    with
  | error e =>
    obtain ⟨hnone, -⟩ := (TransactionState.setStorage_eq_error_iff _ _ _ _ _).mp hset
    rw [show (state.recordStorageRead message.currentTarget
      (U256.toBeBytes (BitVec.ofNat 256 (0 : UInt8).toNat))).getAccountOptional
        message.currentTarget = state.getAccountOptional message.currentTarget from rfl] at hnone
    simp [hnone] at hacc
  | ok state' =>
  have h1 := push1 (code := REVERTER) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas) (byte := 0x01)
    (by decide) rfl rfl (by omega) (by decide)
  have h2 := push1 (code := REVERTER) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 2) (stack := [BitVec.ofNat 256 (1 : UInt8).toNat])
    (memory := .empty) (gas := gas - 3) (byte := 0x00) (by decide) rfl rfl (by omega)
    (by simp [STACK_LIMIT])
  have h3 := sstore (fork := fork) (code := REVERTER) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 4)
    (key := BitVec.ofNat 256 (0 : UInt8).toNat) (new := BitVec.ofNat 256 (1 : UInt8).toNat)
    (rest := []) (gas := gas - 3 - 3) (state' := state') hfork hglam (by decide) rfl hstatic rfl
    (by simp only [CALL_STIPEND]; omega) (by omega) hset
  generalize hG : gas - 3 - 3 - sstoreCost fork _ _ _ _ = G at h3
  have hG' : 18 ≤ G := by omega
  generalize hss : ({ substate with accessedStorageKeys := _, refundCounter := _ } : Substate) =
    ss at h3
  have h4 := push1 (code := REVERTER) (fork := fork) (message := message) (state := state')
    (substate := ss) (pc := 5) (stack := []) (memory := .empty) (gas := G) (byte := 0x2a)
    (by decide) rfl rfl (by omega) (by decide)
  have h5 := push1 (code := REVERTER) (fork := fork) (message := message) (state := state')
    (substate := ss) (pc := 7) (stack := [BitVec.ofNat 256 (0x2a : UInt8).toNat])
    (memory := .empty) (gas := G - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have hext : extendMemory ByteArray.empty.size
      [((BitVec.ofNat 256 (0 : UInt8).toNat : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have h6 := Logic.mstore (fork := fork) (code := REVERTER) (message := message) (pc := 9)
    (start := BitVec.ofNat 256 (0 : UInt8).toNat) (value := BitVec.ofNat 256 (0x2a : UInt8).toNat)
    (rest := []) (memory := .empty) (gas := G - 3 - 3) (state := state') (substate := ss)
    (by decide) rfl (by simp only [hext]; omega)
  have h0 : (BitVec.ofNat 256 (0 : UInt8).toNat : U256).toNat = 0 := rfl
  have h42 : (BitVec.ofNat 256 (0x2a : UInt8).toNat : U256) = 42 := rfl
  rw [hext, h0, h42, CallFlag.memoryWrite_word] at h6
  have h7 := push1 (code := REVERTER) (fork := fork) (message := message) (state := state')
    (substate := ss) (pc := 10) (stack := []) (memory := wordBytes 42) (gas := G - 3 - 3 - (3 + 3))
    (byte := 0x20) (by decide) rfl rfl (by omega) (by decide)
  have h8 := push1 (code := REVERTER) (fork := fork) (message := message) (state := state')
    (substate := ss) (pc := 12) (stack := [32]) (memory := wordBytes 42)
    (gas := G - 3 - 3 - (3 + 3) - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have hext' : extendMemory (wordBytes 42).size [((0 : U256), (32 : U256))] = ⟨0, 0⟩ := by
    rw [size_wordBytes]
    decide
  have h9 := Logic.revert (fork := fork) (code := REVERTER) (message := message) (pc := 14)
    (start := 0) (size := 32) (rest := []) (memory := wordBytes 42)
    (gas := G - 3 - 3 - (3 + 3) - 3 - 3) (state := state') (substate := ss)
    (Nat.le_trans (by decide) hfork) (by decide) rfl (by rw [hext']; exact Nat.zero_le _)
  rw [hext'] at h9
  have hread : memoryReadBytes (memoryExtend (wordBytes 42) 0) (0 : U256).toNat
      (32 : U256).toNat = wordBytes 42 := by
    rw [memoryExtend_zero]
    exact CallEcho.memoryReadBytes_wordBytes _
  have hparent : state'.parent = state.parent := by
    have h := TransactionState.parent_setStorage hset
    exact h
  exact Spec.seq (((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8)
    (h9.consequence (fun _ hp => hp) fun _ ⟨_, he, ho, _, hs, _⟩ =>
      ⟨he, by rw [ho, hread], by rw [hs, hparent]⟩)

/-- The assumption that a call to the code of the callee reverts with the word 42.

The message may change the state, its current address has an account, and it holds the gas.

The frame that ends it is in a state of the same block as the caller. -/
abbrev Callee : Evm fork Nat → Message fork → Evm fork Nat → Prop :=
  RunsAs REVERTER
    (fun message state _ => message.isStatic = false ∧
      (state.getAccountOptional message.currentTarget).isSome ∧ CALLEE_GAS ≤ message.gas)
    fun _ state _ evm =>
      evm.error = some .revert ∧ evm.output = wordBytes 42 ∧ evm.state.parent = state.parent

/-- The runner of the interpreter meets the assumption, for every bound. -/
theorem meets (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) (bound : Nat) :
    Meets (Callee (fork := fork)) (processRunner fork bound) :=
  meets_of_spec (fun message state _ _ ⟨hstatic, hacc, hgas⟩ => by
    have hstart : (startState fork message state).parent = state.parent := by
      unfold startState
      split
      · exact TransactionState.parent_touchAccount _ _
      · rfl
    have hacc' : ((startState fork message state).getAccountOptional
        message.currentTarget).isSome := by
      unfold startState
      split
      · exact TransactionState.isSome_getAccountOptional_touchAccount _ _
      · exact hacc
    exact (reverter hfork hglam hstatic hacc' hgas).consequence (fun _ hp => hp)
      fun _ ⟨he, ho, hp⟩ => ⟨he, ho, hp.trans hstart⟩) bound

variable {message : Message fork} {state : TransactionState} {substate : Substate}

/-- The caller pushes the operands of CALL, for 24 gas. -/
theorem operands {gas : Nat} (hgas : 24 ≤ gas) :
    Hoare fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 16 [65535, target message.data, 0, 0, 0, 0, 32] .empty (gas - 24) state
        substate) := by
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 0) (stack := []) (memory := .empty) (gas := gas) (byte := 0x20)
    (by decide) rfl rfl (by omega) (by decide)
  have h2 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 2) (stack := [32]) (memory := .empty) (gas := gas - 3)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h3 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 4) (stack := [0, 32]) (memory := .empty) (gas := gas - 3 - 3)
    (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h4 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 6) (stack := [0, 0, 32]) (memory := .empty)
    (gas := gas - 3 - 3 - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h5 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 8) (stack := [0, 0, 0, 32]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h6 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 10) (stack := [0, 0, 0, 0, 32]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 3 - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have h7 := calldataload (fork := fork) (code := CODE) (message := message) (state := state)
    (substate := substate) (memory := .empty) (pc := 12) (start := 0) (rest := [0, 0, 0, 0, 32])
    (gas := gas - 3 - 3 - 3 - 3 - 3 - 3) (by decide) rfl (by omega)
  have h8 := Logic.push (fork := fork) (code := CODE) (message := message) (pc := 13)
    (stack := [loadWord message.data 0 32, 0, 0, 0, 0, 32]) (memory := .empty)
    (gas := gas - 3 - 3 - 3 - 3 - 3 - 3 - 3) (state := state) (substate := substate) (n := 2)
    (word := 65535) (by decide) (by decide) rfl rfl (by decide) (by omega) (by simp [STACK_LIMIT])
  have hg : gas - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 = gas - 24 := by omega
  have h := (((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8)
  rw [hg] at h
  exact h

/-- After CALL, the caller writes the word it pushed after a word of memory, and returns both.

That takes 15 gas. -/
theorem finish {x flag : U256} {gas : Nat} {state : TransactionState} {substate : Substate}
    (hgas : 15 ≤ gas) :
    Spec fork (At CODE message 17 [flag] (wordBytes x) gas state substate)
      (Halted false (wordBytes x ++ wordBytes flag) (gas - 15) state substate) := by
  have h1 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 17) (stack := [flag]) (memory := wordBytes x) (gas := gas)
    (byte := 0x20) (by decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have hg1 : extendMemory (wordBytes x).size [((32 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    rw [size_wordBytes]
    decide
  have h2 := Logic.mstore (fork := fork) (code := CODE) (message := message) (pc := 19)
    (start := 32) (value := flag) (rest := []) (memory := wordBytes x) (gas := gas - 3)
    (state := state) (substate := substate) (by decide) rfl (by rw [hg1]; simp only; omega)
  have hm : memoryWrite (memoryExtend (wordBytes x)
      (extendMemory (wordBytes x).size [((32 : U256), (32 : U256))]).expandBy)
      (32 : U256).toNat (wordBytes flag) = wordBytes x ++ wordBytes flag := by
    rw [hg1]
    have h := memoryWrite_extend_end (memory := wordBytes x) (value := wordBytes flag)
    rw [size_wordBytes, size_wordBytes] at h
    exact h
  have h2' := Hoare.memory_eq h2 hm
  rw [hg1] at h2'
  dsimp only at h2'
  have hs : (wordBytes x ++ wordBytes flag).size = 64 := by simp [size_wordBytes]
  have h3 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 20) (stack := []) (memory := wordBytes x ++ wordBytes flag)
    (gas := gas - 3 - (3 + 3)) (byte := 0x40) (by decide) rfl rfl (by omega) (by decide)
  have h4 := push1 (code := CODE) (fork := fork) (message := message) (state := state)
    (substate := substate) (pc := 22) (stack := [64]) (memory := wordBytes x ++ wordBytes flag)
    (gas := gas - 3 - (3 + 3) - 3) (byte := 0x00) (by decide) rfl rfl (by omega) (by decide)
  have hext : extendMemory (wordBytes x ++ wordBytes flag).size [((0 : U256), (64 : U256))] =
      ⟨0, 0⟩ := by
    rw [hs]
    decide
  have h5 := Logic.«return» (fork := fork) (code := CODE) (message := message) (pc := 24)
    (start := 0) (size := 64) (rest := []) (memory := wordBytes x ++ wordBytes flag)
    (gas := gas - 3 - (3 + 3) - 3 - 3) (state := state) (substate := substate) (by decide) rfl
    (by rw [hext]; exact Nat.zero_le _)
  rw [hext, memoryExtend_zero] at h5
  have hread : memoryReadBytes (wordBytes x ++ wordBytes flag) (0 : U256).toNat
      (64 : U256).toNat = wordBytes x ++ wordBytes flag := by
    have h := memoryReadBytes_whole (memory := wordBytes x ++ wordBytes flag)
    rwa [hs] at h
  have hg : gas - 3 - (3 + 3) - 3 - 3 - 0 = gas - 15 := by omega
  exact Spec.seq ((h1.seq h2').seq h3 |>.seq h4)
    (h5.consequence (fun _ hp => hp) fun _ hq => by rw [hread, hg] at hq; exact hq)

/-- An address whose code is the code of the callee has an account. -/
theorem isSome_of_getCode {state : TransactionState} {address : Base.Address}
    (hcode : state.getCode (state.getAccount address).codeHash = .ok REVERTER) :
    (state.getAccountOptional address).isSome := by
  cases h : state.getAccountOptional address with
  | some _ => rfl
  | none =>
    have hempty : state.getAccount address = EMPTY_ACCOUNT := by
      simp [TransactionState.getAccount, h]
    rw [hempty] at hcode
    have hcode' : ByteArray.empty = REVERTER := by
      simpa [TransactionState.getCode, EMPTY_ACCOUNT] using hcode
    exact absurd (congrArg ByteArray.size hcode') (by decide)

/-- The caller returns the word 42, then the word 0, with the runner of the interpreter.

Every word of storage then reads as before the call.

The address in the first word of its call data holds the code of the callee and is no precompile.

The frame may change the state, its depth leaves room for one more frame, and it holds the gas.

Or the run aborts, when a runner fails with an error that aborts the run. -/
theorem runFrame_process (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {cold : Bool}
    (hcode : state.getCode
      (state.getAccount (toAddressMasked (target message.data))).codeHash = .ok REVERTER)
    (hprecompile : Precompiles.isPrecompile fork
      (toAddressMasked (target message.data)).toU256.toNat = false)
    (hstatic : message.isStatic = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked (target message.data) ∉ substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 27 + CallFlag.accessCost cold + 22475 ≤ gas) {bound : Nat}
    {evm : Evm fork Nat} (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok stopped ∧
      stopped.running = false ∧ stopped.error = none ∧
      stopped.output = wordBytes 42 ++ wordBytes 0 ∧
      ∀ address key, stopped.state.getStorage address key = state.getStorage address key) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .error e ∧ e.aborts = true := by
  have hacc : CallFlag.accessCost cold = if cold then 2600 else 100 := rfl
  have hext : extendMemory ByteArray.empty.size
      [((0 : U256), (0 : U256)), ((0 : U256), (32 : U256))] = ⟨3, 32⟩ := by
    decide
  have hcall := callWith (fork := fork) (code := CODE) (message := message) (pc := 16)
    (memory := .empty) (gas := gas - 24) (state := state) (substate := substate)
    (callee := Callee) (asked := 65535) (to := target message.data) (inputStart := 0)
    (inputSize := 0) (outputStart := 0) (outputSize := 32) (rest := []) hfork hglam (by decide)
    rfl hcode (fun _ => by decide) hdepth hcold
    (by rw [hext]; cases cold <;> simp only [CallFlag.accessCost, ite_true, Bool.false_eq_true,
      ite_false] at hgas ⊢ <;> omega)
  rw [hext] at hcall
  have h := SpecUnder.seq (HoareUnder.of_hoare (operands (by omega))) (HoareUnder.seq hcall
    (HoareUnder.of_hoare (Q := fun evm => evm.running = false ∧ evm.error = none ∧
      evm.output = wordBytes 42 ++ wordBytes 0 ∧
      ∀ address key, evm.state.getStorage address key = state.getStorage address key) ?_))
  · rcases h.runFrame (meets hfork hglam bound) start within with
      ⟨stopped, ran, herr, hout, hst⟩ | aborted
    · exact .inl ⟨stopped, ran, running_runFrame ran, herr, hout, hst⟩
    · exact .inr aborted
  rintro evm ⟨caller, msg, child, hcallee, -, hcs, -, hmg, -, hmt, hmtg, hmca, hmcode, -, hmv, -,
    hmst, hat⟩
  have hpre : precompileAddress fork msg = none := by
    simp [precompileAddress, hmca, hprecompile]
  have hsub : CALLEE_GAS ≤ msg.gas ∧ 15 ≤ gas - 24 - ((messageCallGas fork 0 (65535 : U256).toNat
      (gas - 24) 3 (if cold then 2600 else 100)).cost + 3) := by
    have htw : fork ≥ .tangerineWhistle := Nat.le_trans (by decide) hfork
    rw [hmg, show (65535 : U256).toNat = 65535 from rfl]
    simp only [CALLEE_GAS, COLD_STORAGE_ACCESS, STORAGE_SET]
    cases cold <;> simp only [CallFlag.accessCost, ite_true, Bool.false_eq_true, ite_false]
      at hgas ⊢ <;> rw [messageCallGas_of_le htw (by omega)] <;>
      simp only [maxMessageCallGas] <;> omega
  have hg : (caller.state.getAccountOptional msg.currentTarget).isSome := by
    rw [hcs, hmt]
    exact isSome_of_getCode hcode
  obtain ⟨ended, ⟨herr, hout, hparent⟩, hchild⟩ := hcallee hmcode (by simp [hmtg])
    (by simp [hmv]) hpre ⟨by rw [hmst, hstatic], hg, hsub.1⟩
  have hcerr : child.error = some .revert := by rw [hchild, rollbackOnError, herr]; rfl
  have hcout : child.output = wordBytes 42 := by rw [hchild, rollbackOnError, herr]; exact hout
  have hcst : child.state = ended.state.restoreTxState caller.state := by
    rw [hchild, rollbackOnError, herr]; rfl
  have hflag : (if child.error.isNone then (1 : U256) else 0) = 0 := by simp [hcerr]
  have hmem : memoryWrite (memoryExtend ByteArray.empty 32) (0 : U256).toNat
      (child.output.extract 0 (min (32 : U256).toNat child.output.size)) = wordBytes 42 := by
    rw [hcout, size_wordBytes, show (32 : U256).toNat = 32 from rfl, show min 32 32 = 32 from rfl]
    have he := ByteArray.extract_zero_size (b := wordBytes 42)
    rw [size_wordBytes] at he
    rw [he]
    exact CallFlag.memoryWrite_word _
  rw [hflag, hmem] at hat
  have hinc : (incorporateChild fork caller child).state = child.state := by
    unfold incorporateChild
    split <;> rfl
  obtain ⟨stopped, hreach, halted, hq⟩ := finish (fork := fork) (message := message) (x := 42)
    (flag := 0) (Nat.le_trans hsub.2 (Nat.le_add_right _ child.gas)) evm hat
  refine ⟨stopped, hreach, halted, hq.2.1, hq.2.2.1, fun address key => ?_⟩
  rw [hq.2.2.2.2.1, hinc, hcst, TransactionState.getStorage_restoreTxState hparent, hcs]
  simp

end EthLib.Execution.Evm.Logic.CallRevert
