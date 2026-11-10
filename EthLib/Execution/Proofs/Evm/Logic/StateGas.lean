module

public import EthLib.Execution.Proofs.Evm.Logic.Rules

/-!
# Proofs: storage writes with state gas

A one-counter frame pays execution gas and state gas from the same counter.

It ignores state-gas refills, so its gas is a conservative budget for the meter of EIP-8037.

The rules here charge both parts of SSTORE at every fork from Berlin.

Source: [EIP-8037, Gas accounting for SSTORE][eip8037-sstore].

[eip8037-sstore]: https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-sstore-opcode-level
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 Address Bytes32)
open GasCosts

/-- The total charge of a storage write when one counter pays both gas dimensions. -/
def sstoreTotalCost (fork : Fork) (original current new : U256) (cold : Bool) : Nat :=
  sstoreCost fork original current new cold + sstoreStateGas fork original current new

/-- A storage-write budget keeps its old value before Glamsterdam and grows fivefold after it. -/
def storageGasScale (fork : Fork) : Nat := if fork ≥ .glamsterdam then 5 else 1

/-- Scaling never lowers a gas budget. -/
theorem one_le_storageGasScale (fork : Fork) : 1 ≤ storageGasScale fork := by
  unfold storageGasScale
  split <;> decide

/-- The added storage-write budget is at most fivefold. -/
theorem storageGasScale_le (fork : Fork) : storageGasScale fork ≤ 5 := by
  unfold storageGasScale
  split <;> decide

/-- The storage-write budget is unchanged before Glamsterdam. -/
theorem storageGasScale_of_lt {fork : Fork} (h : fork < .glamsterdam) :
    storageGasScale fork = 1 := by
  have hn : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [storageGasScale, hn, ↓reduceIte]

/-- The combined write charge fits the scaled bound of 22,100 gas from Berlin. -/
theorem sstoreTotalCost_le {fork : Fork} (hfork : .berlin ≤ fork)
    (original current new : U256) (cold : Bool) :
    sstoreTotalCost fork original current new cold ≤ 22100 * storageGasScale fork := by
  by_cases hglam : fork ≥ .glamsterdam
  · have he : sstoreCost fork original current new cold ≤ 12100 := by
      rw [sstoreCost, ite_eq_left hglam]
      have hw : (if original = current ∧ current ≠ new then STORAGE_WRITE else 0) ≤ 10000 := by
        split <;> decide
      cases cold <;> simp only [Bool.false_eq_true, ↓reduceIte, COLD_STORAGE_ACCESS,
        WARM_ACCESS] <;> omega
    have hs : sstoreStateGas fork original current new ≤ 97920 := by
      unfold sstoreStateGas
      split <;> decide
    simp only [sstoreTotalCost, storageGasScale, hglam, ↓reduceIte, Nat.reduceMul]
    omega
  · have hcost := sstoreCost_le hfork (Nat.lt_of_not_ge hglam) original current new cold
    simpa [sstoreTotalCost, sstoreStateGas, storageGasScale, hglam,
      COLD_STORAGE_ACCESS, STORAGE_SET] using hcost

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- The step of SSTORE from Berlin, with one counter of gas, in a frame that may change the state.

It pops a key and a word, marks the slot of the current account accessed, and records its read.

It pays execution gas and state gas, from the original, current and new words and the cold flag.

It writes the word, and adds the refund of the write to the refund counter.

The frame keeps its output and its return data. -/
private theorem sstoreStep_eq_total (hfork : .berlin ≤ fork)
    {evm : Evm fork Nat} {key new : U256} {rest : List U256} {state' : State.TransactionState}
    (hst : evm.stack.val = key :: new :: rest) (hstatic : evm.message.isStatic = false)
    (hstipend : CALL_STIPEND < evm.gas)
    (hgas : sstoreTotalCost fork
      (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
      (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new
      (decide (U256.toBeBytes key ∉
        evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅)) ≤ evm.gas)
    (hset : (evm.state.recordStorageRead evm.message.currentTarget (U256.toBeBytes key)).setStorage
      evm.message.currentTarget (U256.toBeBytes key) new = .ok state') :
    ∃ after, sstoreStep evm = .ok after ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = rest ∧
      after.memory = evm.memory ∧
      after.gas = evm.gas - sstoreTotalCost fork
        (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
        (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new
        (decide (U256.toBeBytes key ∉
          evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅)) ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output ∧
      after.state = state' ∧ after.substate = { evm.substate with
        accessedStorageKeys := evm.substate.accessedStorageKeys.insert evm.message.currentTarget
          ((evm.substate.accessedStorageKeys.getD evm.message.currentTarget ∅).insert
            (U256.toBeBytes key))
        refundCounter := evm.substate.refundCounter + sstoreRefund fork
          (evm.state.getStorageOriginal evm.message.currentTarget (U256.toBeBytes key))
          (evm.state.getStorage evm.message.currentTarget (U256.toBeBytes key)) new } ∧
      after.returnData = evm.returnData := by
  have hist : Fork.istanbul ≤ fork := Nat.le_trans (by decide) hfork
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst hstatic hstipend hgas hset ⊢
  subst hst
  let original := state.getStorageOriginal message.currentTarget (U256.toBeBytes key)
  let current := state.getStorage message.currentTarget (U256.toBeBytes key)
  let cold := !decide (U256.toBeBytes key ∈
    substate.accessedStorageKeys.getD message.currentTarget ∅)
  have hgas' : sstoreCost fork original current new cold +
      sstoreStateGas fork original current new ≤ gas := by
    simpa [sstoreTotalCost, original, current, cold] using hgas
  have he : sstoreCost fork original current new cold ≤ gas := by omega
  have hs : sstoreStateGas fork original current new ≤
      gas - sstoreCost fork original current new cold := by omega
  dsimp only [original, current, cold] at he hs
  simp [sstoreStep, popWord, Stack.pop, bind, Except.bind, pure, Except.pure, hist,
    GasMeter.gasLeft, Nat.not_le.mpr hstipend, accessStorageKey, hfork, recordStorageRead,
    keepReads, refillStateGas, GasMeter.refill, chargeGas, GasMeter.charge, Nat.not_lt.mpr he,
    chargeStateGas, GasMeter.chargeState, Nat.not_lt.mpr hs, hstatic, hset,
    Except.mapError, advance, sstoreTotalCost, Nat.sub_sub]

/-- From Berlin, with one counter of gas, SSTORE writes a word to a slot of the current account.

The frame may change the state, and holds more than the stipend of 2300 gas, by EIP-2200.

The slot is cold when the transaction has not accessed it yet, by EIP-2929.

It pays execution gas and state gas, and adds the refund of the write.

The write needs the account of the current address, and gives the state `state'`.

It holds over the steps from frames that are monotone in gas. -/
theorem sstore_total (hfork : .berlin ≤ fork) {key new : U256}
    {rest : List U256} {cold : Bool} {state' : State.TransactionState}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hstatic : message.isStatic = false)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hstipend : CALL_STIPEND < gas)
    (hgas : sstoreTotalCost fork
      (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold ≤ gas)
    (hset : (state.recordStorageRead message.currentTarget (U256.toBeBytes key)).setStorage
      message.currentTarget (U256.toBeBytes key) new = .ok state') :
    Hoare fork (At code message pc (key :: new :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory
        (gas - sstoreTotalCost fork
          (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
          (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold)
        state'
        { substate with
          accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
            ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
              (U256.toBeBytes key))
          refundCounter := substate.refundCounter + sstoreRefund fork
            (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
            (state.getStorage message.currentTarget (U256.toBeBytes key)) new } returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .sstore) rfl (Fork.frontier_le _))
    instruction_sstore
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  subst hm hg hs hss hcold
  obtain ⟨after, h, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11, a12⟩ :=
    sstoreStep_eq_total hfork hst hstatic hstipend hgas hset
  exact ⟨after, h, by rw [a1, hcode], by rw [a2, hj], a3, by rw [a4, hpc], a5, by rw [a6, hmem],
    a7, by rw [a8, hrun], by rw [a9, herr], by rw [ao, hout], a10, a11, by rw [a12, hrd]⟩

/-- From Berlin, with one counter of gas, SSTORE to a slot of the current account, which exists.

The write then gives a state that holds `new` in the slot.

That state keeps every other slot of every address.

It also keeps the words before the transaction, the accounts, the codes and the block.

The rest is as for SSTORE: a frame that may change the state, more than 2300 gas, and the price. -/
theorem sstore_of_account_total (hfork : .berlin ≤ fork)
    {key new : U256} {rest : List U256} {cold : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hstatic : message.isStatic = false)
    (hcold : decide (U256.toBeBytes key ∉
      substate.accessedStorageKeys.getD message.currentTarget ∅) = cold)
    (hstipend : CALL_STIPEND < gas)
    (hgas : sstoreTotalCost fork
      (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
      (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold ≤ gas)
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true) :
    ∃ state' : State.TransactionState,
      state'.getStorage message.currentTarget (U256.toBeBytes key) = new ∧
      (∀ other slot, other ≠ message.currentTarget ∨ slot ≠ U256.toBeBytes key →
        state'.getStorage other slot = state.getStorage other slot) ∧
      state'.getStorageOriginal = state.getStorageOriginal ∧
      (∀ other, state'.getAccountOptional other = state.getAccountOptional other) ∧
      (∀ codeHash, state'.getCode codeHash = state.getCode codeHash) ∧
      state'.parent = state.parent ∧
      Hoare fork (At code message pc (key :: new :: rest) memory gas state substate returnData)
        (At code message (pc + 1) rest memory
          (gas - sstoreTotalCost fork
            (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
            (state.getStorage message.currentTarget (U256.toBeBytes key)) new cold)
          state'
          { substate with
            accessedStorageKeys := substate.accessedStorageKeys.insert message.currentTarget
              ((substate.accessedStorageKeys.getD message.currentTarget ∅).insert
                (U256.toBeBytes key))
            refundCounter := substate.refundCounter + sstoreRefund fork
              (state.getStorageOriginal message.currentTarget (U256.toBeBytes key))
              (state.getStorage message.currentTarget (U256.toBeBytes key)) new } returnData) := by
  -- Recording the read keeps the account, so the write succeeds.
  obtain ⟨state', hset⟩ := State.TransactionState.exists_setStorage (U256.toBeBytes key) new
    (tx := state.recordStorageRead message.currentTarget (U256.toBeBytes key))
    (by rw [(State.TransactionState.recordStorageRead_reads state _ message.currentTarget _
      (U256.toBeBytes key) default).1]; exact hacc)
  refine ⟨state', State.TransactionState.getStorage_setStorage_self hset, fun other slot hne => ?_,
    ?_, fun other => ?_, fun codeHash => ?_,
    by rw [State.TransactionState.parent_setStorage hset]; rfl,
    sstore_total hfork hlt hbyte hstatic hcold hstipend hgas hset⟩
  · rw [State.TransactionState.getStorage_setStorage_of_ne hset hne]
    exact (State.TransactionState.recordStorageRead_reads state _ other _ slot default).2.1
  · rw [State.TransactionState.getStorageOriginal_setStorage hset]
    funext other slot
    exact (State.TransactionState.recordStorageRead_reads state _ other _ slot default).2.2.1
  · rw [State.TransactionState.getAccountOptional_setStorage hset]
    exact (State.TransactionState.recordStorageRead_reads state _ other _
      (U256.toBeBytes key) default).1
  · rw [State.TransactionState.getCode_setStorage hset]
    exact (State.TransactionState.recordStorageRead_reads state _ message.currentTarget _
      (U256.toBeBytes key) codeHash).2.2.2.1

end EthLib.Execution.Evm.Logic
