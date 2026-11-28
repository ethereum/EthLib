module

public import EthLib.Execution.Proofs.Evm.Logic.Environment
public import EthLib.Execution.Proofs.Evm.Instructions.TransientStorage

/-!
# Proofs: rules for the opcodes that read accounts, block hashes and transient storage

Each rule goes from one running frame to the next, from the fork that its hypothesis names.

The rules work out the charge of one counter of gas, the meter of every fork before Glamsterdam.

A read of another account pays a cold or a warm access from Berlin, by EIP-2929.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256 toAddressMasked)
open GasCosts

variable {fork : Fork}

/-! ## The instruction table -/

section Table

variable {Meter : Type} [GasMeter Meter]

/-- From Dencun, BLOBHASH runs the read of a versioned hash of the transaction. -/
theorem instruction_blobhash (h : .dencun ≤ fork) :
    instruction (Meter := Meter) fork .blobhash = some (blobhashStep h) := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From Dencun, TLOAD runs the read of a word of transient storage. -/
theorem instruction_tload (h : .dencun ≤ fork) :
    instruction (Meter := Meter) fork .tload = some tloadStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, h, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

/-- BALANCE runs the read of the balance of an account. -/
theorem instruction_balance : instruction (Meter := Meter) fork .balance = some balanceStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From Constantinople, EXTCODEHASH runs the read of the code hash of an account. -/
theorem instruction_extcodehash (h : .constantinople ≤ fork) :
    instruction (Meter := Meter) fork .extcodehash = some extcodehashStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From Istanbul, SELFBALANCE runs the read of the balance of the current account. -/
theorem instruction_selfbalance (h : .istanbul ≤ fork) :
    instruction (Meter := Meter) fork .selfbalance = some fun evm =>
      readFrame OPCODE_SELFBALANCE
        (fun evm => (evm.state.getAccount evm.message.currentTarget).balance)
        (recordAccountRead evm evm.message.currentTarget) := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, h, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- From Dencun, TSTORE runs the write of a word of transient storage. -/
theorem instruction_tstore (h : .dencun ≤ fork) :
    instruction (Meter := Meter) fork .tstore = some tstoreStep := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, accountStep, storageStep, transientStorageStep, h, HOrElse.hOrElse,
    OrElse.orElse, Option.orElse]

end Table

variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray} {gas : Nat}
  {state : State.TransactionState} {substate : Substate} {returnData : ByteArray}
  {rest : List U256}

/-! ## Block hashes -/

/-- BLOCKHASH puts the hash of a recent block in place of its number, for 20 gas.

The hash is 0 for a block that is not one of the 256 before the current one. -/
theorem blockhash_rule {number : U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x40)
    (hgas : 20 ≤ gas) :
    Hoare fork (At code message pc (number :: rest) memory gas state substate returnData)
      (At code message (pc + 1)
        (blockHash message.blockEnv.blockHashes message.blockEnv.number number.toNat :: rest)
        memory (gas - 20) state substate returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .blockhash) rfl (Fork.frontier_le _)) rfl
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [blockhashStep_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hm], hmem,
    by simp [hg, OPCODE_BLOCKHASH], hrun, herr, hout, hs, hss, hrd⟩

/-- From Dencun, BLOBHASH puts a versioned hash of the transaction in place of its index.

It costs 3 gas, by EIP-4844.

The hash is 0 for an index past the hashes of the transaction. -/
theorem blobhash_rule (hfork : .dencun ≤ fork) {index : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x49) (hgas : 3 ≤ gas) :
    Hoare fork (At code message pc (index :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (blobHash (message.txEnv.blobVersionedHashes hfork) index :: rest)
        memory (gas - 3) state substate returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .blobhash) rfl hfork)
    (instruction_blobhash hfork)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [blobhashStep_cons hfork hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hm], hmem,
    by simp [hg, OPCODE_BLOBHASH], hrun, herr, hout, hs, hss, hrd⟩

/-! ## Transient storage -/

/-- From Dencun, TLOAD puts the transient word of the current account in place of its key.

It costs 100 gas, by EIP-1153. -/
theorem tload_rule (hfork : .dencun ≤ fork) {key : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5c) (hgas : 100 ≤ gas) :
    Hoare fork (At code message pc (key :: rest) memory gas state substate returnData)
      (At code message (pc + 1)
        (state.getTransientStorage message.currentTarget (U256.toBeBytes key) :: rest) memory
        (gas - 100) state substate returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .tload) rfl hfork) (instruction_tload hfork)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [tloadStep_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], by simp [hm, hs], hmem,
    by simp [hg, OPCODE_TLOAD, WARM_ACCESS], hrun, herr, hout, hs, hss, hrd⟩

/-- From Dencun, TSTORE writes a word of transient storage of the current account at a key.

It pops the key, then the word, and costs 100 gas, by EIP-1153.

The frame must be able to change the state. -/
theorem tstore_rule (hfork : .dencun ≤ fork) {key value : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5d) (hstatic : message.isStatic = false) (hgas : 100 ≤ gas) :
    Hoare fork (At code message pc (key :: value :: rest) memory gas state substate returnData)
      (At code message (pc + 1) rest memory (gas - 100)
        (state.setTransientStorage message.currentTarget (U256.toBeBytes key) value) substate
        returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .tstore) rfl hfork) (instruction_tstore hfork)
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  have hstack : evm.stack = ⟨key :: value :: rest, hst ▸ evm.stack.property⟩ := Subtype.ext hst
  have hcharge : GasMeter.charge evm.gas OPCODE_TSTORE = .ok (gas - 100) := by
    rw [hg]
    exact charge_nat hgas
  have hstatic' : evm.message.isStatic = false := hm ▸ hstatic
  simp only [tstoreStep, popWord, hstack, Stack.pop, chargeGas, hcharge, bind, Except.bind,
    pure, Except.pure, hstatic', Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl, hc, hj, hm, by simp [advance, hpc], rfl, hmem, rfl, hrun, herr, hout,
    by rw [← hs, ← hm]; rfl, hss, hrd⟩

/-! ## Accounts -/

/-- From Istanbul, SELFBALANCE pushes the balance of the current account, for 5 gas, by EIP-1884.

It records the read of the account.

The stack needs room for one more word. -/
theorem selfbalance_rule (hfork : .istanbul ≤ fork) {stack : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x47) (hgas : 5 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) ((state.getAccount message.currentTarget).balance :: stack)
        memory (gas - 5) (state.recordAccountRead message.currentTarget) substate returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .selfbalance) rfl hfork)
    (instruction_selfbalance hfork)
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [readFrame_of_length_lt (by simp only [recordAccountRead, hst]; exact hstack),
    charge_nat (by simp only [recordAccountRead, hg, OPCODE_SELFBALANCE, FAST_STEP]; exact hgas)]
  exact ⟨_, rfl, hc, hj, hm, by simp [recordAccountRead, hpc],
    by simp [recordAccountRead, hst, hs, hm], hmem,
    by simp [recordAccountRead, hg, OPCODE_SELFBALANCE, FAST_STEP], hrun, herr, hout,
    by simp [recordAccountRead, hs, hm], hss, hrd⟩

/-- From Berlin, BALANCE puts the balance of an account in place of its address word.

The address is the low 20 bytes of the word.

It adds the address to the accessed set, pays the access, cold or warm, then records the read. -/
theorem balance_rule (hfork : .berlin ≤ fork) {word : U256} {cold : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x31)
    (hcold : decide (toAddressMasked word ∉ substate.accessedAddresses) = cold)
    (hgas : balanceCost fork cold ≤ gas) :
    Hoare fork (At code message pc (word :: rest) memory gas state substate returnData)
      (At code message (pc + 1) ((state.getAccount (toAddressMasked word)).balance :: rest)
        memory (gas - balanceCost fork cold) (state.recordAccountRead (toAddressMasked word))
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked word) }
        returnData) := by
  apply At.rule hlt hbyte (ofByte_of_decode (op := .balance) rfl (Fork.frontier_le _))
    instruction_balance
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [balanceStep_cons hst]
  simp only [accessAddress, hfork, ↓reduceIte, hss, hcold, hg, charge_nat hgas]
  exact ⟨_, rfl, hc, hj, hm, by simp [hpc], by simp [hs], hmem, rfl, hrun, herr, hout,
    by simp [hs], by simp, hrd⟩

/-- From Berlin, EXTCODEHASH puts the code hash of an account in place of its address word.

The word is 0 for an empty account.

It adds the address to the accessed set, pays the access, cold or warm, then records the read. -/
theorem extcodehash_rule (hfork : .berlin ≤ fork) {word : U256} {cold : Bool}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3f)
    (hcold : decide (toAddressMasked word ∉ substate.accessedAddresses) = cold)
    (hgas : extcodehashCost fork cold ≤ gas) :
    Hoare fork (At code message pc (word :: rest) memory gas state substate returnData)
      (At code message (pc + 1) (codeHashWord (state.getAccount (toAddressMasked word)) :: rest)
        memory (gas - extcodehashCost fork cold)
        (state.recordAccountRead (toAddressMasked word))
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked word) }
        returnData) := by
  apply At.rule hlt hbyte
    (ofByte_of_decode (op := .extcodehash) rfl (Nat.le_trans (by decide) hfork))
    (instruction_extcodehash (Nat.le_trans (by decide) hfork))
  rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [extcodehashStep_cons hst]
  simp only [accessAddress, hfork, ↓reduceIte, hss, hcold, hg, charge_nat hgas]
  exact ⟨_, rfl, hc, hj, hm, by simp [hpc], by simp [hs], hmem, rfl, hrun, herr, hout,
    by simp [hs], by simp, hrd⟩

end EthLib.Execution.Evm.Logic
