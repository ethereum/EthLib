module

public import EthLib.Base.Proofs.Fork
public import EthLib.Execution.Evm.Instructions.AccountData
public import EthLib.Execution.Proofs.Evm.Machine.Memory
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.Instructions.AccountData`

From Berlin, an access is cold exactly when the transaction has not yet accessed the address.

The access warms the address, so a second access is warm.

Before Berlin, an access changes nothing.

BALANCE pays the price of its access, then pushes the balance of the account.

EXTCODEHASH and EXTCODESIZE access the address and pay the cold or warm price of the fork.

Then EXTCODEHASH puts the code hash of the account in place of the address.

EXTCODESIZE puts the size of the code there, when the lookup of the code succeeds.

EXTCODEHASH gives 0 for an address with no account.

Each instruction exists exactly from the fork that adds its opcode.

EXTCODECOPY sets each byte of its range to the byte of the code, and keeps every other byte.

Each instruction keeps the size of memory a multiple of 32.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256 byteAt toAddressMasked)
open EthLib.Execution.State (EMPTY_ACCOUNT)

variable {fork : Fork} {Meter : Type}

/-- Before Berlin, an access is warm and leaves the frame as it is. -/
theorem accessAddress_of_lt_berlin (h : fork < .berlin) (evm : Evm fork Meter) (a : Address) :
    accessAddress evm a = (false, evm) := by
  have : ¬fork ≥ .berlin := Nat.not_le_of_lt h
  simp [accessAddress, this]

/-- From Berlin, an access is cold exactly when the transaction has not accessed the address. -/
theorem accessAddress_fst (h : fork ≥ .berlin) (evm : Evm fork Meter) (a : Address) :
    (accessAddress evm a).1 = decide (a ∉ evm.substate.accessedAddresses) := by
  simp [accessAddress, h]

/-- From Berlin, an access adds the address to the accessed addresses. -/
theorem mem_accessAddress (h : fork ≥ .berlin) (evm : Evm fork Meter) (a : Address) :
    a ∈ (accessAddress evm a).2.substate.accessedAddresses := by
  simp [accessAddress, h]

/-- A second access to the same address is warm. -/
theorem accessAddress_accessAddress_fst (evm : Evm fork Meter) (a : Address) :
    (accessAddress (accessAddress evm a).2 a).1 = false := by
  by_cases h : fork ≥ .berlin
  · simp [accessAddress, h]
  · simp [accessAddress, h]

/-- An access keeps the message, the state and every part of the substate but its addresses. -/
theorem accessAddress_snd (evm : Evm fork Meter) (a : Address) :
    ∃ accessed, (accessAddress evm a).2 =
      { evm with substate := { evm.substate with accessedAddresses := accessed } } := by
  unfold accessAddress
  split
  · exact ⟨_, rfl⟩
  · exact ⟨evm.substate.accessedAddresses, rfl⟩

/-- BALANCE on an address word with room on the stack: access, pay, read, push the balance. -/
theorem balanceStep_cons [GasMeter Meter] {evm : Evm fork Meter} {word : U256} {rest : List U256}
    (h : evm.stack.val = word :: rest) :
    balanceStep evm =
      let accessed := accessAddress { evm with stack := ⟨rest, by
        have := evm.stack.property; rw [h] at this; simp at this; omega⟩ } (toAddressMasked word)
      (GasMeter.charge accessed.2.gas (balanceCost fork accessed.1)).map fun gas =>
        { accessed.2 with
          gas
          state := accessed.2.state.recordAccountRead (toAddressMasked word)
          stack := ⟨(evm.state.getAccount (toAddressMasked word)).balance :: rest,
            by have := evm.stack.property; rw [h] at this; simpa using this⟩
          pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨word :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := evm.stack.property
    rw [h] at this
    simp only [List.length_cons] at this
    omega
  obtain ⟨accessed, hacc⟩ := accessAddress_snd
    { evm with stack := ⟨rest, by have := evm.stack.property; rw [h] at this; simp at this; omega⟩ }
    (toAddressMasked word)
  simp only [balanceStep, popWord, chargeGas, recordAccountRead, pushWord, advance, hstack,
    Stack.pop]
  simp only [bind, Except.bind, pure, Except.pure, hacc]
  rcases hc : GasMeter.charge _ _ with _ | _ <;> simp [Except.map, Stack.push, room] <;> rfl

/-- EXTCODEHASH on an address word: access, pay, read, push the code hash of its account.

An address with no account, or with the empty account, gives 0. -/
theorem extcodehashStep_cons [GasMeter Meter] {evm : Evm fork Meter} {word : U256}
    {rest : List U256} (h : evm.stack.val = word :: rest) :
    extcodehashStep evm =
      let accessed := accessAddress { evm with stack := ⟨rest, by
        have := evm.stack.property; rw [h] at this; simp at this; omega⟩ } (toAddressMasked word)
      (GasMeter.charge accessed.2.gas (extcodehashCost fork accessed.1)).map fun gas =>
        { accessed.2 with
          gas
          state := accessed.2.state.recordAccountRead (toAddressMasked word)
          stack := ⟨codeHashWord (evm.state.getAccount (toAddressMasked word)) :: rest,
            by have := evm.stack.property; rw [h] at this; simpa using this⟩
          pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨word :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := evm.stack.property
    rw [h] at this
    simp only [List.length_cons] at this
    omega
  obtain ⟨accessed, hacc⟩ := accessAddress_snd
    { evm with stack := ⟨rest, by have := evm.stack.property; rw [h] at this; simp at this; omega⟩ }
    (toAddressMasked word)
  simp only [extcodehashStep, popWord, chargeGas, recordAccountRead, pushWord, advance, hstack,
    Stack.pop]
  simp only [bind, Except.bind, pure, Except.pure, hacc]
  rcases hc : GasMeter.charge _ _ with _ | _ <;> simp [Except.map, Stack.push, room] <;> rfl

/-- EXTCODESIZE on an address word whose code is found: access, pay, push the size of the code.

The lookup of the code can fail with a state error, which this theorem excludes. -/
theorem extcodesizeStep_of_accountCode [GasMeter Meter] {evm : Evm fork Meter} {word : U256}
    {rest : List U256} {code : ByteArray} (h : evm.stack.val = word :: rest)
    (found : accountCode evm (toAddressMasked word) = .ok code) :
    extcodesizeStep evm =
      let accessed := accessAddress { evm with stack := ⟨rest, by
        have := evm.stack.property; rw [h] at this; simp at this; omega⟩ } (toAddressMasked word)
      (GasMeter.charge accessed.2.gas (externalBaseCost fork accessed.1)).map fun gas =>
        { accessed.2 with
          gas
          state := accessed.2.state.recordAccountRead (toAddressMasked word)
          stack := ⟨BitVec.ofNat 256 code.size :: rest,
            by have := evm.stack.property; rw [h] at this; simpa using this⟩
          pc := evm.pc + 1 } := by
  have hstack : evm.stack = ⟨word :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  have room : ¬(rest.length = STACK_LIMIT) := by
    have := evm.stack.property
    rw [h] at this
    simp only [List.length_cons] at this
    omega
  obtain ⟨accessed, hacc⟩ := accessAddress_snd
    { evm with stack := ⟨rest, by have := evm.stack.property; rw [h] at this; simp at this; omega⟩ }
    (toAddressMasked word)
  simp only [extcodesizeStep, popWord, chargeGas, recordAccountRead, pushWord, advance, hstack,
    Stack.pop]
  simp only [bind, Except.bind, pure, Except.pure, hacc]
  -- Recording the read leaves the account and its code as they are.
  have recorded : Except.mapError EvmError.state
      ((evm.state.recordAccountRead (toAddressMasked word)).getCode
        ((evm.state.recordAccountRead (toAddressMasked word)).getAccount
          (toAddressMasked word)).codeHash) = Except.ok code := found
  rcases hc : GasMeter.charge _ _ with _ | _ <;>
    simp [Except.map, Stack.push, room, accountCode, recorded]

/-- EXTCODECOPY on an address word, a start, an offset and a size, whose code is found.

It accesses the address, pays the access, 3 gas a word and the growth of memory.

It records the read of the account.

It then writes the bytes of the code from the offset, with zeros past its end.

The write is made after memory has grown.

The lookup of the code can fail with a state error, which this theorem excludes. -/
theorem extcodecopyStep_of_accountCode [GasMeter Meter] {evm : Evm fork Meter}
    {word start offset size : U256} {rest : List U256} {code : ByteArray}
    (h : evm.stack.val = word :: start :: offset :: size :: rest)
    (found : accountCode evm (toAddressMasked word) = .ok code) :
    extcodecopyStep evm =
      let accessed := accessAddress { evm with stack := ⟨rest, by
        have := evm.stack.property; rw [h] at this; simp at this; omega⟩ } (toAddressMasked word)
      let growth := extendMemory evm.memory.size [(start, size)]
      (GasMeter.charge accessed.2.gas (externalBaseCost fork accessed.1 +
          GasCosts.OPCODE_COPY_PER_WORD * wordCount size.toNat + growth.cost)).map fun gas =>
        { accessed.2 with
          gas
          state := accessed.2.state.recordAccountRead (toAddressMasked word)
          memory := memoryWrite (memoryExtend evm.memory growth.expandBy) start.toNat
            ⟨(bufferRead code offset.toNat size.toNat).toArray⟩
          pc := evm.pc + 1 } := by
  have hstack : evm.stack =
      ⟨word :: start :: offset :: size :: rest, h ▸ evm.stack.property⟩ := Subtype.ext h
  obtain ⟨accessed, hacc⟩ := accessAddress_snd
    { evm with stack := ⟨rest, by have := evm.stack.property; rw [h] at this; simp at this; omega⟩ }
    (toAddressMasked word)
  simp only [extcodecopyStep, popWord, chargeGasAndMemory, chargeGas, recordAccountRead, advance,
    hstack, Stack.pop]
  simp only [bind, Except.bind, pure, Except.pure, hacc]
  -- Recording the read leaves the account and its code as they are.
  have recorded : Except.mapError EvmError.state
      ((evm.state.recordAccountRead (toAddressMasked word)).getCode
        ((evm.state.recordAccountRead (toAddressMasked word)).getAccount
          (toAddressMasked word)).codeHash) = Except.ok code := found
  rcases hc : GasMeter.charge _ _ with _ | _ <;>
    simp [Except.map, accountCode, recorded]

/-- EXTCODEHASH reads 0 for an address with no account. -/
theorem codeHashWord_of_none {state : State.TransactionState} {a : Address}
    (h : state.getAccountOptional a = none) : codeHashWord (state.getAccount a) = 0 := by
  simp [codeHashWord, State.TransactionState.getAccount, h]

/-- EXTCODEHASH reads the code hash of an account that is not empty. -/
theorem codeHashWord_of_ne {account : State.Account} (h : account ≠ EMPTY_ACCOUNT) :
    codeHashWord account = U256.fromBeBytes account.codeHash := by
  simp [codeHashWord, h]

/-- An opcode that reads another account has an instruction exactly from the fork that adds it.

No other opcode has one. -/
theorem isSome_accountStep [GasMeter Meter] {op : Op} :
    (accountStep (Meter := Meter) fork op).isSome ↔
      op ∈ [.balance, .selfbalance, .extcodesize, .extcodecopy, .extcodehash] ∧
      op.since ≤ fork := by
  cases op <;> simp [accountStep, Op.since, Fork.frontier_le] <;> split <;> simp_all

/-- An access keeps memory. -/
theorem memory_accessAddress (evm : Evm fork Meter) (a : Address) :
    (accessAddress evm a).2.memory = evm.memory := by
  obtain ⟨_, h⟩ := accessAddress_snd evm a
  rw [h]

/-- EXTCODECOPY sets each byte of its range to the byte of the code of the account from the offset.

Past the end of the code, the byte is zero.

It keeps every other byte.

The code is the one that the step reads for the account, in the frame before the step.

Memory must start at a size that is a multiple of 32. -/
theorem byteAt_extcodecopyStep [GasMeter Meter] {evm after : Evm fork Meter}
    {word start offset size : U256} {rest : List U256}
    (hstack : evm.stack.val = word :: start :: offset :: size :: rest)
    (hmod : evm.memory.size % 32 = 0) (h : extcodecopyStep evm = .ok after) :
    ∃ code, accountCode evm (toAddressMasked word) = .ok code ∧ ∀ i,
      byteAt after.memory i =
        if start.toNat ≤ i ∧ i < start.toNat + size.toNat then
          byteAt code (offset.toNat + (i - start.toNat))
        else byteAt evm.memory i := by
  unfold extcodecopyStep at h
  obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨y, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨z, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨w, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨s1, m1, -⟩ := popWord_eq_ok h1
  obtain ⟨s2, m2, -⟩ := popWord_eq_ok h2
  obtain ⟨s3, m3, -⟩ := popWord_eq_ok h3
  obtain ⟨s4, m4, -⟩ := popWord_eq_ok h4
  rw [hstack] at s1
  obtain ⟨rfl, r1⟩ := List.cons.inj s1
  rw [← r1] at s2
  obtain ⟨rfl, r2⟩ := List.cons.inj s2
  rw [← r2] at s3
  obtain ⟨rfl, r3⟩ := List.cons.inj s3
  rw [← r3] at s4
  obtain ⟨rfl, -⟩ := List.cons.inj s4
  have c4 := (((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
    (popWord_sameContext h3)).trans (popWord_sameContext h4)
  obtain ⟨accessed, ha⟩ := accessAddress_snd e4 (toAddressMasked word)
  dsimp only at h
  rw [show accessAddress e4 (toAddressMasked word) = ((accessAddress e4 (toAddressMasked word)).1,
      { e4 with substate := { e4.substate with accessedAddresses := accessed } }) from
      Prod.ext rfl ha] at h
  dsimp only at h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have c5 := chargeGasAndMemory_sameContext h5
  obtain ⟨code, h6, h⟩ := Base.bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hcode : accountCode evm (toAddressMasked word) = .ok code := by
    rw [← h6]
    simp only [accountCode, recordAccountRead, c5.state, c4.state]
    rfl
  refine ⟨code, hcode, fun i => ?_⟩
  have hm4 : e4.memory = evm.memory := by rw [m4, m3, m2, m1]
  have hmem : ∀ j, byteAt e5.memory j = byteAt evm.memory j := fun j => by
    rw [byteAt_chargeGasAndMemory h5]
    exact congrArg (byteAt · j) hm4
  have hlen : ({ data := (bufferRead code offset.toNat size.toNat).toArray } : ByteArray).size =
      size.toNat := by simp [ByteArray.size, bufferRead_length]
  simp only [advance, recordAccountRead]
  by_cases hz : size = 0
  · subst hz
    have hw : memoryWrite e5.memory start.toNat
        ⟨(bufferRead code offset.toNat (0 : U256).toNat).toArray⟩ = e5.memory := by
      unfold memoryWrite
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hlen]; rfl))]
    rw [hw, hmem, ite_eq_right_iff.mpr (fun hc => absurd hc.2 (by have := hc.1; simp; omega))]
  · have hmod4 : e4.memory.size % 32 = 0 := by rw [hm4]; exact hmod
    have fit := le_size_chargeGasAndMemory (evm := { e4 with
      substate := { e4.substate with accessedAddresses := accessed } }) hmod4 h5 (start, size)
      (by simp) hz
    simp only at fit
    rw [byteAt_memoryWrite (by rw [hlen]; exact fit), hlen]
    split
    · rename_i hin
      rw [byteAt_bufferRead, ite_eq_left_iff.mpr (fun hc => absurd (by omega) hc)]
    · exact hmem i

/-- EXTCODEHASH keeps the size of memory a multiple of 32. -/
theorem size_extcodehashStep_mod [GasMeter Meter] {evm after : Evm fork Meter}
    (hmod : evm.memory.size % 32 = 0) (h : extcodehashStep evm = .ok after) :
    after.memory.size % 32 = 0 := by
  obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  cases h
  simp only [advance]
  rw [memory_pushWord h3]
  simp only [recordAccountRead]
  rw [memory_chargeGas h2]
  exact (congrArg (fun m : ByteArray => m.size % 32)
    ((memory_accessAddress e1 (toAddressMasked x)).trans (popWord_eq_ok h1).2.1)).trans hmod

/-- Each instruction that reads another account keeps the size of memory a multiple of 32. -/
theorem size_accountStep_mod [GasMeter Meter] {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some step) {evm after : Evm fork Meter}
    (hmod : evm.memory.size % 32 = 0) (h : step evm = .ok after) :
    after.memory.size % 32 = 0 := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  case extcodehash | selfbalance =>
    split at hstep
    · simp only [Option.some.injEq] at hstep
      subst hstep
      first
        | (rw [memory_readFrame h]; exact hmod)
        | exact size_extcodehashStep_mod hmod h
    · cases hstep
  all_goals subst hstep
  case balance =>
    obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    simp only [advance]
    rw [memory_pushWord h3]
    simp only [recordAccountRead]
    rw [memory_chargeGas h2]
    exact (congrArg (fun m : ByteArray => m.size % 32)
      ((memory_accessAddress e1 (toAddressMasked x)).trans (popWord_eq_ok h1).2.1)).trans hmod
  case extcodesize =>
    obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    simp only [advance]
    rw [memory_pushWord h3]
    simp only [recordAccountRead]
    rw [memory_chargeGas h2]
    exact (congrArg (fun m : ByteArray => m.size % 32)
      ((memory_accessAddress e1 (toAddressMasked x)).trans (popWord_eq_ok h1).2.1)).trans hmod
  case extcodecopy =>
    obtain ⟨⟨x, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨accessed, ha⟩ := accessAddress_snd e4 (toAddressMasked x)
    dsimp only at h
    rw [show accessAddress e4 (toAddressMasked x) = ((accessAddress e4 (toAddressMasked x)).1,
        { e4 with substate := { e4.substate with accessedAddresses := accessed } }) from
        Prod.ext rfl ha] at h
    dsimp only at h
    obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have m4 : e4.memory.size % 32 = 0 := by
      rw [(popWord_eq_ok h4).2.1, (popWord_eq_ok h3).2.1, (popWord_eq_ok h2).2.1,
        (popWord_eq_ok h1).2.1]
      exact hmod
    simp only [advance, recordAccountRead]
    refine size_memoryWrite_chargeGasAndMemory_mod (evm := { e4 with
      substate := { e4.substate with accessedAddresses := accessed } }) m4 h5 ?_
    simp [ByteArray.size, bufferRead_length]

end EthLib.Execution.Evm
