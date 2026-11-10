module

public import EthLib.Base.Proofs.Address
public import EthLib.Execution.Proofs.Evm.Logic.Steps
public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Evm.Logic.Region
public import EthLib.Execution.Proofs.Evm.Logic.Keeps
public import EthLib.Execution.Proofs.Blocks.SystemCall
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: what the system contracts share

A system contract tells a call from the system address apart from any other call.

It reads a word of its input, and its storage, slot by slot.

A call that reads returns one word of 32 bytes, or reverts with no output.

The code of such a return, and of such a revert, is the same in each contract.

A system call to a contract with code runs that code with the gas of a system call.

So a run of the code to a stop with no error gives a system call that succeeds.
-/

@[expose] public section

namespace EthLib.Execution.Blocks.SystemContract

open EthLib.Base (Fork U256 Address)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open GasCosts
open EthLib.Execution.Transactions (prepareFirstFrame_of_value_eq_zero processMessageCall)

/-! ## Words and storage -/

/-- The word of the first 32 bytes of `input`, read big-endian, with zero bytes past its end. -/
def inputWord (input : ByteArray) : U256 := loadWord input 0 32

/-- The storage of the account at `address` in the state `state`, slot by slot. -/
def storageOf (state : TransactionState) (address : Address) (slot : U256) : U256 :=
  state.getStorage address (U256.toBeBytes slot)

/-- The state `post` holds the storage `store` at `target`, and keeps the rest of `S`.

It keeps the storage of every other account, the accounts and the codes. -/
def WritesStorage (target : Address) (store : U256 → U256) (S post : TransactionState) : Prop :=
  (∀ slot, storageOf post target slot = store slot) ∧
    (∀ other key, other ≠ target → post.getStorage other key = S.getStorage other key) ∧
    (∀ other, post.getAccountOptional other = S.getAccountOptional other) ∧
    ∀ codeHash, post.getCode codeHash = S.getCode codeHash

/-- A state holds its own storage at an address, and keeps the rest of itself. -/
theorem WritesStorage.refl (target : Address) (S : TransactionState) :
    WritesStorage target (storageOf S target) S S :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Two writes in turn: the second gives the storage, and both keep the rest. -/
theorem WritesStorage.trans {target : Address} {f g : U256 → U256}
    {S S' S'' : TransactionState} (h : WritesStorage target f S S')
    (h' : WritesStorage target g S' S'') : WritesStorage target g S S'' :=
  ⟨h'.1, fun o k hne => (h'.2.1 o k hne).trans (h.2.1 o k hne),
    fun o => (h'.2.2.1 o).trans (h.2.2.1 o), fun c => (h'.2.2.2 c).trans (h.2.2.2 c)⟩

/-- A record of a read keeps the storage. -/
theorem storageOf_recordStorageRead (S : TransactionState) (target address : Address)
    (key : EthLib.Base.Bytes32) :
    storageOf (S.recordStorageRead address key) target = storageOf S target := rfl

/-- A record of a read keeps the storage and the rest of the state. -/
theorem WritesStorage.recordStorageRead (target : Address) (S : TransactionState)
    (address : Address) (key : EthLib.Base.Bytes32) :
    WritesStorage target (storageOf S target) S (S.recordStorageRead address key) :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The word of the system address is `0xff…fe`. -/
theorem toU256_SYSTEM_ADDRESS :
    SYSTEM_ADDRESS.toU256 = BitVec.ofNat 256 0xfffffffffffffffffffffffffffffffffffffffe := by
  apply BitVec.eq_of_toNat_eq
  rw [SYSTEM_ADDRESS, EthLib.Base.toNat_toU256_toAddressMasked]
  rfl

/-- An address other than the system address has another word. -/
theorem toU256_ne_of_ne_SYSTEM_ADDRESS {a : Address} (h : a ≠ SYSTEM_ADDRESS) :
    a.toU256 ≠ BitVec.ofNat 256 0xfffffffffffffffffffffffffffffffffffffffe := by
  rw [← toU256_SYSTEM_ADDRESS]
  exact EthLib.Base.Address.toU256_injective.ne h

/-- Each of the two prices of a read of storage from Berlin, 2100 and 100, is at most 2100. -/
theorem sloadPrice_le (cold : Bool) : (if cold then 2100 else 100) ≤ 2100 := by
  cases cold <;> decide

/-- The growth of empty memory to one word costs 3 and adds 32 bytes. -/
theorem extendMemory_word : extendMemory 0 [(0, 32)] = ⟨3, 32⟩ := by decide

/-! ## The end of a call that reads -/

/-- What a stopped frame holds when a call gets the answer `result`, from the state `state`.

A word returns its 32 bytes, and no word reverts with no output.

The state reads as `state`: it has its storage, its accounts and its codes. -/
def Answer {fork : Fork} (state : TransactionState) (result : Option U256) (evm : Evm fork Nat) :
    Prop :=
  ReadsAs evm.state state ∧
    match result with
    | some word => evm.error = none ∧ evm.output = wordBytes word
    | none => evm.error = some .revert ∧ evm.output = .empty

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat} {gas : Nat}
  {state : TransactionState} {substate : Substate} {returnData : ByteArray}

/-- An answer from a state that reads as `state` is an answer from `state`. -/
theorem Answer.of_readsAs {after : TransactionState} {result : Option U256} {evm : Evm fork Nat}
    (reads : ReadsAs after state) (h : Answer after result evm) : Answer state result evm :=
  ⟨h.1.trans reads, h.2⟩

/-- From Shapella, PUSH0, PUSH0 and REVERT revert with no output, and keep the state. -/
theorem revertEmpty {stack : List U256} (hfork : .shapella ≤ fork) (hlt : pc + 2 < code.size)
    (h0 : code[pc]'(by omega) = 0x5f) (h1 : code[pc + 1]'(by omega) = 0x5f)
    (h2 : code[pc + 2] = 0xfd) (hstack : stack.length + 2 < STACK_LIMIT) (hgas : 4 ≤ gas) :
    Spec fork (At code message pc stack .empty gas state substate returnData)
      (Answer state none) := by
  refine Triple.seq (push0 hfork (by omega) h0 (by omega) (by omega)) ?_
  refine Triple.seq (push0 hfork (by omega) h1 (by omega) (by simp; omega)) ?_
  refine Spec.consequence (revert (Nat.le_trans (by decide) hfork) (by omega)
    (by simp only [show pc + 1 + 1 = pc + 2 by omega]; exact h2)
    (by rw [extendMemory_of_length_eq_zero]; exact Nat.zero_le _)) (fun _ h => h) ?_
  rintro evm ⟨-, herr, hout, -, hst, -⟩
  refine ⟨hst ▸ ReadsAs.refl _, by simpa using herr, ?_⟩
  rw [hout, extendMemory_of_length_eq_zero]
  rfl

/-- From Shapella, PUSH0, MSTORE, PUSH1 32, PUSH0 and RETURN return the word on the stack.

The memory starts empty, and the run keeps the state. -/
theorem returnWord {word : U256} (hfork : .shapella ≤ fork) (hlt : pc + 5 < code.size)
    (h0 : code[pc]'(by omega) = 0x5f) (h1 : code[pc + 1]'(by omega) = 0x52)
    (h2 : code[pc + 2]'(by omega) = 0x60) (h3 : code[pc + 3]'(by omega) = 0x20)
    (h4 : code[pc + 4]'(by omega) = 0x5f) (h5 : code[pc + 5] = 0xf3) (hgas : 20 ≤ gas) :
    Spec fork (At code message pc [word] .empty gas state substate returnData)
      (Answer state (some word)) := by
  refine Triple.seq (push0 hfork (by omega) h0 (by omega) (by simp [STACK_LIMIT])) ?_
  refine Triple.seq (mstore (by omega) h1
    (by simp only [ByteArray.size_empty, extendMemory_word]; omega)) ?_
  rw [ByteArray.size_empty, extendMemory_word]
  dsimp only
  rw [show BitVec.toNat (0 : U256) = 0 from rfl,
    memoryWrite_whole (by rw [size_memoryExtend, size_wordBytes]; rfl)]
  refine Triple.seq (push1 (by omega) h2
    (by simp only [show pc + 1 + 1 + 1 = pc + 3 by omega]; exact h3) (by omega)
    (by simp [STACK_LIMIT])) ?_
  refine Triple.seq (push0 hfork (by omega)
    (by simp only [show pc + 1 + 1 + 2 = pc + 4 by omega]; exact h4) (by omega)
    (by simp [STACK_LIMIT])) ?_
  have hle : extendMemory (wordBytes word).size [(0, BitVec.ofNat 256 (0x20 : UInt8).toNat)] =
      ⟨0, 0⟩ := extendMemory_of_le (by rw [size_wordBytes]; decide)
  refine Spec.consequence («return» (by omega)
    (by simp only [show pc + 1 + 1 + 2 + 1 = pc + 5 by omega]; exact h5)
    (by rw [hle]; exact Nat.zero_le _)) (fun _ h => h) ?_
  rintro evm ⟨-, herr, hout, -, hst, -⟩
  refine ⟨hst ▸ ReadsAs.refl _, by simpa using herr, ?_⟩
  rw [hout, hle]
  dsimp only
  rw [memoryExtend_zero]
  conv => rhs; rw [← memoryReadBytes_whole (memory := wordBytes word)]
  rw [size_wordBytes]
  rfl

/-! ## The system call -/

/-- An account exists when its code hash maps to a code that is not empty. -/
theorem isSome_of_getCode {address : Address} (hsize : code.size ≠ 0)
    (h : state.getCode (state.getAccount address).codeHash = .ok code) :
    (state.getAccountOptional address).isSome = true := by
  cases hacc : state.getAccountOptional address with
  | some _ => rfl
  | none =>
    simp only [TransactionState.getAccount, hacc, Option.getD_none] at h
    simp only [TransactionState.getCode, State.EMPTY_ACCOUNT, ↓reduceIte, Except.ok.injEq] at h
    exact absurd (congrArg ByteArray.size h).symm hsize

/-- From Paris up to BPO5, a system call to a contract with code runs that code to its end.

The address is not a precompile, and the code is not a delegation indicator.

The code must stop with no error, from every frame that a system call starts.

Its state and output must meet `Q`, with the state that the frame starts from.

Such a frame comes from the system address, to the contract, with the block and the data.

It may change the state, it has the gas of a system call, and the account of the contract exists.

It starts from the state of the block, with the read of the contract recorded.

The system call then succeeds, and its state and output meet `Q`.

In the conclusion, `Q` gets that start state. -/
theorem systemCall_of_spec {env : BlockEnvironment fork} {block : State.BlockState}
    {target : Address} {data : ByteArray}
    {Q : TransactionState → TransactionState → ByteArray → Prop}
    (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hcode : codeAt block target = .ok code) (hsize : code.size ≠ 0)
    (hpre : Precompiles.addedAt target.toU256.toNat = none)
    (hdelegate : delegatedAddress code = none)
    (hspec : ∀ (message : Message fork) (state : TransactionState) (substate : Substate),
      message.caller = SYSTEM_ADDRESS → message.currentTarget = target →
      message.isStatic = false → message.blockEnv = env → message.data = data →
      message.gas = SYSTEM_TRANSACTION_GAS → (state.getAccountOptional target).isSome = true →
      state = (TransactionState.ofBlock block).recordAccountRead target →
      Spec fork (At code message 0 [] .empty message.gas state substate .empty)
        fun evm => evm.error = none ∧ Q state evm.state evm.output) :
    ∃ out, systemCall env block target data = .ok out ∧ out.error = none ∧
      Q ((TransactionState.ofBlock block).recordAccountRead target) out.state out.output := by
  have hc := EthLib.Base.mapError_ok_iff.mp hcode
  have hfirst := prepareFirstFrame_of_value_eq_zero (Meter := Nat) (chainId := env.chainId.toNat)
    (message := systemMessage env target data) (state := .ofBlock block)
    (substate := Substate.empty) (paid := ∅) rfl rfl hc (fun _ => hdelegate)
  generalize hF : Transactions.FirstFrame.ofMeter (Meter := Nat) _ _ _ _ _ = first at hfirst
  have hnot : ¬fork < .paris := Nat.not_lt.mpr hparis
  have hstart : startState fork first.message first.state = first.state := by
    simp only [startState, hnot, ↓reduceIte]
  have hacc : (first.state.getAccountOptional target).isSome = true := by
    subst hF
    exact isSome_of_getCode hsize hc
  have hpre' : precompileAddress fork first.message = none := by
    subst hF
    simp [Transactions.FirstFrame.ofMeter, precompileAddress, systemMessage,
      Precompiles.isPrecompile, hpre]
  have hvalue : ¬(first.message.shouldTransferValue = true ∧ first.message.value ≠ 0) := by
    subst hF
    simp [Transactions.FirstFrame.ofMeter, systemMessage]
  have hcodeM : first.message.code = code := by subst hF; rfl
  obtain ⟨stopped, ⟨herr, hq⟩, hpm⟩ := processMessage_of_spec (message := first.message)
    (state := first.state) (substate := first.substate)
    (hspec first.message (startState fork first.message first.state) first.substate
      (by subst hF; rfl) (by subst hF; rfl) (by subst hF; rfl) (by subst hF; rfl)
      (by subst hF; rfl) (by subst hF; rfl) (by rw [hstart]; exact hacc)
      (by rw [hstart]; subst hF; rfl))
    hvalue hpre' (at_startFrame hcodeM _ _)
  rw [rollbackOnError_of_error_eq_none herr] at hpm
  rw [hstart] at hq
  cases hp : processMessage (Meter := Nat) fork first.message first.state first.substate with
  | error e => rw [hp] at hpm; cases hpm
  | ok ended =>
    rw [hp] at hpm
    have hv : ended.val = stopped := Except.ok.inj hpm
    have hp' : processMessage fork first.message first.state first.substate first.meter
        first.held = .ok ended := by
      subst hF
      exact hp
    rw [systemCall_of_lt_glamsterdam hglam]
    have htarget : (systemMessage env target data).target = some target := rfl
    simp only [processMessageCall, hfirst, hp', htarget, bind, Except.bind, pure, Except.pure,
      Except.map]
    refine ⟨_, rfl, ?_⟩
    simp only [Transactions.CallOutput.ofFrame, hv, herr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte]
    subst hF
    exact ⟨trivial, hq⟩

/-- From Paris up to BPO5, a system call to a contract whose code writes its storage.

The contract has code at an address that is not a precompile, and its code is not a delegation.

The storage of the contract in the block meets `P`.

From every frame that a system call starts on a storage that meets `P`, the code stops.

It stops with no error, and returns `output` of that storage.

Its state holds `store` of that storage at the contract, and keeps the rest.

The system call then succeeds and returns `output` of the storage in the block.

Its state holds `store` of the storage in the block at the contract, and keeps the rest. -/
theorem systemCall_of_writesStorage {env : BlockEnvironment fork} {block : State.BlockState}
    {target : Address} {data : ByteArray} {P : (U256 → U256) → Prop}
    (output : (U256 → U256) → ByteArray) (store : (U256 → U256) → U256 → U256)
    (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hcode : codeAt block target = .ok code) (hsize : code.size ≠ 0)
    (hpre : Precompiles.addedAt target.toU256.toNat = none)
    (hdelegate : delegatedAddress code = none)
    (hread : P (storageOf (.ofBlock block) target))
    (hspec : ∀ (message : Message fork) (state : TransactionState) (substate : Substate),
      message.caller = SYSTEM_ADDRESS → message.currentTarget = target →
      message.isStatic = false → message.blockEnv = env → message.data = data →
      message.gas = SYSTEM_TRANSACTION_GAS → (state.getAccountOptional target).isSome = true →
      P (storageOf state target) →
      Spec fork (At code message 0 [] .empty message.gas state substate .empty) fun evm =>
        evm.error = none ∧ evm.output = output (storageOf state target) ∧
        WritesStorage target (store (storageOf state target)) state evm.state) :
    ∃ out, systemCall env block target data = .ok out ∧ out.error = none ∧
      out.output = output (storageOf (.ofBlock block) target) ∧
      WritesStorage target (store (storageOf (.ofBlock block) target)) (.ofBlock block)
        out.state :=
  systemCall_of_spec (Q := fun S post out => out = output (storageOf S target) ∧
      WritesStorage target (store (storageOf S target)) S post)
    hparis hglam hcode hsize hpre hdelegate
    fun message state substate hcaller htarget hstatic henv hdata hgas hacc hstate =>
      hspec message state substate hcaller htarget hstatic henv hdata hgas hacc
        (by subst hstate; exact hread)

end EthLib.Execution.Blocks.SystemContract
