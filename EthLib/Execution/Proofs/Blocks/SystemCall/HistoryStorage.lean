module

public import EthLib.Execution.Proofs.Blocks.SystemCall.Meter

/-!
# Proofs: the history storage contract of EIP-2935 does what its EIP describes

The contract keeps the hashes of the last 8191 blocks, in a ring of 8191 storage slots.

Its code is the 83 bytes of [EIP-2935][eip-2935-bytecode], which its deployment installs.

A call from the system address sets a hash.

It writes the first 32 bytes of the input, padded with zeros, at the parent number modulo 8191.

A call from any other address gets a hash.

Its input is a block number of 32 bytes, read big-endian.

It returns the word at the slot of that number modulo 8191.

It reverts when the input is not 32 bytes, or when the number is not one of the last 8191 blocks.

Each operation of [the EIP][eip-2935-contract] is a function here.

A theorem runs the code and shows that it computes that function.

The set specification uses a conservative one-counter budget from Shapella, which adds PUSH0.

The block number must be at least 1 and less than `2^256`, as the code computes on words.

From Pectra, a system call to the contract succeeds with the gas meter of its fork.

It leaves the storage that the EIP describes.

A call to empty code keeps the block state and records the address, at every fork from Pectra.

[eip-2935-bytecode]: https://eips.ethereum.org/EIPS/eip-2935#bytecode
[eip-2935-contract]: https://eips.ethereum.org/EIPS/eip-2935#block-hash-history-contract
-/

@[expose] public section

namespace EthLib.Execution.Blocks.HistoryStorage

open EthLib.Base (Fork U256 Address)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open GasCosts
open EthLib.Execution.Blocks.SystemContract

/-! ## The contract -/

/-- The number of hashes that the contract keeps, 8191, by EIP-2935. -/
def HISTORY_SERVE_WINDOW : Nat := 8191

/-- The code of the contract as one number: its 83 bytes, the first byte highest.

The input of the deployment transaction of EIP-2935 is 9 bytes of constructor, then these bytes.

Here they come in three runs of 40, 40 and 3 bytes. -/
def CODE_NUMBER : Nat :=
  0x3373fffffffffffffffffffffffffffffffffffffffe14604657602036036042575f356001430381 * 256 ^ 43 +
  0x11604257611fff81430311604257611fff9006545f5260205ff35b5f5ffd5b5f35611fff60014303 * 256 ^ 3 +
  0x065500

/-- The code of the history storage contract, 83 bytes, by EIP-2935. -/
def CODE : ByteArray := NatCode.ofNat CODE_NUMBER 83

/-- The opcode scan skips PUSH data and finds only instructions supported by both meters. -/
theorem supportedCode_CODE : SupportedCode CODE = true := by
  decide +kernel

/-- The slot of the block number `n`: `n` modulo 8191. -/
def slot (n : Nat) : U256 := BitVec.ofNat 256 (n % HISTORY_SERVE_WINDOW)

/-- The storage after the hash in `input` is set in the block `number`, from the storage `read`.

The slot of the parent number holds the word of the input, and every other slot keeps its word. -/
def setHash (number : Nat) (input : ByteArray) (read : U256 → U256) (s : U256) : U256 :=
  if s = slot (number - 1) then inputWord input else read s

/-- The hash that a call in the block `number` gets for `input`, from `read`, or none to revert.

The input must be 32 bytes, and its word `n` one of the last 8191 block numbers before `number`.

The hash is then the word at the slot of `n`. -/
def getHash (number : Nat) (read : U256 → U256) (input : ByteArray) : Option U256 :=
  if input.size = 32 ∧ (inputWord input).toNat < number ∧
      number ≤ (inputWord input).toNat + HISTORY_SERVE_WINDOW then
    some (read (slot (inputWord input).toNat))
  else none

/-! ## Words -/

/-- The word of the parent number, modulo 8191, is the slot of the parent number. -/
theorem mod_sub_eq_slot {number : Nat} (h1 : 1 ≤ number) (h2 : number < 2 ^ 256) :
    mod (sub (BitVec.ofNat 256 number) 1#256) 8191#256 = slot (number - 1) := by
  have hsub : (sub (BitVec.ofNat 256 number) 1#256).toNat = number - 1 := by
    simp only [sub, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]
    omega
  simp [mod, slot, HISTORY_SERVE_WINDOW, hsub]

/-! ## A call that sets a hash -/

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- A call from the system address sets a hash, as EIP-2935 describes.

It holds from Shapella, on a frame that may change the state.

The account of the contract exists.

The one-counter budget is 30,000 gas before Glamsterdam and 150,000 from Glamsterdam.

The block number is at least 1 and less than `2^256`.

The frame stops with no error and no output.

The state then holds the storage after the input is set in the block, at the contract.

It keeps the storage of every other account, the accounts and the codes. -/
theorem spec_set (hfork : .shapella ≤ fork)
    (hcaller : message.caller = SYSTEM_ADDRESS) (hstatic : message.isStatic = false)
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    (hnumber : 1 ≤ message.blockEnv.number) (hbound : message.blockEnv.number < 2 ^ 256)
    (hgas : 30000 * storageGasScale fork ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      evm.error = none ∧ evm.output = .empty ∧
      WritesStorage message.currentTarget
        (setHash message.blockEnv.number message.data (storageOf state message.currentTarget))
        state evm.state := by
  have hscale := one_le_storageGasScale fork
  evm_step [CODE, CODE_NUMBER]
  rw [hcaller, toU256_SYSTEM_ADDRESS]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  rw [mod_sub_eq_slot hnumber hbound]
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨s1, hs1, ho1, -, ha1, hc1, -, h1⟩ := sstore_of_account_total (code := CODE) (pc := 81)
    (gas := gas - 43) (rest := []) (key := slot (message.blockEnv.number - 1))
    (new := loadWord message.data 0 32)
    hberlin (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER]) hstatic rfl
    (by simp only [CALL_STIPEND]; omega)
    (Nat.le_trans (sstoreTotalCost_le hberlin _ _ _ _)
      (by omega)) hacc
  refine Triple.seq h1 ?_
  refine Spec.consequence (stop (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER])) (fun _ h => h) ?_
  rintro evm ⟨-, herr, hout, -, hst, -⟩
  refine ⟨by simpa using herr, hout, show WritesStorage _ _ _ _ from ⟨fun s => ?_,
    fun o k h => by rw [hst, ho1 o k (.inl h)], fun o => by rw [hst, ha1],
    fun c => by rw [hst, hc1]⟩⟩
  unfold storageOf setHash
  rw [hst]
  by_cases h : s = slot (message.blockEnv.number - 1)
  · subst h
    simp only [eq_self, ite_true]
    exact hs1
  · simp only [h, ite_false]
    exact ho1 _ _ (.inr fun e => h (U256.toBeBytes_inj e))

/-! ## A call that gets a hash -/

/-- SUB of a word `n` from a number at least `n` gives their difference. -/
private theorem toNat_sub_of_le {number : Nat} {n : U256} (hle : n.toNat ≤ number)
    (hbound : number < 2 ^ 256) : (sub (BitVec.ofNat 256 number) n).toNat = number - n.toNat := by
  have hn := n.isLt
  simp only [sub, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
  rw [show 2 ^ 256 - n.toNat + number = (number - n.toNat) + 2 ^ 256 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- MOD by 8191 gives the slot of a number. -/
theorem mod_eq_slot (n : U256) : mod n 8191#256 = slot n.toNat := by
  simp [mod, slot, HISTORY_SERVE_WINDOW]

/-- JUMPDEST, PUSH0, PUSH0 and REVERT, at byte 66, revert with no output. -/
private theorem get_revert {stack : List U256} (hfork : .shapella ≤ fork)
    (hstack : stack.length ≤ 4) (hgas : 10 ≤ gas) :
    Spec fork (At CODE message 66 stack .empty gas state substate returnData)
      (Answer state none) := by
  evm_step [CODE, CODE_NUMBER]
  exact revertEmpty hfork (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
    (by simp only [STACK_LIMIT]; omega) (by omega)

/-- From byte 54, the code reads the slot of the number `n` and returns its word. -/
private theorem get_load {n : U256} (hfork : .shapella ≤ fork) (hgas : 2300 ≤ gas) :
    Spec fork (At CODE message 54 [n] .empty gas state substate returnData)
      (Answer state (some (storageOf state message.currentTarget (slot n.toNat)))) := by
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  rw [mod_eq_slot]
  refine Triple.seq (sload (code := CODE) (pc := 59) (gas := gas - 11) (key := slot n.toNat)
    (rest := []) (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER]) rfl (Nat.le_trans (sloadPrice_le _) (by omega))) ?_
  refine Spec.consequence (returnWord hfork (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
    (Nat.le_trans (by omega) (Nat.sub_le_sub_left (sloadPrice_le _) _))) (fun _ h => h) ?_
  exact fun evm h => h.of_readsAs ((ReadsAs.refl _).recordStorageRead _ _)

/-- A call gets no hash for an input that is not 32 bytes, and otherwise checks its number. -/
theorem getHash_eq (number : Nat) (read : U256 → U256) (input : ByteArray) :
    getHash number read input = if input.size = 32 then
      (if (inputWord input).toNat < number then
        (if number ≤ (inputWord input).toNat + HISTORY_SERVE_WINDOW then
          some (read (slot (inputWord input).toNat))
        else none)
      else none)
    else none := by
  unfold getHash
  by_cases h1 : input.size = 32 <;> by_cases h2 : (inputWord input).toNat < number <;>
    by_cases h3 : number ≤ (inputWord input).toNat + HISTORY_SERVE_WINDOW <;> simp [h1, h2, h3]

/-- A call from an address other than the system address gets a hash, as EIP-2935 describes.

It holds from Shapella up to BPO5, the forks whose frames count gas as one number.

The frame has at least 5,000 gas.

The block number is at least 1 and less than `2^256`.

It assumes fewer than `2^256` bytes of input, which the size word of the EVM can hold.

The frame returns the hash that the storage holds for the input, or reverts with no output.

Its state reads as the state it starts from. -/
theorem spec_get (hfork : .shapella ≤ fork) (_hglam : fork < .glamsterdam)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS)
    (hnumber : 1 ≤ message.blockEnv.number) (hbound : message.blockEnv.number < 2 ^ 256)
    (hsize : message.data.size < 2 ^ 256) (hgas : 5000 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData)
      (Answer state (getHash message.blockEnv.number (storageOf state message.currentTarget)
        message.data)) := by
  have hc : equal (BitVec.ofNat 256 0xfffffffffffffffffffffffffffffffffffffffe)
      message.caller.toU256 = 0 := by
    rw [equal, ite_eq_right_iff]
    exact fun e => absurd e.symm (toU256_ne_of_ne_SYSTEM_ADDRESS hcaller)
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  rw [getHash_eq]
  simp only [inputWord]
  by_cases h : message.data.size = 32
  · have hs : sub (BitVec.ofNat 256 message.data.size) 32#256 = 0 := by rw [h]; rfl
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    have hpar : (sub (BitVec.ofNat 256 message.blockEnv.number) 1#256).toNat =
        message.blockEnv.number - 1 := toNat_sub_of_le (by simpa using hnumber) hbound
    simp only [h, ite_true]
    by_cases hlt : (loadWord message.data 0 32).toNat < message.blockEnv.number
    · have hc1 : greaterThan (loadWord message.data 0 32)
          (sub (BitVec.ofNat 256 message.blockEnv.number) 1#256) = 0 := by
        rw [greaterThan, ite_eq_right_iff, hpar]
        intro e
        exact absurd e (by omega)
      evm_step [CODE, CODE_NUMBER]
      evm_step [CODE, CODE_NUMBER]
      evm_step [CODE, CODE_NUMBER]
      evm_step [CODE, CODE_NUMBER]
      evm_step [CODE, CODE_NUMBER]
      evm_step [CODE, CODE_NUMBER]
      evm_step [CODE, CODE_NUMBER]
      evm_step [CODE, CODE_NUMBER]
      have hdiff := toNat_sub_of_le (n := loadWord message.data 0 32) (Nat.le_of_lt hlt) hbound
      simp only [hlt, ite_true]
      by_cases hle : message.blockEnv.number ≤
          (loadWord message.data 0 32).toNat + HISTORY_SERVE_WINDOW
      · have hc2 : greaterThan (sub (BitVec.ofNat 256 message.blockEnv.number)
            (loadWord message.data 0 32)) 8191#256 = 0 := by
          rw [greaterThan, ite_eq_right_iff, hdiff]
          simp only [BitVec.toNat_ofNat, HISTORY_SERVE_WINDOW] at hle ⊢
          omega
        evm_step [CODE, CODE_NUMBER]
        simp only [hle, ite_true]
        refine get_load hfork ?_
        omega
      · have hc2 : greaterThan (sub (BitVec.ofNat 256 message.blockEnv.number)
            (loadWord message.data 0 32)) 8191#256 ≠ 0 := by
          rw [greaterThan, hdiff]
          simp only [BitVec.toNat_ofNat, HISTORY_SERVE_WINDOW] at hle ⊢
          have hgt : message.blockEnv.number - (loadWord message.data 0 32).toNat >
              8191 % 2 ^ 256 := by omega
          simp [hgt]
        evm_step [CODE, CODE_NUMBER]
        simp only [hle, ite_false]
        exact get_revert hfork (by simp) (by omega)
    · have hc1 : greaterThan (loadWord message.data 0 32)
          (sub (BitVec.ofNat 256 message.blockEnv.number) 1#256) ≠ 0 := by
        rw [greaterThan, hpar]
        have hgt : (loadWord message.data 0 32).toNat > message.blockEnv.number - 1 := by omega
        simp [hgt]
      evm_step [CODE, CODE_NUMBER]
      evm_step [CODE, CODE_NUMBER]
      simp only [hlt, ite_false]
      exact get_revert hfork (by simp) (by omega)
  · have hs : sub (BitVec.ofNat 256 message.data.size) 32#256 ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      simp [sub, BitVec.toNat_sub, Nat.mod_eq_of_lt hsize] at this
      omega
    evm_step [CODE, CODE_NUMBER]
    simp only [h, ite_false]
    exact get_revert hfork (by simp) (by omega)

/-! ## The system call -/

/-- The history storage address is not a precompile. -/
theorem addedAt_HISTORY_STORAGE_ADDRESS :
    Precompiles.addedAt HISTORY_STORAGE_ADDRESS.toU256.toNat = none := by
  rw [HISTORY_STORAGE_ADDRESS, EthLib.Base.toNat_toU256_toAddressMasked]
  rfl

/-- The code is not a delegation indicator: it has 83 bytes, not 23. -/
theorem delegatedAddress_CODE : delegatedAddress CODE = none := by
  simp [delegatedAddress, isValidDelegation, CODE, NatCode.size_ofNat, DELEGATION_SIZE]

/-- From Pectra, a system call to the contract sets a hash.

It writes the first 32 bytes of its data, padded with zeros, at the slot of the parent number.

The account at the history storage address must hold the code of EIP-2935.

The block number is at least 1 and less than `2^256`.

The call succeeds with no output, whatever its data.

The storage of the contract is the storage after the data is set in the block.

A block passes the hash of its parent as that data, by EIP-2935.

The call keeps the storage of every other account, the accounts and the codes. -/
theorem systemCall_set {env : BlockEnvironment fork} {block : State.BlockState} {data : ByteArray}
    (hfork : .pectra ≤ fork)
    (hcode : codeAt block HISTORY_STORAGE_ADDRESS = .ok CODE)
    (hnumber : 1 ≤ env.number) (hbound : env.number < 2 ^ 256) :
    ∃ out, systemCall env block HISTORY_STORAGE_ADDRESS data = .ok out ∧ out.error = none ∧
      out.output = .empty ∧
      WritesStorage HISTORY_STORAGE_ADDRESS
        (setHash env.number data (storageOf (.ofBlock block) HISTORY_STORAGE_ADDRESS))
        (.ofBlock block) out.state :=
  systemCall_of_writesStorage_all (P := fun _ => True) (fun _ => .empty) _
    (Nat.le_trans (by decide) hfork) supportedCode_CODE hcode (by simp [CODE, NatCode.size_ofNat])
    addedAt_HISTORY_STORAGE_ADDRESS delegatedAddress_CODE trivial
    fun message _ _ hcaller htarget hstatic henv hdata hgas hacc _ => by
      subst henv hdata
      rw [← htarget]
      exact spec_set (Nat.le_trans (by decide) hfork) hcaller hstatic (htarget ▸ hacc)
        hnumber hbound (by
          rw [hgas]
          have := storageGasScale_le fork
          simp only [SYSTEM_TRANSACTION_GAS]
          omega)

/-- Empty history storage code keeps the body after the beacon call and records the address.

The empty-code condition is on that intermediate state, not on the state before the beacon call.

This is the silent failure required by [EIP-2935][eip2935].

It holds at every fork from Pectra, with either gas meter.

[eip2935]: https://eips.ethereum.org/EIPS/eip-2935#block-processing -/
theorem startSystemCalls_of_empty {env : BlockEnvironment fork} {body mid : BodyState}
    {out : SystemCallOutput} {parentHash : EthLib.Base.Hash32} (hfork : .pectra ≤ fork)
    (hbeacon : systemCall env body.block BEACON_ROOTS_ADDRESS
      ⟨(env.parentBeaconBlockRoot (Nat.le_trans (by decide) hfork)).toArray⟩ = .ok out)
    (hjoin : body.join out.state = .ok mid)
    (hcode : codeAt mid.block HISTORY_STORAGE_ADDRESS = .ok .empty) :
    startSystemCalls env parentHash body =
      .ok { mid with builder := mid.builder.record HISTORY_STORAGE_ADDRESS id } := by
  have hdencun : .dencun ≤ fork := Nat.le_trans (by decide) hfork
  simp only [startSystemCalls, hdencun, ↓reduceDIte, hbeacon, bind, Except.bind, hjoin,
    Except.mapError, hfork, ↓reduceIte,
    systemCall_of_empty (Nat.le_trans (by decide) hfork) hcode addedAt_HISTORY_STORAGE_ADDRESS,
    BodyState.join_recordAccountRead]

end EthLib.Execution.Blocks.HistoryStorage
