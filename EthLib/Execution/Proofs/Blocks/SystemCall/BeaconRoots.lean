module

public import EthLib.Execution.Proofs.Blocks.SystemCall.Contract

/-!
# Proofs: the beacon roots contract of EIP-4788 does what its EIP describes

The contract keeps one root per timestamp modulo 8191, in two rings of 8191 storage slots.

Its code is the 97 bytes of [EIP-4788][eip-4788-bytecode], which its deployment installs.

A call from the system address sets a root.

It writes the timestamp of the block at the slot of the timestamp modulo 8191.

It writes the first 32 bytes of the input, the root, 8191 slots above.

A call from any other address gets a root.

Its input is a timestamp of 32 bytes, read big-endian.

It returns the root of that timestamp when the ring still holds it.

It reverts when the input is not 32 bytes, is 0, or when the slot holds another timestamp.

Each operation of [the EIP][eip-4788-contract] is a function here.

A theorem runs the code and shows that it computes that function.

It holds from Shapella, which adds PUSH0, up to BPO5, for a frame that counts gas as one number.

From Dencun up to BPO5, a system call to the contract succeeds.

It leaves the storage that the EIP describes.

A call to empty code keeps the block state and records the address, at every fork from Dencun.

[eip-4788-bytecode]: https://eips.ethereum.org/EIPS/eip-4788#bytecode
[eip-4788-contract]: https://eips.ethereum.org/EIPS/eip-4788#beacon-roots-contract
-/

@[expose] public section

namespace EthLib.Execution.Blocks.BeaconRoots

open EthLib.Base (Fork U256 Address)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.SystemContract
open GasCosts

/-! ## The contract -/

/-- The number of roots that the contract keeps, 8191, by EIP-4788. -/
def HISTORY_BUFFER_LENGTH : Nat := 8191

/-- The code of the contract as one number: its 97 bytes, the first byte highest.

The input of the deployment transaction of EIP-4788 is 9 bytes of constructor, then these bytes.

Here they come in three runs of 40, 40 and 17 bytes. -/
def CODE_NUMBER : Nat :=
  0x3373fffffffffffffffffffffffffffffffffffffffe14604d57602036146024575f5ffd5b5f3580 * 256 ^ 57 +
  0x1560495762001fff810690815414603c575f5ffd5b62001fff01545f5260205ff35b5f5ffd5b6200 * 256 ^ 17 +
  0x1fff42064281555f359062001fff015500

/-- The code of the beacon roots contract, 97 bytes, by EIP-4788. -/
def CODE : ByteArray := NatCode.ofNat CODE_NUMBER 97

/-- The slot of the timestamp `t`: `t` modulo 8191. -/
def timestampSlot (t : U256) : U256 := BitVec.ofNat 256 (t.toNat % HISTORY_BUFFER_LENGTH)

/-- The slot of the root of the timestamp `t`: 8191 above the slot of `t`. -/
def rootSlot (t : U256) : U256 :=
  BitVec.ofNat 256 (t.toNat % HISTORY_BUFFER_LENGTH + HISTORY_BUFFER_LENGTH)

/-- The storage after a root is set at the timestamp `t` with the input `input`, from `read`.

The slot of `t` holds `t`, and the slot of its root holds the word of the input.

Every other slot keeps its word. -/
def setRoot (t : U256) (input : ByteArray) (read : U256 → U256) (slot : U256) : U256 :=
  if slot = timestampSlot t then t
  else if slot = rootSlot t then inputWord input
  else read slot

/-- The root that a call gets for the input `input`, from the storage `read`, or none to revert.

The input must be 32 bytes, and its word `t` must not be 0.

The slot of `t` must hold `t`, and the root is then the word 8191 slots above. -/
def getRoot (read : U256 → U256) (input : ByteArray) : Option U256 :=
  if input.size = 32 ∧ inputWord input ≠ 0 ∧
      read (timestampSlot (inputWord input)) = inputWord input then
    some (read (rootSlot (inputWord input)))
  else none

/-! ## Slots -/

/-- MOD by 8191 gives the slot of a timestamp. -/
theorem mod_eq_timestampSlot (t : U256) : mod t 8191#256 = timestampSlot t := by
  simp [mod, timestampSlot, HISTORY_BUFFER_LENGTH]

/-- ADD of 8191 to the slot of a timestamp gives the slot of its root. -/
theorem add_timestampSlot (t : U256) : add 8191#256 (timestampSlot t) = rootSlot t := by
  apply BitVec.eq_of_toNat_eq
  simp only [add, timestampSlot, rootSlot, HISTORY_BUFFER_LENGTH, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

/-- The slot of a timestamp is not the slot of its root. -/
theorem timestampSlot_ne_rootSlot (t : U256) : timestampSlot t ≠ rootSlot t := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [timestampSlot, rootSlot, HISTORY_BUFFER_LENGTH, BitVec.toNat_ofNat] at this
  omega

/-! ## A call that sets a root -/

variable {fork : Fork} {message : Message fork} {gas : Nat} {state : TransactionState}
  {substate : Substate} {returnData : ByteArray}

/-- From byte 87, the code writes the word of the input 8191 slots above `idx`.

It then stops with no error and no output. -/
private theorem set_tail (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam)
    (hstatic : message.isStatic = false)
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    (hgas : 25000 ≤ gas) (idx : U256) :
    Spec fork (At CODE message 87 [idx] .empty gas state substate returnData) fun evm =>
      evm.error = none ∧ evm.output = .empty ∧
      evm.state.getStorage message.currentTarget (U256.toBeBytes (add 8191#256 idx)) =
        inputWord message.data ∧
      (∀ other slot, other ≠ message.currentTarget ∨ slot ≠ U256.toBeBytes (add 8191#256 idx) →
        evm.state.getStorage other slot = state.getStorage other slot) ∧
      (∀ other, evm.state.getAccountOptional other = state.getAccountOptional other) ∧
      (∀ codeHash, evm.state.getCode codeHash = state.getCode codeHash) := by
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  obtain ⟨s', hs', ho', -, ha', hc', -, h'⟩ := sstore_of_account (code := CODE) (pc := 95)
    (gas := gas - 14) (rest := []) (key := add 8191#256 idx) (new := loadWord message.data 0 32)
    (Nat.le_trans (by decide) hfork) hglam (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER]) hstatic rfl (by simp only [CALL_STIPEND]; omega)
    (Nat.le_trans (sstoreCost_le (Nat.le_trans (by decide) hfork) hglam _ _ _ _)
      (by simp only [COLD_STORAGE_ACCESS, STORAGE_SET]; omega)) hacc
  refine Triple.seq h' ?_
  refine Spec.consequence (stop (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER])) (fun _ h => h) ?_
  rintro evm ⟨-, herr, hout, -, hst, -⟩
  exact ⟨by simpa using herr, hout, by rw [hst, hs']; rfl, fun o k h => by rw [hst, ho' o k h],
    fun o => by rw [hst, ha'], fun c => by rw [hst, hc']⟩

/-- A call from the system address sets a root, as EIP-4788 describes.

It holds from Shapella up to BPO5, on a frame that may change the state.

The account of the contract exists, and the frame has at least 50,000 gas.

The frame stops with no error and no output.

The storage of the contract is then the storage after the timestamp and the input are set.

It keeps the storage of every other account, the accounts and the codes. -/
theorem spec_set (hfork : .shapella ≤ fork) (hglam : fork < .glamsterdam)
    (hcaller : message.caller = SYSTEM_ADDRESS) (hstatic : message.isStatic = false)
    (hacc : (state.getAccountOptional message.currentTarget).isSome = true)
    (hgas : 50000 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData) fun evm =>
      evm.error = none ∧ evm.output = .empty ∧
      WritesStorage message.currentTarget
        (setRoot message.blockEnv.timestamp message.data (storageOf state message.currentTarget))
        state evm.state := by
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
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨s1, hs1, ho1, -, ha1, hc1, -, h1⟩ := sstore_of_account (code := CODE) (pc := 86)
    (gas := gas - 37) (rest := [mod message.blockEnv.timestamp 8191#256])
    (key := mod message.blockEnv.timestamp 8191#256) (new := message.blockEnv.timestamp)
    hberlin hglam (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER]) hstatic rfl
    (by simp only [CALL_STIPEND]; omega)
    (Nat.le_trans (sstoreCost_le hberlin hglam _ _ _ _)
      (by simp only [COLD_STORAGE_ACCESS, STORAGE_SET]; omega)) hacc
  refine Triple.seq h1 ?_
  refine Spec.consequence (set_tail hfork hglam hstatic (by rw [ha1]; exact hacc)
    (Nat.le_trans (by simp only [COLD_STORAGE_ACCESS, STORAGE_SET]; omega)
      (Nat.sub_le_sub_left (sstoreCost_le hberlin hglam _ _ _ _) _)) _) (fun _ h => h) ?_
  rintro evm ⟨herr, hout, hs2, ho2, ha2, hc2⟩
  rw [mod_eq_timestampSlot] at hs1 ho1 hs2 ho2
  rw [add_timestampSlot] at hs2 ho2
  refine ⟨herr, hout, show WritesStorage _ _ _ _ from ⟨fun slot => ?_,
    fun o k h => by rw [ho2 o k (.inl h), ho1 o k (.inl h)], fun o => by rw [ha2, ha1],
    fun c => by rw [hc2, hc1]⟩⟩
  unfold storageOf setRoot
  by_cases h1 : slot = timestampSlot message.blockEnv.timestamp
  · subst h1
    simp only [eq_self, ite_true]
    rw [ho2 _ _ (.inr fun e => timestampSlot_ne_rootSlot _ (U256.toBeBytes_inj e)), hs1]
  · simp only [h1, ite_false]
    by_cases h2 : slot = rootSlot message.blockEnv.timestamp
    · subst h2
      simp only [eq_self, ite_true]
      exact hs2
    · simp only [h2, ite_false]
      rw [ho2 _ _ (.inr fun e => h2 (U256.toBeBytes_inj e)),
        ho1 _ _ (.inr fun e => h1 (U256.toBeBytes_inj e))]

/-! ## A call that gets a root -/

/-- PUSH0, PUSH0 and REVERT, at byte 33, 57 or 74, revert with no output. -/
private theorem get_revert {pc : Nat} {stack : List U256} (hfork : .shapella ≤ fork)
    (hpc : pc = 33 ∨ pc = 57 ∨ pc = 74) (hstack : stack.length ≤ 4) (hgas : 10 ≤ gas) :
    Spec fork (At CODE message pc stack .empty gas state substate returnData)
      (Answer state none) := by
  rcases hpc with rfl | rfl | rfl <;>
  · exact revertEmpty hfork (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
      (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
      (by simp only [STACK_LIMIT]; omega) (by omega)

/-- From byte 60, the code reads the slot 8191 above `idx` and returns its word. -/
private theorem get_return {idx : U256} (hfork : .shapella ≤ fork) (hgas : 2200 ≤ gas) :
    Spec fork (At CODE message 60 [idx] .empty gas state substate returnData)
      (Answer state (some (state.getStorage message.currentTarget
        (U256.toBeBytes (add 8191#256 idx))))) := by
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  refine Triple.seq (sload (Nat.le_trans (by decide) hfork) (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER]) rfl (Nat.le_trans (sloadPrice_le _) (by omega))) ?_
  refine Spec.consequence (returnWord hfork (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
    (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
    (Nat.le_trans (by omega) (Nat.sub_le_sub_left (sloadPrice_le _) _))) (fun _ h => h) ?_
  exact fun evm h => h.of_readsAs ((ReadsAs.refl _).recordStorageRead _ _)

/-- From byte 53, the code returns the root when the word `v` of the slot is the timestamp `t`.

It reverts otherwise. -/
private theorem get_compare {v t idx : U256} (hfork : .shapella ≤ fork) (hgas : 2300 ≤ gas) :
    Spec fork (At CODE message 53 [v, t, idx] .empty gas state substate returnData)
      (Answer state (if v = t then some (state.getStorage message.currentTarget
        (U256.toBeBytes (add 8191#256 idx))) else none)) := by
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  by_cases h : v = t
  · have hc : equal v t ≠ 0 := by simp [equal, h]
    evm_step [CODE, CODE_NUMBER]
    simp only [h, ite_true]
    exact get_return hfork (by omega)
  · have hc : equal v t = 0 := by simp [equal, h]
    evm_step [CODE, CODE_NUMBER]
    simp only [h, ite_false]
    exact get_revert hfork (by decide) (by simp) (by omega)

/-- From byte 36, the code reads the word `t` of the input, and reverts when it is 0.

It then compares the word in the slot of `t` with `t`, and returns the root of `t` when equal.

It reverts otherwise. -/
private theorem get_lookup (hfork : .shapella ≤ fork) (hgas : 5000 ≤ gas) :
    Spec fork (At CODE message 36 [] .empty gas state substate returnData)
      (Answer state (if inputWord message.data = 0 then none
        else if storageOf state message.currentTarget (timestampSlot (inputWord message.data)) =
          inputWord message.data then
          some (storageOf state message.currentTarget (rootSlot (inputWord message.data)))
        else none)) := by
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  evm_step [CODE, CODE_NUMBER]
  by_cases h : inputWord message.data = 0
  · have h' : loadWord message.data 0 32 = 0 := h
    have hc : isZero (loadWord message.data 0 32) ≠ 0 := by simp [isZero, h']
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    simp only [h, ite_true]
    exact get_revert hfork (by decide) (by simp) (by omega)
  · have h' : loadWord message.data 0 32 ≠ 0 := h
    have hc : isZero (loadWord message.data 0 32) = 0 := by
      rw [isZero, ite_eq_right_iff]
      exact fun e => absurd e h'
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    evm_step [CODE, CODE_NUMBER]
    refine Triple.seq (sload (code := CODE) (pc := 52) (gas := gas - 42)
      (key := mod (loadWord message.data 0 32) 8191#256)
      (rest := [loadWord message.data 0 32, mod (loadWord message.data 0 32) 8191#256])
      (Nat.le_trans (by decide) hfork)
      (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER]) rfl
      (Nat.le_trans (sloadPrice_le _) (by omega))) ?_
    refine Spec.consequence (get_compare hfork (Nat.le_trans (by omega)
      (Nat.sub_le_sub_left (sloadPrice_le _) _))) (fun _ h => h) ?_
    intro evm hans
    have hans := hans.of_readsAs ((ReadsAs.refl _).recordStorageRead _ _)
    rw [mod_eq_timestampSlot, add_timestampSlot] at hans
    simp only [h, ite_false]
    exact hans

/-- A call gets no root for an input that is not 32 bytes, and otherwise looks its word up. -/
theorem getRoot_eq (read : U256 → U256) (input : ByteArray) :
    getRoot read input = if input.size = 32 then
      (if inputWord input = 0 then none
        else if read (timestampSlot (inputWord input)) = inputWord input then
          some (read (rootSlot (inputWord input)))
        else none)
    else none := by
  unfold getRoot
  by_cases h1 : input.size = 32 <;> by_cases h2 : inputWord input = 0 <;>
    by_cases h3 : read (timestampSlot (inputWord input)) = inputWord input <;> simp [h1, h2, h3]

/-- A call from an address other than the system address gets a root, as EIP-4788 describes.

It holds from Shapella up to BPO5, the forks whose frames count gas as one number.

The frame has at least 5,100 gas.

It assumes fewer than 2^256 bytes of input, which the size word of the EVM can hold.

The frame returns the root that the storage holds for the input, or reverts with no output.

Its state reads as the state it starts from. -/
theorem spec_get (hfork : .shapella ≤ fork) (_hglam : fork < .glamsterdam)
    (hcaller : message.caller ≠ SYSTEM_ADDRESS)
    (hsize : message.data.size < 2 ^ 256) (hgas : 5100 ≤ gas) :
    Spec fork (At CODE message 0 [] .empty gas state substate returnData)
      (Answer state (getRoot (storageOf state message.currentTarget) message.data)) := by
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
  rw [getRoot_eq]
  by_cases h : message.data.size = 32
  · have hs : equal (BitVec.ofNat 256 message.data.size) 32#256 ≠ 0 := by simp [equal, h]
    evm_step [CODE, CODE_NUMBER]
    simp only [h, ite_true]
    exact get_lookup hfork (by omega)
  · have hs : equal (BitVec.ofNat 256 message.data.size) 32#256 = 0 := by
      rw [equal, ite_eq_right_iff]
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsize] at this
      exact absurd this h
    evm_step [CODE, CODE_NUMBER]
    simp only [h, ite_false]
    exact get_revert hfork (by decide) (by simp) (by omega)

/-! ## The system call -/

/-- The beacon roots address is not a precompile. -/
theorem addedAt_BEACON_ROOTS_ADDRESS :
    Precompiles.addedAt BEACON_ROOTS_ADDRESS.toU256.toNat = none := by
  rw [BEACON_ROOTS_ADDRESS, EthLib.Base.toNat_toU256_toAddressMasked]
  rfl

/-- The code is not a delegation indicator: it has 97 bytes, not 23. -/
theorem delegatedAddress_CODE : delegatedAddress CODE = none := by
  simp [delegatedAddress, isValidDelegation, CODE, NatCode.size_ofNat, DELEGATION_SIZE]

/-- From Dencun up to BPO5, a system call to the contract sets a root.

It writes the first 32 bytes of its data as the root.

The account at the beacon roots address must hold the code of EIP-4788.

The call succeeds with no output, whatever its data.

The storage of the contract is the storage after the timestamp of the block and the data are set.

A block passes the root of its parent beacon block as that data, by EIP-4788.

The call keeps the storage of every other account, the accounts and the codes. -/
theorem systemCall_set {env : BlockEnvironment fork} {block : State.BlockState} {data : ByteArray}
    (hfork : .dencun ≤ fork) (hglam : fork < .glamsterdam)
    (hcode : codeAt block BEACON_ROOTS_ADDRESS = .ok CODE) :
    ∃ out, systemCall env block BEACON_ROOTS_ADDRESS data = .ok out ∧ out.error = none ∧
      out.output = .empty ∧
      WritesStorage BEACON_ROOTS_ADDRESS
        (setRoot env.timestamp data (storageOf (.ofBlock block) BEACON_ROOTS_ADDRESS))
        (.ofBlock block) out.state :=
  systemCall_of_writesStorage (P := fun _ => True) (fun _ => .empty) _
    (Nat.le_trans (by decide) hfork) hglam hcode (by simp [CODE, NatCode.size_ofNat])
    addedAt_BEACON_ROOTS_ADDRESS delegatedAddress_CODE trivial
    fun message _ _ hcaller htarget hstatic henv hdata hgas hacc _ => by
      subst henv hdata
      rw [← htarget]
      exact spec_set (Nat.le_trans (by decide) hfork) hglam hcaller hstatic (htarget ▸ hacc)
        (by rw [hgas]; decide)

/-- With no beacon roots code, the start calls record its address and continue to history storage.

The block state does not change before that second call.

This is the silent failure required by [EIP-4788][eip4788], including with the state gas meter.

[eip4788]: https://eips.ethereum.org/EIPS/eip-4788#block-processing -/
theorem startSystemCalls_of_empty {env : BlockEnvironment fork} {body : BodyState}
    {parentHash : EthLib.Base.Hash32} (hfork : .dencun ≤ fork)
    (hcode : codeAt body.block BEACON_ROOTS_ADDRESS = .ok .empty) :
    startSystemCalls env parentHash body = (do
      let mid := { body with builder := body.builder.record BEACON_ROOTS_ADDRESS id }
      if .pectra ≤ fork then do
        let out ← systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩
        (mid.join out.state).mapError EvmError.state
      else pure mid) := by
  simp only [startSystemCalls, hfork, ↓reduceDIte,
    systemCall_of_empty (Nat.le_trans (by decide) hfork) hcode addedAt_BEACON_ROOTS_ADDRESS,
    bind, Except.bind, BodyState.join_recordAccountRead, Except.mapError, pure, Except.pure]

end EthLib.Execution.Blocks.BeaconRoots
