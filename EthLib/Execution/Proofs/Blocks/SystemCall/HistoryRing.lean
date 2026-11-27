module

public import EthLib.Execution.Proofs.Blocks.StorageInvariant
public import EthLib.Execution.Proofs.Blocks.SystemCall.HistoryStorage
public import EthLib.Execution.Proofs.Evm.Logic.LessGas

/-!
# Proofs: the history storage contract of EIP-2935 keeps its ring in every reachable state

The contract keeps the hashes in its first 8191 slots, so every other slot reads 0.

Each call that runs its code keeps that, whoever calls it and whatever its gas.

So every state that a chain reaches from Cancun to BPO5 keeps it.

The chain must start where the contract holds its code and its storage meets the ring.

The proof assumes that no other code has the Keccak-256 hash of the code, which SOUNDNESS.md lists.

Source: [EIP-2935][eip-2935-contract].

[eip-2935-contract]: https://eips.ethereum.org/EIPS/eip-2935#block-hash-history-contract
-/

@[expose] public section

namespace EthLib.Execution.Blocks.HistoryStorage

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Blocks.SystemContract

/-- Every slot of the storage at or above 8191 reads 0. -/
def Ring (storage : Bytes32 → U256) : Prop :=
  ∀ slot : U256, HISTORY_SERVE_WINDOW ≤ slot.toNat → storage (U256.toBeBytes slot) = 0

/-- The empty storage is a ring. -/
theorem ring_empty : Ring fun _ => 0 := fun _ _ => rfl

variable {fork : Fork}

/-- A state that reads as a state where the contract keeps its ring keeps it too. -/
theorem goodAt_of_readsAs {tx S : TransactionState}
    (h : GoodAt HISTORY_STORAGE_ADDRESS CODE Ring S) (reads : ReadsAs tx S) :
    GoodAt HISTORY_STORAGE_ADDRESS CODE Ring tx :=
  h.of_keepsAt (.of_eq (by simp only [TransactionState.getAccount,
      (reads.1 HISTORY_STORAGE_ADDRESS List.not_mem_nil).1])
    reads.2 (funext (reads.1 HISTORY_STORAGE_ADDRESS List.not_mem_nil).2.1))

/-- The write of a call from the system address keeps the ring. -/
theorem goodAt_of_writesStorage {S tx : TransactionState} {number : Nat} {word : U256}
    (h : GoodAt HISTORY_STORAGE_ADDRESS CODE Ring S)
    (writes : WritesStorage HISTORY_STORAGE_ADDRESS
      (fun s => if s = setKey number then word else storageOf S HISTORY_STORAGE_ADDRESS s) S tx) :
    GoodAt HISTORY_STORAGE_ADDRESS CODE Ring tx := by
  obtain ⟨⟨hhash, hcode⟩, hring⟩ := h
  obtain ⟨hstore, -, hacc, hcodes⟩ := writes
  refine ⟨⟨by simp only [TransactionState.getAccount, hacc]; exact hhash,
    (hcodes _).trans hcode⟩, fun slot hslot => ?_⟩
  -- The written slot is below 8191.
  have hne : slot ≠ setKey number := fun e => by
    have := toNat_setKey_lt number
    rw [← e] at this
    omega
  have := hstore slot
  simp only [storageOf, hne, ↓reduceIte] at this
  rw [this]
  exact hring slot hslot

/-- The frame of a call that runs the code, from the system address or not, at any gas. -/
private theorem hoare_frame (hyp : CodeHyp CODE) (hfork : .shapella ≤ fork)
    {message : Message fork}
    {state : TransactionState} {substate : Substate}
    (good : GoodAt HISTORY_STORAGE_ADDRESS CODE Ring state)
    (hat : message.currentTarget = HISTORY_STORAGE_ADDRESS) {g : Nat}
    (hg : 30000 * storageGasScale fork ≤ g) :
    HoareG fork (At CODE message 0 [] .empty g state substate .empty) fun z =>
      (z.running = false ∧ GoodAt HISTORY_STORAGE_ADDRESS CODE Ring z.state) ∨ Stuck z := by
  have hscale := one_le_storageGasScale fork
  -- The account of the contract exists, since it holds code.
  have hacc : (state.getAccountOptional message.currentTarget).isSome = true := by
    rw [hat]
    cases h : state.getAccountOptional HISTORY_STORAGE_ADDRESS with
    | some _ => rfl
    | none =>
      have := good.1.1
      simp [TransactionState.getAccount, h, State.EMPTY_ACCOUNT] at this
      exact absurd this.symm hyp.hash_ne
  by_cases hbound : message.blockEnv.number < 2 ^ 256
  · by_cases hcaller : message.caller = SYSTEM_ADDRESS
    · cases hstatic : message.isStatic
      · -- A call from the system address writes the slot of the parent number.
        refine Triple.consequence (specG_set hfork hcaller hstatic hacc hbound hg) (fun _ h => h)
          fun _ h => .inl ⟨h.1, goodAt_of_writesStorage good (hat ▸ h.2.2.2)⟩
      · -- A static call from the system address is stuck at SSTORE.
        have hc : equal (BitVec.ofNat 256 0xfffffffffffffffffffffffffffffffffffffffe)
            message.caller.toU256 ≠ 0 := by
          rw [hcaller, toU256_SYSTEM_ADDRESS]
          simp [equal]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        exact Triple.consequence (sstore_stuck (by evm_code [CODE, CODE_NUMBER])
          (by evm_code [CODE, CODE_NUMBER]) (.inl hstatic)) (fun _ h => h) fun _ h => .inr h
    · -- Any other call only reads.
      exact Triple.consequence (specG_reads hfork hcaller hbound (by omega)) (fun _ h => h)
        fun _ h => .inl ⟨h.1, goodAt_of_readsAs good h.2⟩
  · -- A block number that does not fit a word makes NUMBER fail.
    have hbig : 2 ^ 256 ≤ message.blockEnv.number := Nat.le_of_not_lt hbound
    have stuck : ∀ {pc : Nat} {stack : List U256} {g' : Nat}, (hlt : pc < CODE.size) →
        CODE[pc] = 0x43 →
        HoareG fork (At CODE message pc stack .empty g' state substate .empty) fun z =>
          (z.running = false ∧ GoodAt HISTORY_STORAGE_ADDRESS CODE Ring z.state) ∨ Stuck z :=
      fun hlt hbyte => Triple.consequence (number_stuck hlt hbyte hbig) (fun _ h => h)
        fun _ h => .inr h
    by_cases hcaller : message.caller = SYSTEM_ADDRESS
    · -- A call from the system address reads the number before it writes.
      have hc : equal (BitVec.ofNat 256 0xfffffffffffffffffffffffffffffffffffffffe)
          message.caller.toU256 ≠ 0 := by
        rw [hcaller, toU256_SYSTEM_ADDRESS]
        simp [equal]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      exact stuck (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
    · have hc : equal (BitVec.ofNat 256 0xfffffffffffffffffffffffffffffffffffffffe)
          message.caller.toU256 = 0 := by
        rw [equal, ite_eq_right_iff]
        exact fun e => absurd e.symm (toU256_ne_of_ne_SYSTEM_ADDRESS hcaller)
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      evm_stepG [CODE, CODE_NUMBER]
      by_cases hs : sub (BitVec.ofNat 256 message.data.size) 32#256 = 0
      · -- An input of 32 bytes reads the number.
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        evm_stepG [CODE, CODE_NUMBER]
        exact stuck (by evm_code [CODE, CODE_NUMBER]) (by evm_code [CODE, CODE_NUMBER])
      · -- Any other input reverts first.
        evm_stepG [CODE, CODE_NUMBER]
        exact Triple.consequence (get_revertG hfork (by simp) (by omega)) (fun _ h => h)
          fun _ h => .inl ⟨h.1, goodAt_of_readsAs good h.2.1⟩

/-- What the proofs ask of the code of the contract holds when no other code has its hash. -/
theorem codeHyp_CODE
    (hashOnly : ∀ other, Cryptography.Hash.Keccak.keccak256 other =
      Cryptography.Hash.Keccak.keccak256 CODE → other = CODE) : CodeHyp CODE where
  -- The empty code has another hash, since it is not the code.
  hash_ne h := by
    have := congrArg ByteArray.size (hashOnly .empty h.symm)
    simp [CODE, NatCode.size_ofNat] at this
  noDelegate := delegatedAddress_CODE
  hashOnly := hashOnly

/-- From Shapella, each call that runs the code keeps the ring, with one counter of gas. -/
theorem framesKeepCode (hyp : CodeHyp CODE) (hfork : .shapella ≤ fork) :
    FramesKeepCode HISTORY_STORAGE_ADDRESS CODE fork Nat Ring := by
  intro bound runChild _ message state substate meter after within hat hcode _ _ good hrun herr
  have start : At CODE message 0 [] .empty meter state substate .empty
      (startFrame message state substate meter) := by
    refine ⟨hcode, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [← hcode]
    rfl
  exact low_of_halts_or_stuck (B := 30000 * storageGasScale fork)
    (fun _ hg => hoare_frame hyp hfork good hat hg) start within hrun herr

/-- From Cancun to BPO5, the ring holds in every state that a chain reaches.

The chain must start where the contract holds its code and its storage meets the ring.

It assumes that no other code has the Keccak-256 hash of the code.

That is an assumption on Keccak-256, which SOUNDNESS.md lists. -/
theorem ring_of_reaches
    (hashOnly : ∀ other, Cryptography.Hash.Keccak.keccak256 other =
      Cryptography.Hash.Keccak.keccak256 CODE → other = CODE)
    {chain chain' : BlockChain}
    (reaches : chain.Reaches (fun fork => .dencun ≤ fork ∧ fork < .glamsterdam) chain')
    (start : GoodAt HISTORY_STORAGE_ADDRESS CODE Ring (.ofBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩)) :
    GoodAt HISTORY_STORAGE_ADDRESS CODE Ring (.ofBlock ⟨chain'.state, ∅, ∅, ∅, ∅⟩) :=
  reaches.goodAt (codeHyp_CODE hashOnly) (fun _ h => h.1)
    (fun _ h _ => framesKeepCode (codeHyp_CODE hashOnly) (Nat.le_trans (by decide) h.1))
    (fun _ h hg => absurd h.2 (Nat.not_lt.mpr hg)) start

end EthLib.Execution.Blocks.HistoryStorage
