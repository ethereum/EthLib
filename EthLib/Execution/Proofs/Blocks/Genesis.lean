module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.Genesis

/-!
# Proofs: the genesis block

The genesis header of a state root holds that root.

The genesis block of an allocation commits to the root of that allocation.

It is block 0, with no parent and an empty body.

Its header holds the fields that the chain chooses.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State (State stateRoot)
open EthLib.Execution.Transactions
open EthLib.Cryptography.Hash.Keccak (keccak256)

variable {fork : Fork} {params : GenesisParams}

/-- A genesis header has number 0, the zero parent hash and the state root it was given.

It holds the fields that the chain chooses, and no gas is used. -/
theorem of_genesisHeader {root : Hash32} {header : Header fork}
    (h : genesisHeader fork params root = .ok header) :
    header.stateRoot = root ∧ header.number = 0 ∧ header.parentHash = 0 ∧ header.gasUsed = 0 ∧
      header.ommersHash = EMPTY_OMMER_HASH ∧ header.coinbase = params.coinbase ∧
      header.difficulty = params.difficulty ∧ header.gasLimit = params.gasLimit ∧
      header.timestamp = params.timestamp ∧ header.extraData = params.extraData ∧
      header.prevRandao = params.prevRandao ∧ header.nonce = params.nonce := by
  unfold genesisHeader at h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A genesis header holds the fields of later forks that the chain chooses.

Its Bloom filter is empty, and no blob gas is used.

It names no parent beacon block, and it commits to no request. -/
theorem of_genesisHeader_since {root : Hash32} {header : Header fork}
    (h : genesisHeader fork params root = .ok header) :
    header.bloom = 0 ∧ (∀ hf, header.baseFeePerGas hf = params.baseFeePerGas) ∧
      (∀ hf, header.excessBlobGas hf = params.excessBlobGas) ∧
      (∀ hf, header.slotNumber hf = params.slotNumber) ∧ (∀ hf, header.blobGasUsed hf = 0) ∧
      (∀ hf, header.parentBeaconBlockRoot hf = 0) ∧
      (∀ hf, header.requestsHash hf = requestsHash []) := by
  unfold genesisHeader at h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  cases h
  exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The genesis block of an allocation commits to the state root of the allocation.

Its header is the genesis header of that root, and its body is empty. -/
theorem of_genesis {alloc : State} {block : Block fork Transaction}
    (h : genesis fork params alloc = .ok block) :
    stateRoot keccak256 alloc = .ok block.header.stateRoot ∧
      genesisHeader fork params block.header.stateRoot = .ok block.header ∧
      block.transactions = [] ∧ block.ommers = [] := by
  unfold genesis at h
  obtain ⟨root, hRoot, h⟩ := bind_ok_iff.mp h
  obtain ⟨header, hHeader, h⟩ := bind_ok_iff.mp h
  cases h
  have hRoot' : stateRoot keccak256 alloc = .ok root := by
    cases hs : stateRoot keccak256 alloc <;> simp_all [Except.mapError]
  have hState := (of_genesisHeader hHeader).1
  refine ⟨?_, ?_, rfl, rfl⟩
  · rw [hState]; exact hRoot'
  · simp only [hState]; exact hHeader

end EthLib.Execution.Blocks
