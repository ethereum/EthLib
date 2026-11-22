module

public import EthLib.Execution.Blocks.BlockAccessList
public import EthLib.Execution.Blocks.Requests
public import EthLib.Execution.Blocks.Transition

/-!
# `Blocks.Genesis`

The genesis block of a chain: block 0, with no parent and an empty body.

Its header commits to the state that the chain starts with, its allocation.

The chain chooses the beneficiary, the difficulty, the gas limit and the time.

It also chooses the extra data, the mix hash and the nonce.

From London it also chooses the base fee, and from Dencun the excess blob gas.

From Glamsterdam it also chooses the slot number.

Every other field holds the value of a block with no parent and an empty body:

- the parent hash, the Bloom filter, the number and the gas used are zero
- the ommers hash and the roots of the transactions and the receipts are those of empty lists
- from Shapella, the withdrawals root is that of an empty list
- from Dencun, the blob gas used and the parent beacon block root are zero
- from Pectra, the requests hash is that of no request
- from Glamsterdam, the block access list hash is that of an empty list

Appendix I of the [Yellow Paper][yp], Berlin version, gives the genesis block of its first chain.

There the parent hash, the beneficiary, the Bloom filter, the number and the gas used are zero.

The ommers hash is that of an empty list, and the body is empty.

Its other values, such as the gas limit and the nonce, are those of that chain only.

The appendix sets the roots of the transactions and the receipts to 0.

Here they are the roots of empty tries, as its section 4.3.2 gives for an empty body.

The mainnet genesis block holds these roots too.

The EIPs add the fields of later forks:

- [EIP-1559][eip-1559]: the base fee
- [EIP-4895][eip-4895]: the withdrawals root
- [EIP-4844][eip-4844]: the blob gas used and the excess blob gas
- [EIP-4788][eip-4788]: the parent beacon block root
- [EIP-7685][eip-7685]: the requests hash
- [EIP-7928][eip-7928]: the block access list hash
- [EIP-7843][eip-7843]: the slot number

[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[eip-1559]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-1559.md#specification
[eip-4895]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-4895.md#new-field-in-the-execution-payload-header-withdrawals-root
[eip-4844]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-4844.md#header-extension
[eip-4788]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-4788.md#block-structure-and-validity
[eip-7685]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7685.md#block-header
[eip-7928]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7928.md#block-structure-modification
[eip-7843]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7843.md#header-extension
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.State (State stateRoot)
open EthLib.Execution.Transactions
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The fields of a genesis header that a chain chooses. -/
structure GenesisParams where
  /-- The beneficiary. -/
  coinbase : Address
  /-- The difficulty. -/
  difficulty : Nat
  /-- The gas limit. -/
  gasLimit : Nat
  /-- The time, in seconds. -/
  timestamp : U256
  /-- The extra data. -/
  extraData : ByteArray
  /-- The mix hash, which holds the randomness of the beacon chain from Paris. -/
  prevRandao : Bytes32
  /-- The nonce. -/
  nonce : Bytes8
  /-- The base fee, from London.

  By EIP-1559, the first block of London has the initial base fee. -/
  baseFeePerGas : Nat := INITIAL_BASE_FEE
  /-- The excess blob gas, from Dencun. -/
  excessBlobGas : UInt64 := 0
  /-- The slot number, from Glamsterdam. -/
  slotNumber : UInt64 := 0

/-- The genesis header at `fork` whose state has the root `root`. -/
def genesisHeader (fork : Fork) (params : GenesisParams) (root : Hash32) :
    Except BlockError (Header fork) := do
  -- `TRIE(∅)` of an empty body, as §4.3.2 gives, where Appendix I writes 0.
  --
  -- The withdrawals root is `TRIE(∅)` too, by EIP-4895.
  let emptyRoot ← (transactionsRoot []).mapError .trie
  let emptyReceipts ← (receiptsRoot (fork := fork) []).mapError .trie
  let emptyWithdrawals ← (withdrawalsRoot []).mapError .trie
  let emptyAccessList ← (BlockAccessList.hash []).mapError .encoding
  return {
    -- Appendix I: `H_p = 0`, and `H_o = KEC(RLP(()))`, the hash of no ommers.
    parentHash := 0
    ommersHash := EMPTY_OMMER_HASH
    -- The chain chooses `H_c`, where Appendix I has `0_160`.
    coinbase := params.coinbase
    -- `H_r`, the root of the allocation.
    stateRoot := root
    transactionsRoot := emptyRoot
    receiptRoot := emptyReceipts
    -- `H_b = 0`, `H_i = 0` and `H_g = 0`.
    --
    -- The chain chooses `H_d`, `H_l`, `H_s`, `H_x`, `H_m` and `H_n`.
    bloom := 0
    difficulty := params.difficulty
    number := 0
    gasLimit := params.gasLimit
    gasUsed := 0
    timestamp := params.timestamp
    extraData := params.extraData
    prevRandao := params.prevRandao
    nonce := params.nonce
    -- EIP-1559: the chain chooses the base fee.
    baseFeePerGas := fun _ => params.baseFeePerGas
    -- EIP-4895: `TRIE(∅)`, no withdrawal.
    withdrawalsRoot := fun _ => emptyWithdrawals
    -- EIP-4844: no blob gas used; the chain chooses the excess blob gas.
    blobGasUsed := fun _ => 0
    excessBlobGas := fun _ => params.excessBlobGas
    -- EIP-4788: no parent beacon block, so 0.
    parentBeaconBlockRoot := fun _ => 0
    -- EIP-7685: the hash of no request.
    requestsHash := fun _ => requestsHash []
    -- EIP-7928: the hash of an empty block access list.
    blockAccessListHash := fun _ => emptyAccessList
    -- EIP-7843: the chain chooses the slot number.
    slotNumber := fun _ => params.slotNumber
  }

/-- The genesis block at `fork` of a chain that starts with the state `alloc`. -/
def genesis (fork : Fork) (params : GenesisParams) (alloc : State) :
    Except BlockError (Block fork Transaction) := do
  -- `TRIE(L_S(sigma))` of the allocation, §4.1.
  let root ← (stateRoot keccak256 alloc).mapError .trie
  -- The header, then no transaction, no ommer and, from Shapella, no withdrawal.
  return ⟨← genesisHeader fork params root, [], [], fun _ => []⟩

end EthLib.Execution.Blocks
