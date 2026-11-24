module

public import EthLib.Execution.Network.Transactions
public import EthLib.Execution.Transactions.Inclusion

/-!
# `Execution.Network.Pool`

The rules by which a node keeps a transaction that a peer sends, in its pool of transactions.

The source is the section Transaction Encoding and Validity of [`caps/eth.md`][eth] in devp2p.

[eth]: https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/caps/eth.md#transaction-encoding-and-validity

A transaction must pass these rules when it is received:

- its type must be known;
- its signature must be valid;
- its gas limit must cover its intrinsic gas;
- its sender must hold its cost;
- its nonce must be at least the nonce of its sender.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Transactions

/-- Check that a node may keep a transaction from a peer, at `fork` on the chain `chainId`.

It returns the sender.

The rules that need no state are those of a transaction alone, which go beyond the source.

They check the chain, the signature and the type, and that the gas limit covers the intrinsic gas.

The type must be active at the fork, which is stricter than the source and which it allows.

The source allows a node to enforce more rules.

A transaction that fails them never enters a block.

Then the nonce must be at least the nonce of the sender.

Last, the sender must hold the most the transaction can cost, with the value it sends.

The source writes that cost for a legacy transaction, as the gas limit times the gas price.

For later types, the price is the most fee per gas, and the most fee of the blobs adds to it.

The errors are those of a transaction alone, a nonce too low, and a balance below the cost. -/
def admitToPool (fork : Fork) (chainId : UInt64) (state : TransactionState)
    (tx : Transaction) : Except InclusionError Address := do
  -- The type is known, the signature is valid, and the gas limit covers the intrinsic gas.
  --
  -- Stricter than the source, which allows it: the type must be active at the fork.
  --
  -- The chain ID and the other rules of a transaction alone must hold too.
  let (sender, _) ← (checkTransaction fork chainId tx).mapError .transaction
  let account := state.getAccount sender
  -- The nonce is at least the nonce of the sender.
  --
  -- A nonce above that of the sender passes, unlike in a block.
  --
  -- The source leaves nonce gaps to the node; EthLib accepts any gap.
  --
  -- The source checks the balance first; the order only chooses the error.
  failIf (tx.nonce.toNat < account.nonce) (.nonceTooLow account.nonce tx.nonce.toNat)
  -- The balance covers `gas-limit * gas-price + value`.
  --
  -- For later types the price is the most fee per gas, and the most fee of the blobs adds to it.
  let cost := tx.maxGasFee + tx.value.toNat
  failIf (account.balance.toNat < cost) (.insufficientBalance account.balance.toNat cost)
  return sender

/-- What a node does with a peer that sent a transaction its pool refuses. -/
inductive PeerAction where
  /-- The node drops the transaction and keeps the peer. -/
  | discard
  /-- The node drops the transaction and should disconnect the peer. -/
  | disconnect
  deriving DecidableEq, Repr

/-- What a node does with a peer that sent a transaction that its pool refuses with an error.

A node should disconnect a peer that sends a transaction of a type that no fork defines.

It must keep a peer that sends any other invalid transaction, which may follow other rules.

A decoded transaction has a type that some fork defines, so only its decoding can disconnect. -/
def peerAction : InclusionError → PeerAction
  -- A type that no fork defines: the peer should be disconnected.
  --
  -- A type that a later fork defines keeps the peer, as any other invalid transaction does.
  | .transaction (.unsupportedType type) => if typeFork type = none then .disconnect else .discard
  -- Any other invalid transaction: the node keeps the peer.
  | _ => .discard

/-- Whether a node may send a transaction whole to its peers in a Transactions message.

[EIP-4844][eip-4844] says that a node never sends a blob transaction whole on its own.

It only announces it by its hash, and sends it when a peer asks.

[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#networking -/
def mayBroadcastWhole (tx : Transaction) : Bool :=
  -- EIP-4844: a blob transaction goes only by announcement and request.
  tx.type != BLOB_TX_TYPE

end EthLib.Execution.Network
