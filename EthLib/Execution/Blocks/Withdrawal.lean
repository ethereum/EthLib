module

public import EthLib.Base.Address
public import EthLib.Execution.State.Tracker
public import EthLib.Serialization.Rlp.Codec

/-!
# `Blocks.Withdrawal`

A withdrawal moves ether from the consensus layer to an account of the execution layer.

[EIP-4895](https://eips.ethereum.org/EIPS/eip-4895#specification) adds withdrawals at Shapella.

Its RLP form is the list of its four fields, in order.

After the transactions of a block, each withdrawal adds its amount to the balance of its account.

The amount is in Gwei, so the balance grows by the amount times `10^9` wei.

A withdrawal costs no gas.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp

/-- A withdrawal, as EIP-4895 defines it. -/
structure Withdrawal where
  /-- The position of the withdrawal among all withdrawals, from 0. -/
  index : UInt64
  /-- The index of the validator on the consensus layer. -/
  validatorIndex : UInt64
  /-- The account that receives the ether. -/
  address : Address
  /-- The amount, in Gwei. -/
  amount : UInt64
  deriving DecidableEq, Repr

namespace Withdrawal

/-- The item of a withdrawal: the list `[index, validator_index, address, amount]`. -/
def toItem (w : Withdrawal) : Item :=
  .list [Codec.toItem w.index, Codec.toItem w.validatorIndex, Codec.toItem w.address,
    Codec.toItem w.amount]

/-- The withdrawal that an item holds: a list of its four fields, in order. -/
def ofItem (item : Item) : Except RlpError Withdrawal := do
  let items ← item.fields 4
  let (index, items) ← Item.readField (α := UInt64) 4 items
  let (validatorIndex, items) ← Item.readField (α := UInt64) 4 items
  let (address, items) ← Item.readField (α := Address) 4 items
  let (amount, _) ← Item.readField (α := UInt64) 4 items
  return ⟨index, validatorIndex, address, amount⟩

end Withdrawal

instance : Codec Withdrawal := ⟨Withdrawal.toItem, Withdrawal.ofItem⟩

open EthLib.Execution.State

/-- The wei in one Gwei. -/
def GWEI_TO_WEI : Nat := 10 ^ 9

/-- Add the amount of each withdrawal, in wei, to the balance of its account, in order.

The writes join the block, as the writes of a transaction do.

It fails only when a balance would reach `2^256`, which EIP-4895 leaves out. -/
def processWithdrawals (fork : Fork) (block : BlockState) (withdrawals : List Withdrawal) :
    Except StateError BlockState := do
  let tx ← withdrawals.foldlM
    (fun tx w => tx.createEther fork w.address (BitVec.ofNat 256 (w.amount.toNat * GWEI_TO_WEI)))
    (TransactionState.ofBlock block)
  return tx.incorporateTxIntoBlock.parent

end EthLib.Execution.Blocks
