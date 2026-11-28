module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.Withdrawal
public import EthLib.Execution.Proofs.Evm.Call.Rebuild

/-!
# Proofs: the withdrawals keep the rebuild property

A withdrawal only adds ether to an account, so it writes no code and no storage word.

It may delete an empty account, which then has no nonce or code in the block state.

So the withdrawals keep the rebuild property of a state on their block, as a transaction does.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256)
open EthLib.Execution.Evm
open EthLib.Execution.State

/-- The withdrawals keep the rebuild property of a state on their block.

Each code read in the block state must have its hash.

That state must hold no delegation at an account with nonce 0. -/
theorem withdrawalState_rebuildState {fork : Fork} {block : BlockState}
    {withdrawals : List Withdrawal} {tx : TransactionState}
    (code : ∀ hash code, (TransactionState.ofBlock block).getCode hash = .ok code →
      keccak256 code = hash)
    (delegations : DelegationsHaveNonce (.ofBlock block))
    (h : withdrawalState fork block withdrawals = .ok tx) : RebuildState block tx :=
  foldlM_ok_invariant (RebuildState block)
    (fun _ _ _ previous step => (previous.createEther step).1)
    (RebuildState.ofBlock code delegations) h

end EthLib.Execution.Blocks
