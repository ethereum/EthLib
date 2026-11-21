module

public import EthLib.Execution.Network.Pool
public import EthLib.Execution.Proofs.Transactions.Inclusion

/-!
# Proofs: the pool of transactions

A node keeps a transaction exactly when three things hold.

It passes the checks of a transaction alone.

Its nonce is at least that of its sender, and its sender holds its cost.

A transaction that the next block could include is kept by the pool.

A transaction whose nonce is ahead of its sender's is kept, though no block can include it yet.

A node disconnects a peer only for a transaction of a type that no fork defines.

A Transactions message built from the transactions that may go whole holds no blob transaction.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Transactions

variable {fork : Fork} {chainId : UInt64} {state : TransactionState} {tx : Transaction}

/-- A node keeps a transaction exactly when three things hold.

The transaction alone passes, and names its sender.

Its nonce is at least the nonce of the sender.

The sender holds the most it can cost, with the value it sends. -/
theorem admitToPool_eq_ok_iff {sender : Address} :
    admitToPool fork chainId state tx = .ok sender ↔
      ∃ gas, checkTransaction fork chainId tx = .ok (sender, gas) ∧
        (state.getAccount sender).nonce ≤ tx.nonce.toNat ∧
        tx.maxGasFee + tx.value.toNat ≤ (state.getAccount sender).balance.toNat := by
  unfold admitToPool
  cases hc : checkTransaction fork chainId tx with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok p =>
    obtain ⟨s, g⟩ := p
    simp only [Except.mapError, bind, Except.bind, failIf, pure, Except.pure]
    constructor
    · intro h
      split at h
      · cases h
      split at h
      · cases h
      cases h
      exact ⟨g, rfl, by simp_all, by simp_all⟩
    · rintro ⟨g', hp, hn, hb⟩
      cases hp
      have fresh : ¬ tx.nonce.toNat < (state.getAccount sender).nonce := by omega
      have funded : ¬ (state.getAccount sender).balance.toNat < tx.maxGasFee + tx.value.toNat := by
        omega
      simp [fresh, funded]

/-- A transaction that may enter the next block at a state is kept by a pool at that state.

So a pool never refuses what the next block could include. -/
theorem admitToPool_of_checkInclusion {env : Evm.BlockEnvironment fork} {used : BlockGas}
    {included : Included} (h : checkInclusion chainId env used state tx = .ok included) :
    admitToPool fork chainId state tx = .ok included.sender := by
  obtain ⟨hChain, hSender, hValid, -, -, -, -, -, hContents, -, -, hNonce, hBalance, -⟩ :=
    checkInclusion_eq_ok_iff.mp h
  -- The transaction alone passes, with the sender and the intrinsic gas of the block's check.
  have alone : checkTransaction fork chainId tx = .ok (included.sender, included.intrinsicGas) := by
    simp [checkTransaction, hChain, hSender, hValid, hContents, bind, Except.bind, pure,
      Except.pure]
  exact admitToPool_eq_ok_iff.mpr ⟨_, alone, by omega, hBalance⟩

/-- A transaction that the pool keeps, with a nonce ahead of its sender's, enters no block yet.

A block needs the nonce of the sender at that state, while the pool takes any nonce from it on. -/
theorem admitToPool_future_nonce {sender : Address}
    (h : admitToPool fork chainId state tx = .ok sender)
    (ahead : (state.getAccount sender).nonce < tx.nonce.toNat)
    (env : Evm.BlockEnvironment fork) (used : BlockGas) (included : Included) :
    checkInclusion chainId env used state tx ≠ .ok included := by
  intro hIncluded
  -- The pool names the sender that the block's check names.
  have same := admitToPool_of_checkInclusion hIncluded
  rw [h] at same
  cases same
  have hNonce := (checkInclusion_ok hIncluded).2.2.2.2.2.2.2.2.1
  omega

/-- A node disconnects a peer only for a transaction of a type that no fork defines. -/
theorem peerAction_eq_disconnect_iff {error : InclusionError} :
    peerAction error = .disconnect ↔
      ∃ type, error = .transaction (.unsupportedType type) ∧ typeFork type = none := by
  cases error with
  | transaction e =>
    cases e with
    | unsupportedType type => cases h : typeFork type <;> simp [peerAction, h]
    | _ => simp [peerAction]
  | _ => simp [peerAction]

/-- The transactions that a node may send whole hold no blob transaction. -/
theorem transactions_no_blob (txs : List Transaction) :
    ∀ tx ∈ txs.filter mayBroadcastWhole, ∀ blob, tx ≠ .blob blob := by
  intro tx member blob same
  subst same
  simp [mayBroadcastWhole, Transaction.type, BLOB_TX_TYPE] at member

end EthLib.Execution.Network
