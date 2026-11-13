module

public import EthLib.Execution.Rpc.Methods
public import EthLib.Execution.Proofs.State.Tracker
public import EthLib.Execution.Proofs.Rpc.Errors
public import EthLib.Execution.Proofs.Transactions.Envelope

/-!
# Proofs: the submission of a raw transaction

The hash that a submission returns is the hash of the transaction that its raw form holds.

When the first byte of the raw form is not 3, that hash is the Keccak-256 hash of the raw bytes.

The method of the dispatcher reads the raw bytes and returns that hash.

The next block in which a transaction is checked has the next base fee of the fee history.

A future nonce never fails the checks of the nonce.

Each code that names the condition of a failed check is in a group that the method lists.

It lies in the range of that group.

Two failed checks get the same code only when they are of the same kind.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Execution.Transactions
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The hash of an accepted submission is the hash of the transaction of its raw form.

That transaction leaves out the blobs, the commitments and the proofs of a network form. -/
theorem ChainView.sendRawTransaction_hash {v : ChainView} {bytes : ByteArray} {h : Hash32}
    (hok : v.sendRawTransaction bytes = .ok h) :
    ∃ raw, decodeRawTransaction (v.head.nextFork v.config) bytes = .ok raw ∧
      transactionHash raw.tx = .ok h := by
  unfold ChainView.sendRawTransaction at hok
  simp only [Except.mapError, bind, Except.bind] at hok
  rcases hd : decodeRawTransaction (v.head.nextFork v.config) bytes with e | raw
  · rw [hd] at hok
    simp at hok
  · refine ⟨raw, rfl, ?_⟩
    rw [hd] at hok
    rcases raw with tx | w <;> dsimp only [RawTransaction.tx] at hok ⊢
    · split at hok
      · cases hok
      · split at hok
        · cases hok
        · cases hok
          assumption
    · split at hok
      · split at hok
        · split at hok
          · cases hok
          · split at hok
            · cases hok
            · cases hok
              assumption
        · simp at hok
      · simp at hok

/-- The hash of an accepted submission whose first byte is not 3 is the hash of its bytes.

Only a blob transaction, of type 3, comes in a network form. -/
theorem ChainView.sendRawTransaction_keccak {v : ChainView} {bytes : ByteArray} {h : Hash32}
    (hok : v.sendRawTransaction bytes = .ok h) (hType : bytes.data[0]? ≠ some 3) :
    h = keccak256 bytes := by
  obtain ⟨raw, hd, hh⟩ := ChainView.sendRawTransaction_hash hok
  unfold decodeRawTransaction at hd
  simp only [hType, false_and, ite_false] at hd
  rcases hdt : decodeTransaction (v.head.nextFork v.config) bytes with e | t
  · rw [hdt] at hd
    cases hd
  · rw [hdt] at hd
    cases hd
    have he := (encodeTransaction_of_decodeTransaction hdt).1
    simp only [RawTransaction.tx, transactionHash, he] at hh
    cases hh
    rfl

/-- The method answers `eth_sendRawTransaction` with the hash of the bytes that it reads. -/
theorem ChainView.call_sendRawTransaction (v : ChainView) (j : Lean.Json) :
    v.call "eth_sendRawTransaction" [j] =
      (ChainView.readParam (Serialization.JsonRpc.bytes "transaction") j >>= fun b =>
        hash32Json <$> v.sendRawTransaction b) := rfl

/-- The next block in which a transaction is checked has the next base fee of the fee history. -/
theorem ChainView.baseFeeOf_nextEnvironment (v : ChainView) :
    baseFeeOf v.nextEnvironment =
      if .london ≤ v.head.nextFork v.config then v.baseFee else 0 := by
  unfold baseFeeOf
  split <;> simp_all [ChainView.nextEnvironment, ChainView.baseFee]

/-- The sender has at least the nonce of the transaction in the state of the future nonce. -/
theorem withFutureNonce_nonce (state : State.TransactionState) (sender : Address)
    (tx : Transaction) :
    tx.nonce.toNat ≤ ((withFutureNonce state sender tx).getAccount sender).nonce := by
  unfold withFutureNonce
  dsimp only
  split
  · simp [State.TransactionState.getAccount,
      State.TransactionState.getAccountOptional_setAccount_self]
  · omega

/-- Each code that names the condition of a failed check is in a group that the method lists.

It lies in the range of that group. -/
theorem rpcCode_mem {e : InclusionError} {c : ErrorCode} (h : rpcCode e = some c) :
    ∃ g ∈ submitErrorGroups, c ∈ g.errors ∧
      ∃ r, g.range = some r ∧ r.1 ≤ c.code ∧ c.code ≤ r.2 := by
  have hc : c ∈ [intrinsicGasTooLow, gasLimitAboveBlock, priorityFeeAboveCap, invalidSender,
      feeCapBelowBaseFee, nonceTooLow, nonceTooHigh, insufficientFunds] := by
    unfold rpcCode at h
    split at h <;> first | (cases h; simp; done) | cases h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- Two failed checks with the same code are of the same kind. -/
theorem rpcCode_injective {e₁ e₂ : InclusionError} {c₁ c₂ : ErrorCode}
    (h₁ : rpcCode e₁ = some c₁) (h₂ : rpcCode e₂ = some c₂) (hc : c₁.code = c₂.code) :
    e₁.code = e₂.code := by
  unfold rpcCode at h₁ h₂
  split at h₁ <;> split at h₂ <;>
    first | (cases h₁; cases h₂) | cases h₁ | cases h₂
  all_goals first | rfl | (exfalso; revert hc; decide +kernel)

end EthLib.Execution.Rpc
