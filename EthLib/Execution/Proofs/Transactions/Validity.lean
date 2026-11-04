module

public import EthLib.Execution.Transactions.Validity

/-!
# Proofs: the intrinsic gas and the rules of a transaction

The intrinsic gas is at least 21000.

The price of call data and of an access list adds up over concatenation, so it only grows.

A transaction that passes the rules has a gas limit that covers its least gas limit.

Its nonce is below `2^64 - 1`, and from Fusaka its gas limit is at most `2^24`.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.Evm.GasCosts

/-! ## The intrinsic gas -/

/-- The intrinsic gas is the sum of its five terms. -/
theorem intrinsicGas_eq (fork : Fork) (tx : Transaction) :
    intrinsicGas fork tx = TX_BASE + dataCost fork tx.data +
      (if tx.to.isNone then createCost fork tx.data.size else 0) +
      accessListCost tx.accesses + AUTH_PER_EMPTY_ACCOUNT * tx.authorizations.length :=
  rfl

/-- The intrinsic gas is at least 21000, at every fork. -/
theorem TX_BASE_le_intrinsicGas (fork : Fork) (tx : Transaction) :
    TX_BASE ≤ intrinsicGas fork tx := by
  rw [intrinsicGas_eq]
  omega

/-- A byte string has at most as many zero bytes as bytes. -/
theorem zeroBytes_le_size (data : ByteArray) : zeroBytes data ≤ data.size := by
  unfold zeroBytes
  calc _ ≤ data.data.toList.length := List.countP_le_length
    _ = data.size := Array.length_toList

/-- The zero bytes of two byte strings add up. -/
theorem zeroBytes_append (a b : ByteArray) : zeroBytes (a ++ b) = zeroBytes a + zeroBytes b := by
  simp only [zeroBytes, ByteArray.data_append, Array.toList_append, List.countP_append]

/-- The price of call data adds up over concatenation. -/
theorem dataCost_append (fork : Fork) (a b : ByteArray) :
    dataCost fork (a ++ b) = dataCost fork a + dataCost fork b := by
  have ha := zeroBytes_le_size a
  have hb := zeroBytes_le_size b
  simp only [dataCost, zeroBytes_append, ByteArray.size_append]
  rw [show a.size + b.size - (zeroBytes a + zeroBytes b) =
    (a.size - zeroBytes a) + (b.size - zeroBytes b) by omega]
  simp only [Nat.mul_add]
  omega

/-- More call data never costs less. -/
theorem dataCost_le_append (fork : Fork) (a b : ByteArray) :
    dataCost fork a ≤ dataCost fork (a ++ b) := by
  rw [dataCost_append]
  omega

/-- The price of access lists adds up over concatenation. -/
theorem accessListCost_append (a b : List Access) :
    accessListCost (a ++ b) = accessListCost a + accessListCost b := by
  simp [accessListCost, List.map_append, List.sum_append]

/-- A longer access list never costs less. -/
theorem accessListCost_le_append (a b : List Access) :
    accessListCost a ≤ accessListCost (a ++ b) := by
  rw [accessListCost_append]
  omega

/-- The least gas limit covers the intrinsic gas. -/
theorem intrinsicGas_le_minimumGas (fork : Fork) (tx : Transaction) :
    intrinsicGas fork tx ≤ minimumGas fork tx := by
  unfold minimumGas
  split <;> omega

/-- From Pectra, the least gas limit covers the call data floor. -/
theorem calldataFloor_le_minimumGas {fork : Fork} (hFork : fork ≥ .pectra) (tx : Transaction) :
    calldataFloor tx.data ≤ minimumGas fork tx := by
  simp only [minimumGas, hFork, ↓reduceIte]
  omega

/-! ## A valid transaction -/

/-- What a transaction that passes the gas, nonce and fee rules satisfies.

It returns its intrinsic gas, and its gas limit covers the least gas limit of the fork.

Its nonce is below `2^64 - 1`.

From Shapella its init code has at most 49152 bytes.

From Fusaka its gas limit is at most `2^24`. -/
theorem validateTransaction_ok {fork : Fork} {tx : Transaction} {gas : Nat}
    (h : validateTransaction fork tx = .ok gas) :
    gas = intrinsicGas fork tx ∧ minimumGas fork tx ≤ tx.gas.toNat ∧
      tx.nonce.toNat < 2 ^ 64 - 1 ∧
      (fork ≥ .shapella → tx.to = none → tx.data.size ≤ MAX_INIT_CODE_SIZE) ∧
      (fork ≥ .fusaka → tx.gas.toNat ≤ TX_MAX_GAS_LIMIT) := by
  unfold validateTransaction at h
  split at h
  · cases h
  · rename_i hGas
    split at h
    · cases h
    · rename_i hInit
      split at h
      · cases h
      · rename_i hCap
        split at h
        · cases h
        · rename_i hNonce
          split at h
          · cases h
          · cases h
            refine ⟨rfl, by omega, by omega, ?_, ?_⟩
            · intro hShapella hTo
              simp only [hTo, Option.isNone_none, true_and] at hInit
              exact Nat.not_lt.mp fun hlt => hInit ⟨hShapella, hlt⟩
            · intro hFusaka
              exact Nat.not_lt.mp fun hlt => hCap ⟨hFusaka, hlt⟩

/-- A valid transaction has a gas limit of at least 21000. -/
theorem validateTransaction_gas_ge {fork : Fork} {tx : Transaction} {gas : Nat}
    (h : validateTransaction fork tx = .ok gas) : TX_BASE ≤ tx.gas.toNat := by
  obtain ⟨-, hMin, -⟩ := validateTransaction_ok h
  have := TX_BASE_le_intrinsicGas fork tx
  have := intrinsicGas_le_minimumGas fork tx
  omega

/-- What a transaction that passes every rule alone satisfies.

Its gas and nonce pass the rules, and it signs no chain or the chain of the network.

Its signature names the sender, and its blobs and authorizations pass the rules. -/
theorem checkTransaction_ok {fork : Fork} {chainId : UInt64} {tx : Transaction}
    {sender : Address} {gas : Nat} (h : checkTransaction fork chainId tx = .ok (sender, gas)) :
    validateTransaction fork tx = .ok gas ∧ checkChainId fork chainId tx = .ok () ∧
      recoverSender fork tx = .ok sender ∧ checkContents fork tx = .ok () := by
  unfold checkTransaction at h
  cases hv : validateTransaction fork tx with
  | error e => simp [hv, bind, Except.bind] at h
  | ok g =>
    cases hc : checkChainId fork chainId tx with
    | error e => simp [hv, hc, bind, Except.bind] at h
    | ok u =>
      cases hs : recoverSender fork tx with
      | error e => simp [hv, hc, hs, bind, Except.bind] at h
      | ok a =>
        cases hk : checkContents fork tx with
        | error e => simp [hv, hc, hs, hk, bind, Except.bind] at h
        | ok w =>
          simp only [hv, hc, hs, hk, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, rfl, rfl, rfl⟩

end EthLib.Execution.Transactions
