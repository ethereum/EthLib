module

public import EthLib.Execution.Transactions.Validity

/-!
# Proofs: the intrinsic gas and the rules of a transaction

The intrinsic gas is at least 12000 at every fork, and 21000 before Glamsterdam.

Before Glamsterdam, it does not depend on the sender.

The price of call data and of an access list adds up over concatenation, so it only grows.

A transaction that passes the rules has a gas limit that covers its least gas limit.

Its nonce is below `2^64 - 1`, and from Fusaka to BPO5 its gas limit is at most `2^24`.

From Shapella the init code of a creation has at most the size that the fork allows.

From Glamsterdam its gas limit is at most `2^32 - 1`, and its least gas limit at most `2^24`.

A transaction passes the rules exactly when it meets these bounds and its fees are not inverted.

Its fees are inverted when its priority fee per gas is above its maximum fee per gas.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.Evm.GasCosts

/-! ## The intrinsic gas -/

/-- The intrinsic gas is the sum of its six terms. -/
theorem intrinsicGas_eq (fork : Fork) (sender : Address) (tx : Transaction) :
    intrinsicGas fork sender tx = baseCost fork sender tx + dataCost fork tx.data +
      (if tx.to.isNone then createCost fork tx.data.size else 0) +
      accessListCost fork tx.accesses + accessListDataCost fork tx.accesses +
      authorizationCost fork * tx.authorizations.length :=
  rfl

/-- Before Glamsterdam, the base is 21000 whoever the sender is. -/
theorem baseCost_of_lt_glamsterdam {fork : Fork} (h : fork < .glamsterdam) (sender : Address)
    (tx : Transaction) : baseCost fork sender tx = TX_BASE := by
  have hn : ¬ fork ≥ Fork.glamsterdam := Nat.not_le.mpr h
  simp [baseCost, hn]

/-- Before Glamsterdam, the intrinsic gas does not depend on the sender. -/
theorem intrinsicGas_sender_of_lt_glamsterdam {fork : Fork} (h : fork < .glamsterdam)
    (sender sender' : Address) (tx : Transaction) :
    intrinsicGas fork sender tx = intrinsicGas fork sender' tx := by
  simp only [intrinsicGas_eq, baseCost_of_lt_glamsterdam h]

/-- Before Glamsterdam, the least gas limit does not depend on the sender. -/
theorem minimumGas_sender_of_lt_glamsterdam {fork : Fork} (h : fork < .glamsterdam)
    (sender sender' : Address) (tx : Transaction) :
    minimumGas fork sender tx = minimumGas fork sender' tx := by
  simp only [minimumGas, calldataFloor, intrinsicGas_eq, baseCost_of_lt_glamsterdam h]

/-- The base is at least 12000, the price of the sender, at every fork. -/
theorem TX_BASE_COST_le_baseCost (fork : Fork) (sender : Address) (tx : Transaction) :
    TX_BASE_COST ≤ baseCost fork sender tx := by
  unfold baseCost
  split
  · omega
  · simp [TX_BASE_COST, TX_BASE]

/-- The intrinsic gas is at least 12000, the price of the sender, at every fork. -/
theorem TX_BASE_COST_le_intrinsicGas (fork : Fork) (sender : Address) (tx : Transaction) :
    TX_BASE_COST ≤ intrinsicGas fork sender tx := by
  have := TX_BASE_COST_le_baseCost fork sender tx
  rw [intrinsicGas_eq]
  omega

/-- Before Glamsterdam, the intrinsic gas is at least 21000. -/
theorem TX_BASE_le_intrinsicGas {fork : Fork} (h : fork < .glamsterdam) (sender : Address)
    (tx : Transaction) : TX_BASE ≤ intrinsicGas fork sender tx := by
  rw [intrinsicGas_eq, baseCost_of_lt_glamsterdam h]
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
theorem accessListCost_append (fork : Fork) (a b : List Access) :
    accessListCost fork (a ++ b) = accessListCost fork a + accessListCost fork b := by
  simp [accessListCost, List.map_append, List.sum_append]

/-- A longer access list never costs less. -/
theorem accessListCost_le_append (fork : Fork) (a b : List Access) :
    accessListCost fork a ≤ accessListCost fork (a ++ b) := by
  rw [accessListCost_append]
  omega

/-- The least gas limit covers the intrinsic gas. -/
theorem intrinsicGas_le_minimumGas (fork : Fork) (sender : Address) (tx : Transaction) :
    intrinsicGas fork sender tx ≤ minimumGas fork sender tx := by
  unfold minimumGas
  split <;> omega

/-- From Pectra, the least gas limit covers the call data floor. -/
theorem calldataFloor_le_minimumGas {fork : Fork} (hFork : fork ≥ .pectra) (sender : Address)
    (tx : Transaction) : calldataFloor fork sender tx ≤ minimumGas fork sender tx := by
  simp only [minimumGas, hFork, ↓reduceIte]
  omega

/-! ## A valid transaction -/

/-- A transaction passes the gas, nonce and fee rules exactly when it satisfies each of them.

It then returns its intrinsic gas.

Its gas limit covers the least gas limit of the fork, and its nonce is below `2^64 - 1`.

From Shapella its init code has at most the size that the fork allows.

From Fusaka to BPO5 its gas limit is at most `2^24`.

From Glamsterdam its gas limit is at most `2^32 - 1`, and its least gas limit at most `2^24`.

Its priority fee per gas is at most its maximum fee per gas. -/
theorem validateTransaction_eq_ok_iff {fork : Fork} {sender : Address} {tx : Transaction}
    {gas : Nat} :
    validateTransaction fork sender tx = .ok gas ↔
      gas = intrinsicGas fork sender tx ∧ minimumGas fork sender tx ≤ tx.gas.toNat ∧
        tx.nonce.toNat < 2 ^ 64 - 1 ∧
        (fork ≥ .shapella → tx.to = none → tx.data.size ≤ maxInitCodeSize fork) ∧
        (fork ≥ .fusaka → fork < .glamsterdam → tx.gas.toNat ≤ TX_MAX_GAS_LIMIT) ∧
        (fork ≥ .glamsterdam →
          tx.gas.toNat ≤ TX_MAX_TOTAL_GAS_LIMIT ∧ minimumGas fork sender tx ≤ TX_MAX_GAS_LIMIT) ∧
        validateTransaction.feesInverted tx = false := by
  unfold validateTransaction
  constructor
  · intro h
    split at h
    · cases h
    rename_i hGas
    split at h
    · cases h
    rename_i hInit
    split at h
    · cases h
    rename_i hTotal
    split at h
    · cases h
    rename_i hIntrinsic
    split at h
    · cases h
    rename_i hCap
    split at h
    · cases h
    rename_i hNonce
    split at h
    · cases h
    rename_i hFees
    cases h
    refine ⟨rfl, by omega, by omega, ?_, ?_, ?_, by simpa using hFees⟩
    · intro hShapella hTo
      simp only [hTo, Option.isNone_none, true_and] at hInit
      exact Nat.not_lt.mp fun hlt => hInit ⟨hShapella, hlt⟩
    · intro hFusaka hBefore
      exact Nat.not_lt.mp fun hlt => hCap ⟨hFusaka, hBefore, hlt⟩
    · intro hAfter
      exact ⟨Nat.not_lt.mp fun hlt => hTotal ⟨hAfter, hlt⟩,
        Nat.not_lt.mp fun hlt => hIntrinsic ⟨hAfter, hlt⟩⟩
  · rintro ⟨rfl, hMin, hNonce, hInit, hCap, hAfter, hFees⟩
    split
    · omega
    split
    · rename_i hbad
      obtain ⟨hShapella, hTo, hlt⟩ := hbad
      have := hInit hShapella (Option.isNone_iff_eq_none.mp hTo)
      omega
    split
    · rename_i hbad
      have := (hAfter hbad.1).1
      omega
    split
    · rename_i hbad
      have := (hAfter hbad.1).2
      omega
    split
    · rename_i hbad
      have := hCap hbad.1 hbad.2.1
      omega
    split
    · omega
    split
    · simp_all
    rfl

/-- What a transaction that passes the gas, nonce and fee rules satisfies.

It returns its intrinsic gas, and its gas limit covers the least gas limit of the fork.

Its nonce is below `2^64 - 1`.

From Shapella its init code has at most the size that the fork allows.

From Fusaka to BPO5 its gas limit is at most `2^24`.

From Glamsterdam its gas limit is at most `2^32 - 1`, and its least gas limit at most `2^24`. -/
theorem validateTransaction_ok {fork : Fork} {sender : Address} {tx : Transaction} {gas : Nat}
    (h : validateTransaction fork sender tx = .ok gas) :
    gas = intrinsicGas fork sender tx ∧ minimumGas fork sender tx ≤ tx.gas.toNat ∧
      tx.nonce.toNat < 2 ^ 64 - 1 ∧
      (fork ≥ .shapella → tx.to = none → tx.data.size ≤ maxInitCodeSize fork) ∧
      (fork ≥ .fusaka → fork < .glamsterdam → tx.gas.toNat ≤ TX_MAX_GAS_LIMIT) ∧
      (fork ≥ .glamsterdam →
        tx.gas.toNat ≤ TX_MAX_TOTAL_GAS_LIMIT ∧ minimumGas fork sender tx ≤ TX_MAX_GAS_LIMIT) := by
  obtain ⟨hGas, hMin, hNonce, hInit, hCap, hAfter, -⟩ := validateTransaction_eq_ok_iff.mp h
  exact ⟨hGas, hMin, hNonce, hInit, hCap, hAfter⟩

/-- A valid transaction has a gas limit of at least 12000, the price of its sender. -/
theorem validateTransaction_gas_ge {fork : Fork} {sender : Address} {tx : Transaction} {gas : Nat}
    (h : validateTransaction fork sender tx = .ok gas) : TX_BASE_COST ≤ tx.gas.toNat := by
  obtain ⟨-, hMin, -⟩ := validateTransaction_ok h
  have := TX_BASE_COST_le_intrinsicGas fork sender tx
  have := intrinsicGas_le_minimumGas fork sender tx
  omega

/-- What a transaction that passes every rule alone satisfies.

It signs no chain or the chain of the network, and its signature names the sender.

Its gas and nonce pass the rules for that sender.

Its blobs and authorizations pass the rules. -/
theorem checkTransaction_ok {fork : Fork} {chainId : UInt64} {tx : Transaction}
    {sender : Address} {gas : Nat} (h : checkTransaction fork chainId tx = .ok (sender, gas)) :
    checkChainId fork chainId tx = .ok () ∧ recoverSender fork tx = .ok sender ∧
      validateTransaction fork sender tx = .ok gas ∧ checkContents fork tx = .ok () := by
  unfold checkTransaction at h
  cases hc : checkChainId fork chainId tx with
  | error e => simp [hc, bind, Except.bind] at h
  | ok u =>
    cases hs : recoverSender fork tx with
    | error e => simp [hc, hs, bind, Except.bind] at h
    | ok a =>
      cases hv : validateTransaction fork a tx with
      | error e => simp [hc, hs, hv, bind, Except.bind] at h
      | ok g =>
        cases hk : checkContents fork tx with
        | error e => simp [hc, hs, hv, hk, bind, Except.bind] at h
        | ok w =>
          simp only [hc, hs, hv, hk, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, rfl, hv, rfl⟩

end EthLib.Execution.Transactions
