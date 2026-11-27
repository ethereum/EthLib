module

public import EthLib.Execution.Blocks.Roots
public import EthLib.Base.Proofs.ExceptT

/-!
# Proofs: the roots of typed lists

A list of transactions, withdrawals or receipts has a root exactly when two steps succeed.

Each item has bytes, and the list of those bytes has that root.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Transactions
open EthLib.Execution.Trie
open EthLib.Serialization.Rlp

/-- A typed list has a root exactly when each item has bytes and their list has that root. -/
theorem bind_indexedRoot_eq_ok_iff {γ : Type} {encodeItem : γ → Except RlpError ByteArray}
    {items : List γ} {root' : Hash32} :
    ((items.mapM encodeItem).mapError TrieError.rlp >>= indexedRoot) = .ok root' ↔
      ∃ values, items.mapM encodeItem = .ok values ∧ indexedRoot values = .ok root' := by
  cases items.mapM encodeItem <;> simp [Except.mapError, bind, Except.bind]

/-- A list of transactions has a root exactly when the list of their bytes has that root. -/
theorem transactionsRoot_eq_ok_iff {transactions : List Transaction} {root' : Hash32} :
    transactionsRoot transactions = .ok root' ↔
      ∃ values, transactions.mapM encodeTransaction = .ok values ∧
        indexedRoot values = .ok root' :=
  bind_indexedRoot_eq_ok_iff

/-- The withdrawals root, with a plain hash. -/
theorem withdrawalsRootM_eq (hash : ByteArray → Hash32) (withdrawals : List Withdrawal) :
    (withdrawalsRootM (m := Id) hash withdrawals).run =
      (withdrawals.mapM Codec.encode).mapError TrieError.rlp >>= fun values =>
        (indexedRootM (m := Id) hash values).run := by
  simp only [withdrawalsRootM, ExceptT.run, exceptT_id_bind, exceptT_id_monadLift, except_bind_eq]

/-- A list of withdrawals has a root with a plain hash exactly when their encodings have it. -/
theorem withdrawalsRootM_eq_ok_iff (hash : ByteArray → Hash32) {withdrawals : List Withdrawal}
    {root' : Hash32} :
    (withdrawalsRootM (m := Id) hash withdrawals).run = .ok root' ↔
      ∃ values, withdrawals.mapM Codec.encode = .ok values ∧
        (indexedRootM (m := Id) hash values).run = .ok root' := by
  rw [withdrawalsRootM_eq]
  cases withdrawals.mapM Codec.encode <;> simp [Except.mapError, bind, Except.bind]

/-- A list of withdrawals has a root exactly when the list of their encodings has that root. -/
theorem withdrawalsRoot_eq_ok_iff {withdrawals : List Withdrawal} {root' : Hash32} :
    withdrawalsRoot withdrawals = .ok root' ↔
      ∃ values, withdrawals.mapM Codec.encode = .ok values ∧ indexedRoot values = .ok root' :=
  withdrawalsRootM_eq_ok_iff Cryptography.Hash.Keccak.keccak256

/-- A list of receipts has a root exactly when the list of their bytes has that root. -/
theorem receiptsRoot_eq_ok_iff {fork : Fork} {receipts : List (UInt8 × Receipt fork)}
    {root' : Hash32} :
    receiptsRoot receipts = .ok root' ↔
      ∃ values, receipts.mapM (fun (type, r) => encodeReceipt (fork := fork) type r) = .ok values ∧
        indexedRoot values = .ok root' :=
  bind_indexedRoot_eq_ok_iff

end EthLib.Execution.Blocks
