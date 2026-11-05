module

public import EthLib.Execution.Network.Transactions
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the transaction exchange

An announcement reads back from its RLP item on the versions that use its form.

The transactions of an answer that passes the check have hashes that are requested hashes, in
the order of the request.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

namespace Announcement

/-- The announcement of eth/68 reads back on eth/68 to eth/71. -/
theorem ofItem_eth68 {version : EthVersion} (hv : version < .eth72) (t : ByteArray)
    (s : List Nat) (h : List Hash32) : ofItem version (eth68 t s h).toItem = .ok (eth68 t s h) := by
  simp [ofItem, toItem, hv, Item.fields, Item.toItems, Item.field_toItem, bind, Except.bind,
    pure, Except.pure]

/-- The announcement of eth/72 reads back on eth/72. -/
theorem ofItem_eth72 (t : ByteArray) (s : List Nat) (h : List Hash32)
    (c : Option (Vector UInt8 16)) : ofItem .eth72 (eth72 t s h c).toItem = .ok (eth72 t s h c) := by
  have : ¬ EthVersion.eth72 < .eth72 := by decide
  simp [ofItem, toItem, this, Item.fields, Item.toItems, Item.field_toItem, bind, Except.bind,
    pure, Except.pure]

/-- eth/68 to eth/71 reject the announcement of eth/72, which has four fields. -/
theorem ofItem_eth68_of_eth72 {version : EthVersion} (hv : version < .eth72) (t : ByteArray)
    (s : List Nat) (h : List Hash32) (c : Option (Vector UInt8 16)) :
    ofItem version (eth72 t s h c).toItem = .error (.wrongFieldCount 3 4) := by
  simp [ofItem, toItem, hv, Item.fields, Item.toItems, bind, Except.bind]

end Announcement

/-- In an answer that passes the check, the hashes of the transactions are requested hashes, in
the order of the request. -/
theorem sublist_of_checkPooled {requested : List Hash32} {txs : List Item}
    (h : checkPooled requested txs = .ok ()) :
    ∃ hashes, txs.mapM wireHash = .ok hashes ∧ hashes.Sublist requested := by
  unfold checkPooled at h
  cases hm : txs.mapM wireHash with
  | error e => simp [hm, Except.mapError, bind, Except.bind] at h
  | ok hashes =>
    refine ⟨hashes, rfl, ?_⟩
    simp only [hm, Except.mapError, bind, Except.bind] at h
    by_cases hs : hashes.isSublist requested
    · exact List.isSublist_iff_sublist.mp hs
    · simp [hs, throw, throwThe, MonadExceptOf.throw] at h

/-- The empty answer passes the check of every request. -/
theorem checkPooled_nil (requested : List Hash32) : checkPooled requested [] = .ok () := by
  simp [checkPooled, List.mapM, List.mapM.loop, Except.mapError, bind, Except.bind, pure,
    Except.pure, List.isSublist]

/-- Two errors with one code come from one constructor. -/
theorem PoolError.code_injective (e₁ e₂ : PoolError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [PoolError.code] at h; exact absurd h (by decide))

end EthLib.Execution.Network
