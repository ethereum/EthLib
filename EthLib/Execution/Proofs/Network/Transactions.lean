module

public import EthLib.Execution.Network.Transactions
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the transaction exchange

An announcement reads back from its RLP item on the versions that use its form.

It reads from no other item.

Take an answer that passes the check.

Its transactions have hashes that are requested hashes, in the order of the request.

An answer passes exactly when its transactions hash to a sublist of the requested hashes, in order.
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
    (c : Option (Vector UInt8 16)) :
    ofItem .eth72 (eth72 t s h c).toItem = .ok (eth72 t s h c) := by
  have : ¬ EthVersion.eth72 < .eth72 := by decide
  simp [ofItem, toItem, this, Item.fields, Item.toItems, Item.field_toItem, bind, Except.bind,
    pure, Except.pure]

/-- eth/68 to eth/71 reject the announcement of eth/72, which has four fields. -/
theorem ofItem_eth68_of_eth72 {version : EthVersion} (hv : version < .eth72) (t : ByteArray)
    (s : List Nat) (h : List Hash32) (c : Option (Vector UInt8 16)) :
    ofItem version (eth72 t s h c).toItem = .error (.wrongFieldCount 3 4) := by
  simp [ofItem, toItem, hv, Item.fields, Item.toItems, bind, Except.bind]

/-- An announcement reads exactly from its own RLP item, on a version that uses its form.

eth/68 to eth/71 read only the three fields of the older form, and eth/72 only the four of its own.

This reader does not check the lengths of the lists.

The decoder of messages does. -/
theorem ofItem_eq_ok_iff {version : EthVersion} {item : Item} {a : Announcement} :
    ofItem version item = .ok a ↔
      item = a.toItem ∧ match a with
        | .eth68 .. => version < .eth72
        | .eth72 .. => version = .eth72 := by
  constructor
  · intro h
    unfold ofItem at h
    split at h
    · rename_i hv
      obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp h
      rcases items with _ | ⟨t, _ | ⟨s, _ | ⟨h, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hlen
      obtain ⟨x₁, rfl, h₁⟩ := Item.field_bind_eq_ok.mp hrest
      obtain ⟨x₂, rfl, h₂⟩ := Item.field_bind_eq_ok.mp h₁
      obtain ⟨x₃, rfl, h₃⟩ := Item.field_bind_eq_ok.mp h₂
      cases h₃
      exact ⟨rfl, hv⟩
    · rename_i hv
      obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp h
      rcases items with _ | ⟨t, _ | ⟨s, _ | ⟨h, _ | ⟨c, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hlen
      obtain ⟨x₁, rfl, h₁⟩ := Item.field_bind_eq_ok.mp hrest
      obtain ⟨x₂, rfl, h₂⟩ := Item.field_bind_eq_ok.mp h₁
      obtain ⟨x₃, rfl, h₃⟩ := Item.field_bind_eq_ok.mp h₂
      obtain ⟨x₄, rfl, h₄⟩ := Item.field_bind_eq_ok.mp h₃
      cases h₄
      refine ⟨rfl, ?_⟩
      cases version <;> first | rfl | exact absurd (by decide) hv
  · rintro ⟨rfl, hv⟩
    cases a with
    | eth68 t s h => exact ofItem_eth68 hv t s h
    | eth72 t s h c =>
      subst hv
      exact ofItem_eth72 t s h c

end Announcement

/-- Take an answer that passes the check.

The hashes of its transactions are requested hashes, in the order of the request. -/
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

/-- An answer passes the check of a request exactly when its transactions hash to requested hashes.

Every transaction must hash, and the hashes form a sublist of the requested hashes, in order.

The conditions do not ask for every requested hash, since a peer may leave some out.

They read only the hash of each transaction, not whether it is valid. -/
theorem checkPooled_eq_ok_iff {requested : List Hash32} {txs : List Item} :
    checkPooled requested txs = .ok () ↔
      ∃ hashes, txs.mapM wireHash = .ok hashes ∧ hashes.Sublist requested := by
  refine ⟨sublist_of_checkPooled, fun ⟨hashes, hm, hs⟩ => ?_⟩
  simp [checkPooled, hm, List.isSublist_iff_sublist.mpr hs, Except.mapError, bind, Except.bind,
    pure, Except.pure]

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
