module

public import EthLib.Execution.State.Account
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the RLP form of an account

Each field of an account has a lawful codec, so the form of the account is lawful too.

So decoding accepts a byte string exactly when it encodes an account with a storage root.
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base
open EthLib.Serialization.Rlp

/-- Reading the item of an account gives the account and its storage root. -/
theorem Account.ofItem_toItem (account : Account) (storageRoot : Hash32) :
    Account.ofItem (account.toItem storageRoot) = .ok (account, storageRoot) := by
  simp [Account.ofItem, Account.toItem, Item.fields, Item.toItems, LawfulCodec.ofItem_toItem, bind,
    Except.bind, pure, Except.pure]

/-- An item that holds an account and a storage root is the item of the two. -/
theorem Account.toItem_of_ofItem {item : Item} {account : Account} {storageRoot : Hash32}
    (h : Account.ofItem item = .ok (account, storageRoot)) : account.toItem storageRoot = item := by
  unfold Account.ofItem at h
  cases hFields : item.fields 4 with
  | error e => simp [hFields, bind, Except.bind] at h
  | ok items =>
    obtain ⟨rfl, hLength⟩ := Item.fields_eq_ok.mp hFields
    simp only [hFields, bind, Except.bind] at h
    -- The four items each hold the value of their field.
    match items, hLength with
    | [nonce, balance, root, codeHash], _ =>
      simp only at h
      cases hn : (Codec.ofItem nonce : Except RlpError Nat) <;>
        cases hb : (Codec.ofItem balance : Except RlpError U256) <;>
        cases hc : (Codec.ofItem codeHash : Except RlpError Hash32) <;>
        cases hr : (Codec.ofItem root : Except RlpError Hash32) <;>
        simp only [hn, hb, hc, hr, pure, Except.pure, reduceCtorEq, Except.ok.injEq,
          Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [Account.toItem, LawfulCodec.toItem_of_ofItem hn, LawfulCodec.toItem_of_ofItem hb,
        LawfulCodec.toItem_of_ofItem hc, LawfulCodec.toItem_of_ofItem hr]

/-- Decoding the encoding of an account gives the account and its storage root. -/
theorem decodeAccount_encodeAccount {account : Account} {storageRoot : Hash32} {b : ByteArray}
    (h : encodeAccount account storageRoot = .ok b) :
    decodeAccount b = .ok (account, storageRoot) := by
  simp [decodeAccount, decode_encode _ _ h, Account.ofItem_toItem, bind, Except.bind]

/-- A byte string that decodes to an account and a storage root is the encoding of the two. -/
theorem encodeAccount_of_decodeAccount {b : ByteArray} {account : Account} {storageRoot : Hash32}
    (h : decodeAccount b = .ok (account, storageRoot)) :
    encodeAccount account storageRoot = .ok b := by
  unfold decodeAccount at h
  cases hItem : decode b with
  | error e => simp [hItem, bind, Except.bind] at h
  | ok item =>
    simp only [hItem, bind, Except.bind] at h
    rw [encodeAccount, Account.toItem_of_ofItem h]
    exact encode_decode b item hItem

/-- Decoding accepts exactly the encoding of each account with each storage root. -/
theorem decodeAccount_eq_ok_iff (b : ByteArray) (account : Account) (storageRoot : Hash32) :
    decodeAccount b = .ok (account, storageRoot) ↔ encodeAccount account storageRoot = .ok b :=
  ⟨encodeAccount_of_decodeAccount, decodeAccount_encodeAccount⟩

end EthLib.Execution.State
