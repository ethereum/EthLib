module

public import EthLib.Networking.Enr.Eth
public import EthLib.Networking.Proofs.Devp2p.ForkId

/-!
# Proofs: the "eth" entry of a node record

The fork identifier reads back from the value of the entry.

A reader ignores the elements after the first, and it reads exactly the values whose first
element is a fork identifier.
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Networking.Devp2p
open EthLib.Serialization.Rlp

/-- A value with the identifier first reads as that identifier, whatever elements follow. -/
theorem readEthEntry_cons (id : ForkId) (rest : List Item) :
    readEthEntry (.list (Codec.toItem id :: rest)) = .ok id := by
  simp [readEthEntry, Item.toItems, Item.field_toItem, bind, Except.bind]

/-- The fork identifier reads back from the value of the entry. -/
theorem readEthEntry_ethEntry (id : ForkId) : readEthEntry (ethEntry id) = .ok id :=
  readEthEntry_cons id []

/-- A value reads as an identifier only when it is a list whose first element is that
identifier. -/
theorem eq_of_readEthEntry {item : Item} {id : ForkId} (h : readEthEntry item = .ok id) :
    ∃ rest, item = .list (Codec.toItem id :: rest) := by
  unfold readEthEntry at h
  cases item with
  | bytes _ => simp [Item.toItems, bind, Except.bind] at h
  | list items =>
    cases items with
    | nil => simp [Item.toItems, bind, Except.bind] at h
    | cons first rest =>
      simp only [Item.toItems, bind, Except.bind] at h
      exact ⟨rest, by rw [LawfulCodec.toItem_of_ofItem (Item.field_eq_ok.mp h)]⟩

/-- A record without the key has no fork identifier. -/
theorem readEth_of_find?_eq_none {r : Enr} (h : r.pairs.find? (·.1 = KEY_ETH) = none) :
    readEth r = .ok none := by
  simp [readEth, h, pure, Except.pure]

end EthLib.Networking.Enr
