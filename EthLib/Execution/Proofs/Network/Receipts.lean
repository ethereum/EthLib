module

public import EthLib.Execution.Network.Receipts
public import EthLib.Execution.Proofs.Blocks.Receipt

/-!
# Proofs: the receipts of eth/69

A receipt reads back from its RLP item.

Leaving out the Bloom filter and computing it again gives a receipt back exactly when its filter
is the filter of its logs.

From eth/69 on, the reader of a receipt gives its consensus form.

From eth/70, a partial list of receipts passes the EIP-7975 checks exactly when three bounds hold.

Before eth/70, a peer sends every receipt of a block, and these checks do not apply.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Blocks

variable {fork : Fork}

instance : LawfulCodec (WireReceipt fork) where
  ofItem_toItem r := by
    show WireReceipt.ofItem (WireReceipt.toItem r) = _
    simp only [WireReceipt.ofItem, WireReceipt.toItem, Item.fields, Item.toItems,
      List.length_cons, List.length_nil, ↓reduceIte, Item.field_toItem, bind, Except.bind, pure,
      Except.pure]
  toItem_of_ofItem {item r} h := by
    change WireReceipt.ofItem item = .ok r at h
    unfold WireReceipt.ofItem at h
    obtain ⟨items, rfl, hlen, hrest⟩ := Item.fields_bind_eq_ok.mp h
    rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hlen
    obtain ⟨w, rfl, h1⟩ := Item.field_bind_eq_ok.mp hrest
    obtain ⟨x, rfl, h2⟩ := Item.field_bind_eq_ok.mp h1
    obtain ⟨y, rfl, h3⟩ := Item.field_bind_eq_ok.mp h2
    obtain ⟨z, rfl, h4⟩ := Item.field_bind_eq_ok.mp h3
    cases h4
    rfl

namespace WireReceipt

/-- A receipt of eth/69 comes back from its consensus form. -/
theorem ofConsensus_toConsensus (r : WireReceipt fork) : ofConsensus r.toConsensus = r := by
  cases r
  rfl

/-- A receipt in consensus form comes back through eth/69 exactly when its Bloom filter is the
filter of its logs. -/
theorem toConsensus_ofConsensus (t : UInt8) (r : Receipt fork) :
    (ofConsensus (t, r)).toConsensus = (t, r) ↔ r.bloom = logsBloom r.logs := by
  cases r
  simp [ofConsensus, toConsensus, makeReceipt, eq_comm]

end WireReceipt

/-- From eth/69 on, a receipt reads as its consensus form, with the filter of its logs. -/
theorem consensusOfItem_toItem {version : EthVersion} (hv : version ≠ .eth68)
    (r : WireReceipt fork) :
    consensusOfItem version fork (Codec.toItem r) = .ok r.toConsensus := by
  simp [consensusOfItem, hv, LawfulCodec.ofItem_toItem, Functor.map, Except.map,
    Except.mapError]

/-- A partial list that passes the checks of EIP-7975 has no more receipts than transactions, each
receipt within its bound, and a total within the bound of the block. -/
theorem of_checkPartialReceipts {gasLimits : List Nat} {blockGasLimit : Nat} {sizes : List Nat}
    (h : checkPartialReceipts gasLimits blockGasLimit sizes = .ok ()) :
    sizes.length ≤ gasLimits.length ∧
      (∀ (i : Nat) (hs : i < sizes.length) (hg : i < gasLimits.length),
        sizes[i] ≤ gasLimits[i] / 8) ∧
      sizes.sum ≤ blockGasLimit / 8 := by
  unfold checkPartialReceipts at h
  by_cases hl : gasLimits.length < sizes.length
  · simp [hl, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [hl, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
  cases hf : ((List.range sizes.length).zip (sizes.zip gasLimits)).find?
      (fun (_, size, gas) => gas / 8 < size) with
  | some x =>
    obtain ⟨i, size, gas⟩ := x
    simp [hf, throw, throwThe, MonadExceptOf.throw] at h
  | none =>
    simp only [hf] at h
    refine ⟨by omega, fun i hs hg => ?_, ?_⟩
    · have hmem : (i, sizes[i], gasLimits[i])
          ∈ (List.range sizes.length).zip (sizes.zip gasLimits) :=
        List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
      have := List.find?_eq_none.mp hf _ hmem
      simp at this
      omega
    · by_cases ht : blockGasLimit / 8 < sizes.sum
      · simp [ht, throw, throwThe, MonadExceptOf.throw] at h
      · omega

/-- From eth/70, a partial list passes the checks of EIP-7975 exactly when three bounds hold.

There are no more receipts than transactions.

Each receipt is within the bound of its transaction, its gas limit over 8.

All the receipts together are within the bound of the block.

The conditions read only the sizes of the receipts.

They do not check the receipts against the receipts root, nor that the list is complete. -/
theorem checkPartialReceipts_eq_ok_iff {gasLimits : List Nat} {blockGasLimit : Nat}
    {sizes : List Nat} :
    checkPartialReceipts gasLimits blockGasLimit sizes = .ok () ↔
      sizes.length ≤ gasLimits.length ∧
        (∀ (i : Nat) (hs : i < sizes.length) (hg : i < gasLimits.length),
          sizes[i] ≤ gasLimits[i] / 8) ∧
        sizes.sum ≤ blockGasLimit / 8 := by
  refine ⟨of_checkPartialReceipts, fun ⟨hl, hall, ht⟩ => ?_⟩
  unfold checkPartialReceipts
  -- No indexed receipt is above the bound of its transaction.
  have hf : ((List.range sizes.length).zip (sizes.zip gasLimits)).find?
      (fun (_, size, gas) => gas / 8 < size) = none := by
    apply List.find?_eq_none.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_zip, List.length_range, Nat.lt_min] at hi
    simp only [List.getElem_zip, List.getElem_range, decide_eq_true_eq, Nat.not_lt]
    exact hall i hi.1 hi.2.2
  simp [Nat.not_lt.mpr hl, hf, Nat.not_lt.mpr ht, pure, Except.pure]

/-- Two errors with one code come from one constructor. -/
theorem PartialReceiptsError.code_injective (e₁ e₂ : PartialReceiptsError)
    (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [PartialReceiptsError.code] at h; exact absurd h (by decide))

end EthLib.Execution.Network
