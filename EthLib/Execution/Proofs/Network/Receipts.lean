module

public import EthLib.Execution.Network.Receipts
public import EthLib.Execution.Proofs.Blocks.Receipt

/-!
# Proofs: the receipts of the eth protocol

A receipt reads back from its RLP item.

Leaving out the Bloom filter and computing it again can give a receipt back.

It does so exactly when its filter is the filter of its logs.

From eth/69 on, the reader of a receipt gives its consensus form.

On eth/68, a list reads as a legacy receipt, and a byte string as a receipt of another type.

The receipts of a block match a root exactly when their consensus forms, in order, have that root.

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

/-- A receipt in consensus form can come back through eth/69.

It does so exactly when its Bloom filter is the filter of its logs. -/
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

/-- From eth/69 on, an item reads in consensus form exactly when it holds a receipt of eth/69.

The consensus form is the type, and the receipt with the Bloom filter of its logs. -/
theorem consensusOfItem_eq_ok_iff {version : EthVersion} (hv : version ≠ .eth68) {item : Item}
    {c : UInt8 × Receipt fork} :
    consensusOfItem version fork item = .ok c ↔
      ∃ w : WireReceipt fork, Codec.ofItem item = .ok w ∧ c = w.toConsensus := by
  cases hd : (Codec.ofItem item : Except RlpError (WireReceipt fork)) <;>
    simp [consensusOfItem, hv, hd, Functor.map, Except.map, Except.mapError, eq_comm]

/-- Bytes that hold a receipt of type 0 are exactly those whose first byte is at least `0xc0`. -/
private theorem eq_zero_iff_of_decodeReceipt {bytes : ByteArray} {type : UInt8}
    {r : Receipt fork} (h : decodeReceipt fork bytes = .ok (type, r)) :
    ∃ h0 : 0 < bytes.size, (type = 0 ↔ (0xc0 : UInt8) ≤ bytes[0]) := by
  unfold decodeReceipt at h
  split at h
  · rename_i h0
    refine ⟨h0, ?_⟩
    dsimp only at h
    split at h
    · rename_i hHigh
      cases hd : (Codec.decode bytes : Except RlpError (Receipt fork)) with
      | error e => simp [hd, Functor.map, Except.map, Except.mapError] at h
      | ok r' =>
        simp only [hd, Functor.map, Except.map, Except.mapError, Except.ok.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [hHigh]
    · rename_i hLow
      split at h
      · rename_i since hSince
        split at h
        · cases hd : (Codec.decode (bytes.extract 1 bytes.size) : Except RlpError (Receipt fork))
            with
          | error e => simp [hd, Functor.map, Except.map, Except.mapError] at h
          | ok r' =>
            simp only [hd, Functor.map, Except.map, Except.mapError, Except.ok.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [hLow, ne_zero_of_typeFork hSince]
        · cases h
      · cases h
  · cases h

/-- The first byte of a nonempty byte string is the head of its list of bytes. -/
private theorem head?_toList {bytes : ByteArray} (h0 : 0 < bytes.size) :
    bytes.data.toList.head? = some bytes[0] := by
  rcases bytes with ⟨⟨l⟩⟩
  cases l with
  | nil => exact absurd h0 (Nat.lt_irrefl 0)
  | cons x xs => rfl

/-- On eth/68, an item reads as a receipt in consensus form in exactly one of two ways.

A list reads as the receipt of a legacy transaction, whose type is 0.

A byte string reads as the bytes of a receipt whose type is not 0.

So a legacy receipt sent as a byte string does not read. -/
theorem consensusOfItem_eth68_eq_ok_iff {item : Item} {type : UInt8} {r : Receipt fork} :
    consensusOfItem .eth68 fork item = .ok (type, r) ↔
      (∃ items, item = .list items ∧ type = 0 ∧ Codec.ofItem item = .ok r) ∨
        ∃ bytes, item = .bytes bytes ∧ type ≠ 0 ∧ decodeReceipt fork bytes = .ok (type, r) := by
  cases item with
  | list items =>
    cases hd : (Codec.ofItem (.list items) : Except RlpError (Receipt fork)) <;>
      simp [consensusOfItem, hd, Functor.map, Except.map, Except.mapError, eq_comm, and_comm]
  | bytes b =>
    simp only [consensusOfItem, ↓reduceIte, reduceCtorEq, false_and, exists_false, false_or,
      Item.bytes.injEq, exists_eq_left']
    constructor
    · intro h
      split at h
      · rename_i hLow
        obtain ⟨h0, hiff⟩ := eq_zero_iff_of_decodeReceipt h
        rw [head?_toList h0] at hLow
        simp only [Option.all_some, decide_eq_true_eq] at hLow
        exact ⟨fun hz => absurd (hiff.mp hz) (UInt8.not_le.mpr hLow), h⟩
      · cases h
    · rintro ⟨hne, h⟩
      obtain ⟨h0, hiff⟩ := eq_zero_iff_of_decodeReceipt h
      have hLow : b.data.toList.head?.all (· < 0xc0) = true := by
        rw [head?_toList h0]
        simpa using UInt8.not_le.mp (mt hiff.mpr hne)
      simp only [hLow, ↓reduceIte, h]

/-- The receipts of a block match a receipts root exactly when two conditions hold.

Each receipt reads as a receipt in consensus form, the one at its own position.

The receipts root of those consensus forms, in the order of the list, is that root. -/
theorem receiptsMatch_eq_true_iff {version : EthVersion} {root : Hash32} {receipts : List Item} :
    receiptsMatch version fork root receipts = true ↔
      ∃ cs : List (UInt8 × Receipt fork), cs.length = receipts.length ∧
        (∀ (k : Nat) (hc : k < cs.length) (hr : k < receipts.length),
          consensusOfItem version fork receipts[k] = .ok cs[k]) ∧
          receiptsRoot cs = .ok root := by
  unfold receiptsMatch
  constructor
  · intro h
    split at h
    · rename_i cs hcs
      split at h
      · rename_i root' hroot
        obtain ⟨hlen, hget⟩ := mapM_eq_ok_iff.mp hcs
        exact ⟨cs, hlen, fun k _ hr => hget k hr, by simpa using hroot.trans (by simpa using h)⟩
      · cases h
    · cases h
  · rintro ⟨cs, hlen, hget, hroot⟩
    have hcs : receipts.mapM (consensusOfItem version fork) = .ok cs :=
      mapM_eq_ok_iff.mpr ⟨hlen, fun k hk => hget k (by omega) hk⟩
    simp [hcs, hroot]

/-- A partial list that passes the checks of EIP-7975 has no more receipts than transactions.

Each receipt is within its bound, and the total is within the bound of the block. -/
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
