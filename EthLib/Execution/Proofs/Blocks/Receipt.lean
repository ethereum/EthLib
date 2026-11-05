module

public import EthLib.Execution.Blocks.Receipt
public import EthLib.Execution.Proofs.Blocks.Bloom
public import EthLib.Execution.Proofs.Transactions.Envelope

/-!
# Proofs: logs and receipts

The RLP codecs of a log, of an outcome and of a receipt are lawful at every fork.

The bytes of a receipt decode back to its transaction type and the receipt.

They do so at each fork that has the type, and only the encoding decodes to them.

The receipts of a block count the gas cumulatively, so the counts never decrease.

Each receipt counts the gas of the transactions up to it.

So two receipts in a row differ by the gas of the second transaction.

The last count is the gas of all the transactions.

The Bloom filter of each receipt is the filter of its logs.

The filters of the receipts combine into the filter of all the logs of the block.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Transactions

instance : LawfulCodec Log where
  ofItem_toItem _ := Item.fields_bind_eq_ok.mpr
    ⟨_, rfl, rfl, by simp [Item.field_toItem, bind, Except.bind, pure, Except.pure]⟩
  toItem_of_ofItem h := by
    obtain ⟨items, rfl, hLen, h⟩ := Item.fields_bind_eq_ok.mp h
    match items, hLen, h with
    | [x0, x1, x2], _, h =>
      simp only [Item.field_bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨y0, rfl, y1, rfl, y2, rfl, rfl⟩ := h
      rfl

variable {fork : Fork}

instance : LawfulCodec (Outcome fork) where
  ofItem_toItem
    | .postState before root => by
      -- Before Byzantium, the decoder reads a state root.
      have h : ¬Fork.byzantium ≤ fork := Nat.not_le_of_lt before
      show Outcome.ofItem (Codec.toItem root) = _
      simp [Outcome.ofItem, h, LawfulCodec.ofItem_toItem, Functor.map, Except.map]
    | .status since succeeded => by
      show Outcome.ofItem (Codec.toItem succeeded) = _
      simp [Outcome.ofItem, since, LawfulCodec.ofItem_toItem, Functor.map, Except.map]
  toItem_of_ofItem {item o} h := by
    change Outcome.ofItem item = .ok o at h
    unfold Outcome.ofItem at h
    split at h
    · obtain ⟨b, hb, rfl⟩ := map_ok_iff.mp h
      exact LawfulCodec.toItem_of_ofItem (α := Bool) hb
    · obtain ⟨root, hRoot, rfl⟩ := map_ok_iff.mp h
      exact LawfulCodec.toItem_of_ofItem (α := Hash32) hRoot

instance : LawfulCodec (Receipt fork) where
  ofItem_toItem _ := Item.fields_bind_eq_ok.mpr
    ⟨_, rfl, rfl, by simp [Item.field_toItem, bind, Except.bind, pure, Except.pure]⟩
  toItem_of_ofItem h := by
    obtain ⟨items, rfl, hLen, h⟩ := Item.fields_bind_eq_ok.mp h
    match items, hLen, h with
    | [x0, x1, x2, x3], _, h =>
      simp only [Item.field_bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨y0, rfl, y1, rfl, y2, rfl, y3, rfl, rfl⟩ := h
      rfl

/-- A type that some fork adds is below `0xc0`, so it never starts a legacy receipt. -/
theorem not_le_of_typeFork {type : UInt8} {since : Fork} (h : typeFork type = some since) :
    ¬(0xc0 : UInt8) ≤ type := by
  unfold typeFork at h
  split at h
  · subst_vars; decide
  split at h
  · subst_vars; decide
  split at h
  · subst_vars; decide
  split at h
  · subst_vars; decide
  · cases h

/-- A type that some fork adds is not 0, the type of a legacy transaction. -/
theorem ne_zero_of_typeFork {type : UInt8} {since : Fork} (h : typeFork type = some since) :
    type ≠ 0 := by
  rintro rfl
  simp [typeFork] at h

/-- The decoder gives back the type and the receipt from their bytes.

It does so at each fork that has the type.

Type 0, a legacy transaction, exists at every fork. -/
theorem decodeReceipt_encodeReceipt {type : UInt8} {r : Receipt fork} {bytes : ByteArray}
    (h : encodeReceipt type r = .ok bytes)
    (hType : type = 0 ∨ ∃ since, typeFork type = some since ∧ since ≤ fork) :
    decodeReceipt fork bytes = .ok (type, r) := by
  unfold encodeReceipt at h
  split at h
  · rename_i hZero
    subst hZero
    obtain ⟨first, rest, hList, hFirst⟩ := encode_list_head _ _ h
    obtain ⟨h0, hEq⟩ := getElem_zero_of_toList hList
    simp [decodeReceipt, h0, hEq, hFirst, Codec.decode_encode h, Functor.map, Except.map,
      Except.mapError]
  · rename_i hNe
    obtain ⟨since, hSince, hFork⟩ := hType.resolve_left hNe
    cases hPayload : Codec.encode r with
    | error e => simp [hPayload, Functor.map, Except.map] at h
    | ok payload =>
      simp only [hPayload, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have h0 : 0 < (typedBytes type payload).size := by simp [size_typedBytes]
      simp [decodeReceipt, h0, typedBytes_getElem_zero, not_le_of_typeFork hSince, hSince, hFork,
        extract_typedBytes, Codec.decode_encode hPayload, Functor.map, Except.map,
        Except.mapError]

/-- Bytes that decode to a type and a receipt are the encoding of that receipt with that type.

So two different byte strings never decode to the same type and receipt. -/
theorem encodeReceipt_of_decodeReceipt {bytes : ByteArray} {type : UInt8} {r : Receipt fork}
    (h : decodeReceipt fork bytes = .ok (type, r)) : encodeReceipt type r = .ok bytes := by
  unfold decodeReceipt at h
  split at h
  · rename_i h0
    dsimp only at h
    split at h
    · cases hd : (Codec.decode bytes : Except RlpError (Receipt fork)) with
      | error e => simp [hd, Functor.map, Except.map, Except.mapError] at h
      | ok r' =>
        simp only [hd, Functor.map, Except.map, Except.mapError, Except.ok.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [encodeReceipt, Codec.encode_decode hd]
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
            simp [encodeReceipt, ne_zero_of_typeFork hSince, Codec.encode_decode hd,
              Functor.map, Except.map, typedBytes_getElem_extract bytes h0]
        · cases h
      · cases h
  · cases h

/-! ## Error codes -/

section

open EthLib.Execution.Blocks
open EthLib.Serialization.Rlp

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Execution.Blocks.ReceiptError.code_injective
    (e₁ e₂ : ReceiptError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [ReceiptError.code] at h; exact absurd h (by decide))

/-- A receipt error never has the code of an RLP error, so one Python class carries both. -/
theorem _root_.EthLib.Execution.Blocks.ReceiptError.code_ne_rlp
    (e : ReceiptError) (r : RlpError) : e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [ReceiptError.code, RlpError.code] <;> decide

end

/-! ## The receipts of a block -/

section Receipts

variable {fork : Fork}

/-- The Bloom filter of a receipt is the filter of its logs. -/
theorem bloom_makeReceipt (outcome : Outcome fork) (cumulativeGasUsed : Nat) (logs : List Log) :
    (makeReceipt outcome cumulativeGasUsed logs).bloom = logsBloom logs := rfl

/-- From Byzantium, the outcome of a transaction is whether it succeeded. -/
theorem Outcome.make_of_le {fork : Fork} (h : Fork.byzantium ≤ fork) (succeeded : Bool)
    (postStateRoot : Unit → Hash32) :
    Outcome.make fork succeeded postStateRoot = .status h succeeded := by
  simp [Outcome.make, h]

/-- Each transaction gives one receipt. -/
theorem length_makeReceiptsFrom (gasUsed : Nat) (results : List (Outcome fork × Nat × List Log)) :
    (makeReceiptsFrom gasUsed results).length = results.length := by
  induction results generalizing gasUsed with
  | nil => rfl
  | cons r rest ih => simp [makeReceiptsFrom, ih]

/-- Each receipt counts at least the gas of the block before the transactions. -/
theorem le_cumulativeGasUsed {gasUsed : Nat} {results : List (Outcome fork × Nat × List Log)}
    {r : Receipt fork} (h : r ∈ makeReceiptsFrom gasUsed results) :
    gasUsed ≤ r.cumulativeGasUsed := by
  induction results generalizing gasUsed with
  | nil => cases h
  | cons head rest ih =>
    obtain ⟨outcome, gas, logs⟩ := head
    simp only [makeReceiptsFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (Nat.le_add_right _ _) (ih h)

/-- The cumulative gas of the receipts never decreases. -/
theorem cumulativeGasUsed_pairwise (gasUsed : Nat)
    (results : List (Outcome fork × Nat × List Log)) :
    (makeReceiptsFrom gasUsed results).Pairwise
      (fun a b => a.cumulativeGasUsed ≤ b.cumulativeGasUsed) := by
  induction results generalizing gasUsed with
  | nil => exact .nil
  | cons head rest ih =>
    obtain ⟨outcome, gas, logs⟩ := head
    exact .cons (fun _ h => le_cumulativeGasUsed h) (ih _)

/-- Receipt `i` counts the gas of the block before, plus the gas of transactions `0` to `i`.

So two receipts in a row differ by the gas of the second transaction. -/
theorem getElem_makeReceiptsFrom_cumulativeGasUsed (gasUsed : Nat)
    (results : List (Outcome fork × Nat × List Log)) (i : Nat)
    (h : i < (makeReceiptsFrom gasUsed results).length) :
    (makeReceiptsFrom gasUsed results)[i].cumulativeGasUsed =
      gasUsed + ((results.take (i + 1)).map (·.2.1)).sum := by
  induction results generalizing gasUsed i with
  | nil => simp [makeReceiptsFrom] at h
  | cons head rest ih =>
    obtain ⟨outcome, gas, logs⟩ := head
    cases i with
    | zero => simp [makeReceiptsFrom, makeReceipt]
    | succ i =>
      simp only [makeReceiptsFrom, List.getElem_cons_succ, List.take_succ_cons, List.map_cons,
        List.sum_cons]
      rw [ih]
      omega

/-- The last receipt counts the gas of the block before, plus the gas of every transaction. -/
theorem getLast?_makeReceiptsFrom (gasUsed : Nat) (results : List (Outcome fork × Nat × List Log)) :
    (makeReceiptsFrom gasUsed results).getLast?.map (·.cumulativeGasUsed) =
      if results = [] then none else some (gasUsed + (results.map (·.2.1)).sum) := by
  induction results generalizing gasUsed with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨outcome, gas, logs⟩ := head
    cases rest with
    | nil => simp [makeReceiptsFrom, makeReceipt]
    | cons next more =>
      have := ih (gasUsed + gas)
      simp only [makeReceiptsFrom, reduceCtorEq, ↓reduceIte, List.map_cons,
        List.sum_cons] at this ⊢
      rw [List.getLast?_cons_cons, this]
      simp only [Option.some.injEq]
      omega

/-- The receipts hold the logs of the transactions, in order. -/
theorem flatMap_logs_makeReceiptsFrom (gasUsed : Nat)
    (results : List (Outcome fork × Nat × List Log)) :
    (makeReceiptsFrom gasUsed results).flatMap (·.logs) = results.flatMap (·.2.2) := by
  induction results generalizing gasUsed with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨outcome, gas, logs⟩ := head
    simp [makeReceiptsFrom, makeReceipt, ih]

/-- The filters of some receipts combine into the filter of all their logs. -/
theorem foldr_ofLogs (receipts : List (Receipt fork)) :
    (receipts.map fun r => Bloom.ofLogs r.logs).foldr (· ||| ·) 0 =
      Bloom.ofLogs (receipts.flatMap (·.logs)) := by
  induction receipts with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.map_cons, List.foldr_cons, List.flatMap_cons, Bloom.ofLogs_append]
    rw [ih]

/-- The filters of the receipts combine into the filter of all the logs of the block. -/
theorem ofLogs_makeReceipts (results : List (Outcome fork × Nat × List Log)) :
    ((makeReceipts results).map fun r => Bloom.ofLogs r.logs).foldr (· ||| ·) 0 =
      Bloom.ofLogs (results.flatMap (·.2.2)) := by
  rw [foldr_ofLogs, makeReceipts, flatMap_logs_makeReceiptsFrom]

end Receipts

end EthLib.Execution.Blocks
