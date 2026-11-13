module

public import EthLib.Execution.Rpc.Json
public import EthLib.Serialization.Proofs.JsonRpc
-- The fields of an encoded object unfold Lean's `Json.mkObj` and `Json.isNull`.
import all Lean.Data.Json.Basic

/-!
# Proofs: the JSON form of a withdrawal

A withdrawal reads exactly from an object with exactly its four fields, each of its type.

The writer of withdrawals writes what the reader reads back, alone or in a list.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Serialization.JsonRpc

/-- A withdrawal decodes exactly when its object holds exactly its four fields.

Its index, validator index and amount must decode as 64-bit numbers, and its address as 20 bytes.

Each becomes that field of the withdrawal. -/
theorem withdrawal_eq_ok_iff {j : Lean.Json} {w : Blocks.Withdrawal} :
    withdrawal j = .ok w ↔
      ∃ fs, fields "withdrawal" j = .ok fs ∧
        hasExactly fs ["index", "validatorIndex", "address", "amount"] = true ∧
        ∃ index validator recipient amount, fs.lookup "index" = some index ∧
          fs.lookup "validatorIndex" = some validator ∧ fs.lookup "address" = some recipient ∧
          fs.lookup "amount" = some amount ∧
          uint64 "index" index = .ok w.index ∧
          uint64 "validatorIndex" validator = .ok w.validatorIndex ∧
          address "address" recipient = .ok w.address ∧
          uint64 "amount" amount = .ok w.amount := by
  unfold withdrawal
  simp only [bind_ok_iff]
  constructor
  · rintro ⟨fs, hfs, h⟩
    by_cases hc : hasExactly fs ["index", "validatorIndex", "address", "amount"] = true
    · rw [ite_eq_left hc] at h
      simp only [bind_ok_iff, field_eq_ok_iff] at h
      obtain ⟨i, hl1, i', hf1, v, hl2, v', hf2, a, hl3, a', hf3, m, hl4, m', hf4, hw⟩ := h
      cases hw
      exact ⟨fs, hfs, hc, i, v, a, m, hl1, hl2, hl3, hl4, hf1, hf2, hf3, hf4⟩
    -- An object with other fields is rejected, never read as a withdrawal.
    · rw [ite_eq_right hc, bind_ok_iff] at h
      obtain ⟨_, hInvalid, -⟩ := h
      cases hInvalid
  · rintro ⟨fs, hfs, hc, i, v, a, m, hl1, hl2, hl3, hl4, hf1, hf2, hf3, hf4⟩
    refine ⟨fs, hfs, ?_⟩
    rw [ite_eq_left hc]
    simp only [bind_ok_iff, field_eq_ok_iff]
    exact ⟨i, hl1, _, hf1, v, hl2, _, hf2, a, hl3, _, hf3, m, hl4, _, hf4, rfl⟩

/-- The object of a withdrawal holds exactly its four fields, each the encoding of its value. -/
private theorem fields_withdrawalJson (w : Blocks.Withdrawal) :
    ∃ fs, fields "withdrawal" (withdrawalJson w) = .ok fs ∧
      hasExactly fs ["index", "validatorIndex", "address", "amount"] = true ∧
      fs.lookup "index" = some (quantityJson w.index.toNat) ∧
      fs.lookup "validatorIndex" = some (quantityJson w.validatorIndex.toNat) ∧
      fs.lookup "address" = some (dataJson w.address.toList) ∧
      fs.lookup "amount" = some (quantityJson w.amount.toNat) := by
  obtain ⟨kvs, hobj, hlen, hmem, hd⟩ := toList_mkObj (pairs := [
    ("index", quantityJson w.index.toNat), ("validatorIndex", quantityJson w.validatorIndex.toNat),
    ("address", dataJson w.address.toList), ("amount", quantityJson w.amount.toNat)])
    (by simp)
  -- No field is `null`, so every field of the object counts.
  have hkeep : kvs.toList.filter (fun (_, v) => !v.isNull) = kvs.toList := by
    refine List.filter_eq_self.mpr fun p hp => ?_
    have h := (hmem p).mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  have hm : ∀ p, p ∈ [("index", quantityJson w.index.toNat),
      ("validatorIndex", quantityJson w.validatorIndex.toNat),
      ("address", dataJson w.address.toList), ("amount", quantityJson w.amount.toNat)] →
      p ∈ kvs.toList := fun p h => (hmem p).mpr h
  refine ⟨kvs.toList, by rw [withdrawalJson, hobj, fields, hkeep]; rfl, ?_,
    lookup_of_mem hd (hm ("index", quantityJson w.index.toNat) (by simp)),
    lookup_of_mem hd (hm ("validatorIndex", quantityJson w.validatorIndex.toNat) (by simp)),
    lookup_of_mem hd (hm ("address", dataJson w.address.toList) (by simp)),
    lookup_of_mem hd (hm ("amount", quantityJson w.amount.toNat) (by simp))⟩
  simp only [hasExactly, hlen, List.length_cons, List.length_nil, beq_self_eq_true,
    Bool.true_and, List.all_eq_true, List.any_eq_true, beq_iff_eq]
  intro name hname
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hname
  rcases hname with rfl | rfl | rfl | rfl
  · exact ⟨("index", quantityJson w.index.toNat), hm _ (by simp), rfl⟩
  · exact ⟨("validatorIndex", quantityJson w.validatorIndex.toNat), hm _ (by simp), rfl⟩
  · exact ⟨("address", dataJson w.address.toList), hm _ (by simp), rfl⟩
  · exact ⟨("amount", quantityJson w.amount.toNat), hm _ (by simp), rfl⟩

/-- The decoder of withdrawals reads back the object that the encoder writes for a withdrawal. -/
theorem withdrawal_withdrawalJson (w : Blocks.Withdrawal) :
    withdrawal (withdrawalJson w) = .ok w := by
  obtain ⟨fs, hfs, hx, h1, h2, h3, h4⟩ := fields_withdrawalJson w
  exact withdrawal_eq_ok_iff.mpr ⟨fs, hfs, hx, _, _, _, _, h1, h2, h3, h4,
    uint64_toDigits _ _, uint64_toDigits _ _, fixed_hexString _ 20 _ true, uint64_toDigits _ _⟩

/-- The decoder of lists of withdrawals reads back the encoding of any list of withdrawals. -/
theorem array_withdrawal_listJson (what : String) (ws : List Blocks.Withdrawal) :
    array what withdrawal (listJson withdrawalJson ws) = .ok ws := by
  rw [array_listJson]
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.mapM_cons]
    rw [ih, withdrawal_withdrawalJson]
    rfl

end EthLib.Execution.Rpc
