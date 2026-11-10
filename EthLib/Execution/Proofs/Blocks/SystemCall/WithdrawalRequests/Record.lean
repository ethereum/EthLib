module

public import EthLib.Execution.Proofs.Blocks.SystemCall.RequestQueue
public import EthLib.Execution.Proofs.Evm.Instructions.Bitwise

/-!
# Proofs: the record of a withdrawal request in memory

The system call of the withdrawal request contract writes a record of 76 bytes per request.

The record is three words of memory, then eight single bytes in reverse order.

Each lemma here gives what memory holds after some of these writes, or what the bytes are.

None of them reads the bytecode of the contract.
-/

@[expose] public section

namespace EthLib.Execution.Blocks.WithdrawalRequests

open EthLib.Base (Fork U256 byteAt_extract)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Blocks.RequestQueue
open GasCosts

variable {fork : Fork} {message : Message fork} {returnData : ByteArray}

/-- The three words that start a record of 76 bytes, after the bytes `pre` from offset 0.

The first word holds the address in its first 20 bytes, the second the first 32 bytes of the key.

The third holds the end of the key in its first 16 bytes, under the mask of the code.

Each write starts where the bytes before it end, so it overwrites the tail of the word before.

Memory then holds `pre`, the address, the second word and the first 16 bytes of the third. -/
theorem holds_head {M M₁ M₂ M₃ pre : ByteArray} {off e₁ e₂ e₃ : Nat} {v₀ v₁ v₂ : U256}
    (hpre : Holds M 0 pre) (hoff : pre.size = off)
    (hM₁ : M₁ = memoryWrite (memoryExtend M e₁) off (wordBytes (bitwiseShl 96#256 v₀)))
    (hM₂ : M₂ = memoryWrite (memoryExtend M₁ e₂) (off + 20) (wordBytes v₁))
    (hM₃ : M₃ = memoryWrite (memoryExtend M₂ e₃) (off + 52) (wordBytes (bitwiseAnd
      0xffffffffffffffffffffffffffffffff00000000000000000000000000000000#256 v₂)))
    (h₁ : off + 32 ≤ M.size + e₁) (h₂ : off + 20 + 32 ≤ M₁.size + e₂)
    (h₃ : off + 52 + 32 ≤ M₂.size + e₃) :
    Holds M₃ 0 (pre ++ ((wordBytes v₀).extract 12 32 ++ wordBytes v₁ ++
      (wordBytes v₂).extract 0 16)) := by
  have s := size_wordBytes
  have w₁ : off + (wordBytes (bitwiseShl 96#256 v₀)).size ≤ M.size + e₁ := by rw [s]; exact h₁
  have w₂ : off + 20 + (wordBytes v₁).size ≤ M₁.size + e₂ := by rw [s]; omega
  have w₃ : off + 52 + (wordBytes (bitwiseAnd
      0xffffffffffffffffffffffffffffffff00000000000000000000000000000000#256 v₂)).size ≤
      M₂.size + e₃ := by rw [s]; omega
  have hA₁ : Holds M₁ off ((wordBytes v₀).extract 12 32) := by
    have hw := hM₁ ▸ holds_extend_write w₁
    have hfit : off + ((wordBytes v₀).extract 12 32).size ≤ M₁.size := by
      have := hw.1
      simp only [s, ByteArray.size_extract] at this ⊢
      omega
    refine Holds.of_byteAt hfit fun i hi => ?_
    simp only [ByteArray.size_extract, s] at hi
    rw [hw.byteAt_eq (by rw [s]; omega), byteAt_wordBytes_shl v₀ (by omega), byteAt_extract, s,
      ite_eq_left (by omega)]
  have hsA : ((wordBytes v₀).extract 12 32).size = 20 := by simp [s]
  have hA₂ : Holds M₂ off ((wordBytes v₀).extract 12 32) :=
    hM₂ ▸ Holds.extend_write hA₁ w₂ (by omega)
  have hA₃ : Holds M₃ off ((wordBytes v₀).extract 12 32) :=
    hM₃ ▸ Holds.extend_write hA₂ w₃ (by omega)
  have hB₂ : Holds M₂ (off + 20) (wordBytes v₁) := hM₂ ▸ holds_extend_write w₂
  have hB₃ : Holds M₃ (off + 20) (wordBytes v₁) :=
    hM₃ ▸ Holds.extend_write hB₂ w₃ (by rw [s]; omega)
  have hC₃ : Holds M₃ (off + 52) ((wordBytes v₂).extract 0 16) := by
    have hw := hM₃ ▸ holds_extend_write w₃
    have hfit : off + 52 + ((wordBytes v₂).extract 0 16).size ≤ M₃.size := by
      have := hw.1
      simp only [s, ByteArray.size_extract] at this ⊢
      omega
    refine Holds.of_byteAt hfit fun i hi => ?_
    simp only [ByteArray.size_extract, s] at hi
    rw [hw.byteAt_eq (by rw [s]; omega), byteAt_wordBytes_and v₂ (by omega), byteAt_extract, s,
      ite_eq_left (by omega), Nat.zero_add]
  have hP₁ : Holds M₁ 0 pre := hM₁ ▸ Holds.extend_write hpre w₁ (by omega)
  have hP₂ : Holds M₂ 0 pre := hM₂ ▸ Holds.extend_write hP₁ w₂ (by omega)
  have hP₃ : Holds M₃ 0 pre := hM₃ ▸ Holds.extend_write hP₂ w₃ (by omega)
  have hR := (Holds.append hA₃ (by rw [hsA]; exact hB₃)).append
    (by rw [ByteArray.size_append, hsA, s]; exact hC₃)
  exact Holds.append hP₃ (by rw [Nat.zero_add, hoff]; exact hR)

/-- Bytes 16 to 23 of a word, as the word over powers of 256, modulo 256. -/
theorem extract_amount (v : U256) : (wordBytes v).extract 16 24 =
    ⟨[UInt8.ofNat (v.toNat / 256 ^ 15), UInt8.ofNat (v.toNat / 256 ^ 14),
      UInt8.ofNat (v.toNat / 256 ^ 13), UInt8.ofNat (v.toNat / 256 ^ 12),
      UInt8.ofNat (v.toNat / 256 ^ 11), UInt8.ofNat (v.toNat / 256 ^ 10),
      UInt8.ofNat (v.toNat / 256 ^ 9), UInt8.ofNat (v.toNat / 256 ^ 8)].toArray⟩ := by
  refine EthLib.Base.eq_of_byteAt (by rw [ByteArray.size_extract, size_wordBytes]; rfl)
    fun j => ?_
  rw [byteAt_extract, size_wordBytes]
  by_cases hj : j < 8
  · rw [ite_eq_left (by omega), byteAt_wordBytes _ (by omega)]
    obtain _ | _ | _ | _ | _ | _ | _ | _ | j := j
    all_goals first | rfl | omega
  · rw [ite_eq_right (by omega), EthLib.Base.byteAt_of_size_le (by
      show 8 ≤ j
      omega)]

/-- The eight bytes that the code writes from offset 68 of a record, from the third word `v`.

They are the bytes 16 to 23 of the word, in reverse order. -/
theorem amount_bytes (v : U256) :
    (⟨[UInt8.ofNat (bitwiseShr 64#256 v).toNat,
      UInt8.ofNat (bitwiseShr 8#256 (bitwiseShr 64#256 v)).toNat,
      UInt8.ofNat (bitwiseShr 16#256 (bitwiseShr 64#256 v)).toNat,
      UInt8.ofNat (bitwiseShr 24#256 (bitwiseShr 64#256 v)).toNat,
      UInt8.ofNat (bitwiseShr 32#256 (bitwiseShr 64#256 v)).toNat,
      UInt8.ofNat (bitwiseShr 40#256 (bitwiseShr 64#256 v)).toNat,
      UInt8.ofNat (bitwiseShr 48#256 (bitwiseShr 64#256 v)).toNat,
      UInt8.ofNat (bitwiseShr 56#256 (bitwiseShr 64#256 v)).toNat].toArray⟩ : ByteArray) =
      ⟨((wordBytes v).extract 16 24).data.reverse⟩ := by
  rw [extract_amount]
  simp only [toNat_bitwiseShr, BitVec.reduceToNat, Nat.div_div_eq_div_mul, List.reverse_toArray,
    List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append]

end EthLib.Execution.Blocks.WithdrawalRequests
