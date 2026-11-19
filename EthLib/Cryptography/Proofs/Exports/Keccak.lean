module

public import EthLib.Cryptography.Exports.Keccak
public import EthLib.Cryptography.Proofs.Hash.Keccak.BitsSponge
import all EthLib.Cryptography.Exports.Keccak

/-!
# Proofs: `Cryptography.Exports.Keccak`

The permutation export reads a 200-byte state into lanes, applies Keccak-f[1600] and writes back.

This file proves that it returns the bit-level Keccak-f[1600] of FIPS 202 §3.3 and Algorithm 7.

Bit `64(5y + x) + z` of the state string is `A[x, y, z]`, by FIPS 202 §3.1.2.

The output is written back in the same order, by FIPS 202 §3.1.3.

Each byte holds its bits from the least significant, by FIPS 202 Appendix B.1.
-/

public section

namespace EthLib.Cryptography.Hash.Exports

open EthLib.Cryptography.Models.KeccakBits (ofLanes ofLanes_ofLanes ofString messageBits
  messageBits_get messageBits_length permutation permutation_ofLanes squeezeBytes outputByte_ofLanes
  index)

/-- Joining groups of 8 bytes gives 8 bytes per group. -/
private theorem length_flatMap_eight {α : Type} (g : α → List UInt8) (hg : ∀ a, (g a).length = 8)
    (l : List α) : (l.flatMap g).length = 8 * l.length := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    simp [hg, ih]
    omega

/-- Byte `i` of joined groups of 8 bytes is byte `i % 8` of group `i / 8`. -/
private theorem getElem_flatMap_eight {α : Type} (g : α → List UInt8) (hg : ∀ a, (g a).length = 8)
    (l : List α) (i : Nat) (h : i < 8 * l.length) :
    (l.flatMap g)[i]'(by rw [length_flatMap_eight g hg]; exact h) =
      (g (l[i / 8]'(by omega)))[i % 8]'(by rw [hg]; omega) := by
  induction l generalizing i with
  | nil => simp at h
  | cons b bs ih =>
    have hlen : (g b).length = 8 := hg b
    simp only [List.flatMap_cons]
    by_cases hi : i < 8
    -- The first eight bytes come from the first group.
    · rw [List.getElem_append_left (by simpa [hlen] using hi)]
      have div : i / 8 = 0 := Nat.div_eq_of_lt hi
      have rem : i % 8 = i := Nat.mod_eq_of_lt hi
      simp [div, rem]
    -- The later bytes come from the remaining groups, eight positions earlier.
    · rw [List.getElem_append_right (by omega : (g b).length ≤ i)]
      have k : i - 8 < 8 * bs.length := by
        simp only [List.length_cons] at h
        omega
      have j : (i - 8) / 8 + 1 = i / 8 := by omega
      have r : (i - 8) % 8 = i % 8 := by omega
      simp only [hlen]
      rw [ih (i - 8) k]
      simp only [← j, List.getElem_cons_succ, r]

/-- The lanes read from a 200-byte string are its bits at the coordinates of FIPS 202 §3.1.2. -/
private theorem ofLanes_laneAt {state : ByteArray} (h : state.size = 200) :
    ofLanes (Keccak.State.ofLanes fun x y => Keccak.Internal.laneAt state (8 * (x.val + 5 * y.val)))
      = ofString (messageBits state) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have hi : index x y z < 8 * state.size := by
    simp only [index, h]
    omega
  have hb : index x y z / 8 < state.size := by omega
  simp only [ofLanes_ofLanes, ofString, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by rw [messageBits_length]; exact hi), Option.getD_some,
    messageBits_get _ _ hi, Keccak.Internal.laneAt_testBit _ _ _ hz]
  -- Bit `z` of lane `x + 5y` is bit `z % 8` of byte `8(x + 5y) + z / 8`.
  have byte : 8 * (x.val + 5 * y.val) + z.val / 8 = index x y z / 8 := by
    simp only [index]
    omega
  have bit : z.val % 8 = index x y z % 8 := by
    simp only [index]
    omega
  rw [byte, bit, EthLib.Base.byteAt, dif_pos hb]
  rfl

/-- The bytes of the 25 lanes, in order, are the 200 output bytes of the bit state. -/
private theorem bytesOfLanes_eq (B : Keccak.State) :
    ([B.a0, B.a1, B.a2, B.a3, B.a4, B.a5, B.a6, B.a7, B.a8, B.a9, B.a10, B.a11, B.a12, B.a13,
      B.a14, B.a15, B.a16, B.a17, B.a18, B.a19, B.a20, B.a21, B.a22, B.a23,
      B.a24].flatMap Keccak.Internal.bytesOfLane).toArray =
      (squeezeBytes 200 (ofLanes B)).toArray := by
  apply Array.ext
  · rw [List.size_toArray, length_flatMap_eight _ (fun _ => rfl), Vector.size_toArray]
    rfl
  · intro i h₁ h₂
    have hi : i < 200 := by simpa using h₂
    simp only [List.getElem_toArray, Vector.getElem_toArray, squeezeBytes, Vector.getElem_ofFn]
    rw [getElem_flatMap_eight _ (fun _ => rfl) _ i (by simp only [List.length_cons,
      List.length_nil]; omega), outputByte_ofLanes B hi]
    -- Group `i / 8` is lane `((i / 8) % 5, i / 40)`, the lane at index `i / 8`.
    have lane : [B.a0, B.a1, B.a2, B.a3, B.a4, B.a5, B.a6, B.a7, B.a8, B.a9, B.a10, B.a11, B.a12,
        B.a13, B.a14, B.a15, B.a16, B.a17, B.a18, B.a19, B.a20, B.a21, B.a22, B.a23,
        B.a24][i / 8]'(by simp only [List.length_cons, List.length_nil]; omega) =
        B.lane ⟨(i / 8) % 5, by omega⟩ ⟨i / 40, by omega⟩ := by
      simp only [Keccak.State.lane, show (i / 8) % 5 + 5 * (i / 40) = i / 8 by omega]
      exact (getElem!_pos _ (i / 8) (by simp only [List.length_cons, List.length_nil]; omega)).symm
    simp only [lane]

/-- For every 200-byte state, the export returns Keccak-f[1600] of the bit model.

Output byte `i` is byte `i` of the permuted state string, by FIPS 202 §3.1.3 and Appendix B.1. -/
theorem keccakF1600_eq {state : ByteArray} (h : state.size = 200) :
    keccakF1600 state =
      .ok ⟨(squeezeBytes 200 (permutation (ofString (messageBits state)))).toArray⟩ := by
  rw [← ofLanes_laneAt h, ← permutation_ofLanes, ← bytesOfLanes_eq]
  -- The size check passes, and the export reads, permutes and writes the same lanes.
  have size : ¬ (state.size ≠ 8 * Keccak.LANES) := by
    simp only [h, Keccak.LANES, ne_eq, not_not]
  unfold keccakF1600
  simp only [size, ↓reduceIte]
  rfl

end EthLib.Cryptography.Hash.Exports
