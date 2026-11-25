module

public import EthLib.Cryptography.Proofs.Hash.Keccak.Basic
public import EthLib.Base.Proofs.Bytes
public import EthLib.Base.Proofs.ByteOrder
public import Mathlib.Data.FinEnum
import Mathlib.Tactic

/-!
# Proofs: strings of lanes as bytes

The lanes are FIPS 202's representation of the state (§3.1.2, Appendix B.1).

A string of lanes is the byte string that lists each lane, least significant byte first.

The strings of lanes are in bijection with the byte strings whose length is a multiple of 8.

Keccak-256 of a string of lanes is Keccak-256 of its bytes.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

open Internal

/-! ## The bytes of a lane -/

/-- A lane is 8 bytes. -/
@[simp] theorem length_bytesOfLane (x : UInt64) : (bytesOfLane x).length = 8 := by
  simp [bytesOfLane]

/-- Byte `q` of a lane, for `q < 8`, is the lane shifted down by `8 q`. -/
theorem getD_bytesOfLane (v : UInt64) (q : Nat) (hq : q < 8) :
    (bytesOfLane v).getD q 0 = (v >>> (8 * q).toUInt64).toUInt8 := by
  interval_cases q <;> rfl

/-- Bit `i` of a lane's integer is the bit of its bit vector. -/
theorem testBit_toNat_lane (v : UInt64) (i : Nat) : v.toNat.testBit i = v.toBitVec.getLsbD i :=
  BitVec.testBit_toNat v.toBitVec

/-- Bit `t` of byte `q` of a number is its bit `8 q + t`. -/
theorem testBit_byte (x q t : Nat) (ht : t < 8) :
    (x / 2 ^ (8 * q) % 256).testBit t = x.testBit (8 * q + t) := by
  rw [show (256 : Nat) = 2 ^ 8 by rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [ht, Nat.add_comm]

/-- Bit `t` of byte `k` of a lane is the lane's bit `8 k + t`. -/
theorem testBit_getD_bytesOfLane (v : UInt64) (k t : Nat) (hk : k < 8) (ht : t < 8) :
    ((bytesOfLane v).getD k 0).toNat.testBit t = v.toNat.testBit (8 * k + t) := by
  rw [← testBit_byte _ _ _ ht]
  interval_cases k <;>
    simp [bytesOfLane, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-- The bytes of the lane read at byte `s` of a buffer are the buffer's bytes `s` to `s + 7`. -/
theorem getD_bytesOfLane_laneAt (b : ByteArray) (s k : Nat) (hk : k < 8) :
    (bytesOfLane (laneAt b s)).getD k 0 = EthLib.Base.byteAtOrZero b (s + k) := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 8
  · rw [testBit_getD_bytesOfLane _ _ _ hk ht,
      testBit_toNat_lane,
      laneAt_testBit _ _ _ (by omega), show (8 * k + t) / 8 = k by omega,
      show (8 * k + t) % 8 = t by omega]
  · have h1 : ((bytesOfLane (laneAt b s)).getD k 0).toNat < 2 ^ t :=
      lt_of_lt_of_le (UInt8.toNat_lt _) (Nat.pow_le_pow_right (by decide) (by omega))
    have h2 : (EthLib.Base.byteAtOrZero b (s + k)).toNat < 2 ^ t :=
      lt_of_lt_of_le (UInt8.toNat_lt _) (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

/-- Byte `j` of two lanes is byte `j mod 8` of the lane that holds it. -/
theorem getElem_lanes2_bytes (w : Lanes2) (j : Nat) (hj : j < 16) :
    w.bytes[j] = (bytesOfLane (if j < 8 then w.lo else w.hi)).getD (j % 8) 0 := by
  interval_cases j <;> rfl

/-- Byte `j` of four lanes is byte `j mod 8` of the lane that holds it. -/
theorem getElem_lanes4_bytes (w : Lanes4) (j : Nat) (hj : j < 32) :
    w.bytes[j] = (bytesOfLane (if j < 8 then w.w0 else if j < 16 then w.w1 else
      if j < 24 then w.w2 else w.w3)).getD (j % 8) 0 := by
  interval_cases j <;> rfl

/-! ## Strings of lanes as bytes -/

/-- The bytes of a string of lanes: lane after lane, each least significant byte first. -/
def lanesBytes (lanes : Array UInt64) : List UInt8 :=
  lanes.toList.flatMap bytesOfLane

/-- The bytes of two strings of lanes, joined, are the joined bytes. -/
@[simp] theorem lanesBytes_append (a b : Array UInt64) :
    lanesBytes (a ++ b) = lanesBytes a ++ lanesBytes b := by
  simp [lanesBytes]

/-- A list of lanes has 8 bytes a lane. -/
private theorem length_flatMap_bytesOfLane (l : List UInt64) :
    (l.flatMap bytesOfLane).length = 8 * l.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]; omega

/-- A string of lanes has 8 bytes a lane. -/
@[simp] theorem length_lanesBytes (a : Array UInt64) : (lanesBytes a).length = 8 * a.size := by
  rw [lanesBytes, length_flatMap_bytesOfLane, Array.length_toList]

/-- A byte of the zero lane reads as zero, also past the end of the lane. -/
private theorem getD_bytesOfLane_zero (k : Nat) : (bytesOfLane 0).getD k 0 = 0 := by
  by_cases hk : k < 8
  · interval_cases k <;> simp [bytesOfLane]
  · simp [List.getD_eq_getElem?_getD, Nat.not_lt.mp hk]

/-- Byte `8 j + k` of a string of lanes is byte `k` of lane `j`, and zero past the end. -/
theorem getD_flatMap_bytesOfLane (l : List UInt64) (j k : Nat) (hk : k < 8) :
    (l.flatMap bytesOfLane).getD (8 * j + k) 0 = (bytesOfLane (l.getD j 0)).getD k 0 := by
  induction l generalizing j with
  | nil => simpa using (getD_bytesOfLane_zero k).symm
  | cons x l ih =>
    cases j with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simp [hk])]
    | succ j =>
      simp only [List.flatMap_cons, List.getD_cons_succ]
      rw [show 8 * (j + 1) + k = (bytesOfLane x).length + (8 * j + k) by simp; omega]
      simp only [List.getD_eq_getElem?_getD] at ih ⊢
      rw [List.getElem?_append_right (by simp)]
      simpa using ih j

/-- A byte that a list holds, read by index, is the byte of the byte array. -/
private theorem byteAtOrZero_mk (l : List UInt8) (i : Nat) :
    EthLib.Base.byteAtOrZero ⟨l.toArray⟩ i = l.getD i 0 := by
  have hsize : (ByteArray.mk l.toArray).size = l.length := by simp [ByteArray.size]
  unfold EthLib.Base.byteAtOrZero
  split
  · next h =>
    rw [hsize] at h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    rfl
  · next h =>
    rw [hsize] at h
    simp [List.getD_eq_getElem?_getD, Nat.not_lt.mp h]

/-- The lane at byte `8 j` of the bytes of a string of lanes is lane `j` of the string. -/
theorem laneAt_lanesBytes (a : Array UInt64) (j : Nat) :
    laneAt ⟨(lanesBytes a).toArray⟩ (8 * j) = laneOfArray a (8 * j) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [laneAt_testBit _ _ _ hi, byteAtOrZero_mk, laneOfArray, lanesBytes,
    getD_flatMap_bytesOfLane _ _ _ (by omega),
    testBit_getD_bytesOfLane _ _ _ (by omega) (by omega), Nat.mul_div_cancel_left _ (by omega),
    ← testBit_toNat_lane, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList]
  simp [List.getD_eq_getElem?_getD, show 8 * (i / 8) + i % 8 = i by omega]

/-- Two strings of lanes with the same bytes are the same lanes. -/
theorem lanesBytes_injective : Function.Injective lanesBytes := by
  intro a b h
  have hsize : a.size = b.size := by
    have := congrArg List.length h
    simp only [length_lanesBytes] at this
    omega
  have hlane : ∀ j, laneOfArray a (8 * j) = laneOfArray b (8 * j) := fun j => by
    rw [← laneAt_lanesBytes, ← laneAt_lanesBytes, h]
  apply Array.ext hsize
  intro j h1 h2
  have := hlane j
  simpa [laneOfArray, h1, h2] using this

/-- Every byte string whose length is a multiple of 8 is the bytes of some string of lanes. -/
theorem exists_lanesBytes_eq {l : List UInt8} (h : 8 ∣ l.length) : ∃ a, lanesBytes a = l := by
  obtain ⟨n, hn⟩ := h
  refine ⟨(List.range n).toArray.map fun j => laneAt ⟨l.toArray⟩ (8 * j), ?_⟩
  apply List.ext_getElem (by simp [hn])
  intro i h1 h2
  have hi : i < 8 * n := by simpa [hn] using h2
  rw [List.getElem_eq_getD (fallback := 0), List.getElem_eq_getD (fallback := 0),
    show i = 8 * (i / 8) + i % 8 by omega, lanesBytes,
    getD_flatMap_bytesOfLane _ _ _ (by omega)]
  have hj : i / 8 < n := by omega
  simp only [Array.toList_map, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some]
  have := getD_bytesOfLane_laneAt ⟨l.toArray⟩ (8 * (i / 8)) (i % 8) (by omega)
  rw [byteAtOrZero_mk] at this
  simpa [List.getD_eq_getElem?_getD] using this

/-- The strings of lanes are in bijection with the byte strings whose length is a multiple of 8.

The bijection lists the bytes of each lane. -/
noncomputable def lanesBytesEquiv : Array UInt64 ≃ {l : List UInt8 // 8 ∣ l.length} where
  toFun a := ⟨lanesBytes a, ⟨a.size, length_lanesBytes a⟩⟩
  invFun l := Classical.choose (exists_lanesBytes_eq l.2)
  left_inv a := lanesBytes_injective
    (Classical.choose_spec (exists_lanesBytes_eq ⟨a.size, length_lanesBytes a⟩))
  right_inv l := Subtype.ext (Classical.choose_spec (exists_lanesBytes_eq l.2))

/-- The bytes of two lanes are the bytes of the array of the two lanes. -/
@[simp] theorem lanesBytes_lanes2 (w : Lanes2) : lanesBytes w.toArray = w.bytes.toList := by
  simp [lanesBytes, Lanes2.toArray, Lanes2.bytes, bytesOfLane]

/-- The bytes of four lanes are the bytes of the array of the four lanes. -/
@[simp] theorem lanesBytes_lanes4 (w : Lanes4) : lanesBytes w.toArray = w.bytes.toList := by
  simp [lanesBytes, Lanes4.toArray, Lanes4.bytes, bytesOfLane]

/-- The bytes of one lane are the bytes of the array of that lane. -/
@[simp] theorem lanesBytes_singleton (x : UInt64) : lanesBytes #[x] = bytesOfLane x := by
  simp [lanesBytes]

/-! ## The integer of two lanes -/

/-- The integer below `2^128` that a 16-byte value's two lanes make: `lo + 2^64 * hi`. -/
def Lanes2.toNat (w : Lanes2) : Nat :=
  w.lo.toNat + 2 ^ 64 * w.hi.toNat

/-- Two lanes make an integer below `2^128`. -/
theorem Lanes2.toNat_lt (w : Lanes2) : w.toNat < 2 ^ 128 := by
  have := w.lo.toNat_lt
  have := w.hi.toNat_lt
  unfold Lanes2.toNat
  omega

/-- Two lanes are their integer: the low lane is its remainder by `2^64`, the high its quotient. -/
theorem Lanes2.toNat_injective : Function.Injective Lanes2.toNat := by
  intro a b h
  have := a.lo.toNat_lt
  have := a.hi.toNat_lt
  have := b.lo.toNat_lt
  have := b.hi.toNat_lt
  unfold Lanes2.toNat at h
  have hlo : a.lo.toNat = b.lo.toNat := by omega
  have hhi : a.hi.toNat = b.hi.toNat := by omega
  cases a
  cases b
  simp only [Lanes2.mk.injEq]
  exact ⟨UInt64.toNat_inj.mp hlo, UInt64.toNat_inj.mp hhi⟩

/-! ## The bytes of two lanes -/

/-- Byte `j` of two lanes is byte `j` of the low lane, or byte `j - 8` of the high lane. -/
theorem Lanes2.toNat_getElem_bytes (w : Lanes2) (j : Nat) (hj : j < 16) :
    (w.bytes[j]).toNat =
      if j < 8 then w.lo.toNat / 2 ^ (8 * j) % 256 else w.hi.toNat / 2 ^ (8 * (j - 8)) % 256 := by
  interval_cases j <;>
    simp [Lanes2.bytes, UInt64.toNat_shiftRight,
      Nat.shiftRight_eq_div_pow]

/-- The bytes of two lanes are the little-endian bytes of their integer. -/
theorem Lanes2.bytes_eq_toLE (w : Lanes2) : w.bytes = Base.ByteOrder.toLE 16 w.toNat := by
  have := w.lo.toNat_lt
  apply Vector.ext
  intro j hj
  apply UInt8.toNat_inj.mp
  rw [Lanes2.toNat_getElem_bytes _ _ hj]
  simp only [Base.ByteOrder.toLE, Lanes2.toNat, Vector.getElem_ofFn, UInt8.toNat_ofNat',
    Nat.shiftRight_eq_div_pow]
  interval_cases j <;>
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceLT, Nat.reduceSub, ite_true, ite_false] <;>
    omega

/-- The little-endian integer of the bytes of two lanes is the integer of the lanes. -/
theorem Lanes2.ofLE_bytes (w : Lanes2) : Base.ByteOrder.ofLE w.bytes = w.toNat := by
  rw [w.bytes_eq_toLE, Base.ByteOrder.ofLE_toLE,
    Nat.mod_eq_of_lt (by simpa using w.toNat_lt)]

/-- The bytes of the two lanes read at an offset are the 16 bytes there. -/
theorem Lanes2.bytes_read (b : ByteArray) (offset : Nat) (h : offset + 16 ≤ b.size) :
    (Lanes2.read b offset).bytes = Base.readBytes b offset 16 h := by
  apply Vector.ext
  intro j hj
  have hread : (Base.readBytes b offset 16 h)[j] = Base.byteAtOrZero b (offset + j) := by
    simp only [Base.readBytes_eq_ofFn_data, Vector.getElem_ofFn, Base.byteAtOrZero,
      dite_eq_left_of_eq_true (eq_true (show offset + j < b.size by omega))]
    rfl
  -- Byte `j` is byte `j mod 8` of the lane that holds it, read from the buffer.
  rw [hread, getElem_lanes2_bytes _ _ hj]
  simp only [Lanes2.read]
  split
  · rw [getD_bytesOfLane_laneAt _ _ _ (by omega), Nat.mod_eq_of_lt ‹_›]
  · rw [getD_bytesOfLane_laneAt _ _ _ (by omega)]
    congr 1
    omega

/-- Two lanes with the same bytes are the same lanes. -/
theorem Lanes2.bytes_injective : Function.Injective Lanes2.bytes := by
  intro a b h
  have := congrArg Base.ByteOrder.ofLE h
  rw [Lanes2.ofLE_bytes, Lanes2.ofLE_bytes] at this
  exact Lanes2.toNat_injective this

/-- The bytes of the four lanes read at an offset are the 32 bytes there. -/
theorem Lanes4.bytes_read (b : ByteArray) (offset : Nat) (h : offset + 32 ≤ b.size) :
    (Lanes4.read b offset).bytes = Base.readBytes b offset 32 h := by
  apply Vector.ext
  intro j hj
  have hread : (Base.readBytes b offset 32 h)[j] = Base.byteAtOrZero b (offset + j) := by
    simp only [Base.readBytes_eq_ofFn_data, Vector.getElem_ofFn, Base.byteAtOrZero,
      dite_eq_left_of_eq_true (eq_true (show offset + j < b.size by omega))]
    rfl
  -- Byte `j` is byte `j mod 8` of the lane that holds it, read from the buffer.
  rw [hread, getElem_lanes4_bytes _ _ hj]
  simp only [Lanes4.read]
  split_ifs <;> rw [getD_bytesOfLane_laneAt _ _ _ (by omega)] <;>
    exact congrArg (Base.byteAtOrZero b) (by omega)

/-- Four lanes with the same bytes are the same lanes.

Bytes 0 to 15 are the bytes of the first two lanes, and bytes 16 to 31 those of the last two. -/
theorem Lanes4.bytes_injective : Function.Injective Lanes4.bytes := by
  intro a b h
  -- The list of 32 bytes splits into the lists of the two halves.
  have split : ∀ w : Lanes4, w.bytes.toList =
      (⟨w.w0, w.w1⟩ : Lanes2).bytes.toList ++ (⟨w.w2, w.w3⟩ : Lanes2).bytes.toList :=
    fun _ => rfl
  have hl := congrArg Vector.toList h
  rw [split, split] at hl
  obtain ⟨h01, h23⟩ := List.append_inj hl (by simp)
  obtain ⟨e0, e1⟩ := Lanes2.mk.inj (Lanes2.bytes_injective (Vector.toList_inj.mp h01))
  obtain ⟨e2, e3⟩ := Lanes2.mk.inj (Lanes2.bytes_injective (Vector.toList_inj.mp h23))
  cases a
  cases b
  simp_all

/-! ## Strings of lanes with lanes appended -/

/-- The lanes of a string with two lanes appended: its own, then the two, then zeros.

At each multiple of 8, it is the reader of the string alone, with the two lanes XORed in. -/
theorem laneOfArray_append_two (before : Array UInt64) (lo hi : UInt64) (q : Nat) (hq : 8 ∣ q) :
    laneOfArray (before ++ #[lo, hi]) q =
      if q = 8 * (before.size + 1) then
        (if q = 8 * before.size then laneOfArray before q ^^^ lo else laneOfArray before q) ^^^ hi
      else if q = 8 * before.size then laneOfArray before q ^^^ lo else laneOfArray before q := by
  obtain ⟨j, rfl⟩ := hq
  simp only [laneOfArray, Nat.mul_div_cancel_left _ (by decide : 0 < 8),
    Array.getD_eq_getD_getElem?, Array.getElem?_append]
  by_cases h1 : j < before.size
  · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_right (by omega)]
  · obtain ⟨k, rfl⟩ : ∃ k, j = before.size + k := ⟨j - before.size, by omega⟩
    have hn : before[before.size + k]? = none := Array.getElem?_eq_none (by omega)
    rw [ite_eq_right h1, hn, Option.getD_none, Nat.add_sub_cancel_left]
    rcases k with _ | _ | k
    · simp only [Nat.add_zero] at hn ⊢
      rw [ite_eq_right (by omega)]
      simp
    · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
      simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp


/-! ## Keccak-256 of lanes -/

/-- Keccak-256 of a message read a lane at a time is Keccak-256 of the message.

The reader gives the message's lanes at every multiple of 8, as reading the bytes does.

It holds over every permutation, in every monad. -/
theorem keccak256Read_eq_keccak256With {m : Type → Type} [Monad m] (f : State → m State)
    (msg : ByteArray) (read : Nat → UInt64) (h : ∀ q, 8 ∣ q → read q = laneAt msg q) :
    Lanes4.bytes <$> keccak256Read f msg.size read = keccak256With f msg := by
  rw [keccak256With, keccak256Read, keccak256Read]
  unfold spongeAbsorb
  rw [stateBeforeLastPermutation_congr f lanes_rate msg.size h]
  rfl

/-- Keccak-256 of a string of lanes is Keccak-256 of its bytes, over every permutation. -/
theorem keccak256LanesWith_lanesBytes {m : Type → Type} [Monad m] (f : State → m State)
    (a : Array UInt64) :
    Lanes4.bytes <$> keccak256LanesWith f a = keccak256With f ⟨(lanesBytes a).toArray⟩ := by
  have hsize : (ByteArray.mk (lanesBytes a).toArray).size = 8 * a.size := by
    simp [ByteArray.size]
  rw [keccak256LanesWith, ← hsize]
  refine keccak256Read_eq_keccak256With f _ _ fun q hq => ?_
  obtain ⟨j, rfl⟩ := hq
  exact (laneAt_lanesBytes a j).symm

/-- Keccak-256 of a string of lanes is Keccak-256 of its bytes. -/
theorem keccak256Lanes_lanesBytes (a : Array UInt64) :
    (keccak256Lanes a).bytes = keccak256 ⟨(lanesBytes a).toArray⟩ :=
  congrArg Id.run (keccak256LanesWith_lanesBytes (m := Id) (fun S => pure (keccakF S)) a)

/-! ## The values of two lanes -/

/-- Two lanes are two 64-bit words. -/
def lanes2Equiv : Lanes2 ≃ UInt64 × UInt64 where
  toFun w := (w.lo, w.hi)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The values of two lanes are finitely many. -/
instance : Fintype Lanes2 := Fintype.ofEquiv _ lanes2Equiv.symm

/-- There are `2^128` values of two lanes. -/
theorem card_lanes2 : Fintype.card Lanes2 = 2 ^ 128 := by
  rw [Fintype.card_congr lanes2Equiv, Fintype.card_prod, ← FinEnum.card_eq_fintypeCard,
    FinEnum.card_UInt64]
  norm_num

end EthLib.Cryptography.Hash.Keccak
