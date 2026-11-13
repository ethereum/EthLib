module

public import EthLib.Networking.Quic.Varint
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: QUIC integers

Reading an integer written at any width that holds it returns that integer and the trailing bytes.

Every complete integer is accepted, and only a truncated input is rejected.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Varint

open EthLib.Base

/-- A chosen width writes exactly the byte count selected by its two-bit prefix. -/
theorem length_encodeWith (w : Width) (v : Varint) (h : v.val < capacity w) :
    (encodeWith w v h).length = 2 ^ w.val := by
  simp only [encodeWith, List.length_cons, natToBytes_length, tailLength]
  have : 0 < 2 ^ w.val := Nat.two_pow_pos _
  omega

/-- The top two bits of the first byte hold the width, and the low six bits the high part. -/
private theorem head_parts (w : Width) (v : Varint) (h : v.val < capacity w) :
    (UInt8.ofNat (w.val * 64 + v.val / 256 ^ tailLength w)).toNat / 64 = w.val ∧
    (UInt8.ofNat (w.val * 64 + v.val / 256 ^ tailLength w)).toNat % 64 =
      v.val / 256 ^ tailLength w := by
  have hp : 0 < 256 ^ tailLength w := Nat.pow_pos (by decide)
  have hq : v.val / 256 ^ tailLength w < 64 := by
    exact (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [capacity, Nat.mul_comm] using h)
  have hw := w.isLt
  have hhead : w.val * 64 + v.val / 256 ^ tailLength w < UInt8.size := by
    simp only [UInt8.size]
    omega
  simp only [UInt8.toNat_ofNat_of_lt' hhead]
  generalize v.val / 256 ^ tailLength w = q at hq ⊢
  constructor <;> omega

/-- Decoding undoes encoding at every width that holds the value, with any trailing bytes. -/
theorem decode_encodeWith (w : Width) (v : Varint) (h : v.val < capacity w)
    (rest : List UInt8) : decode (encodeWith w v h ++ rest) = .ok (v, rest) := by
  obtain ⟨hdiv, hmod⟩ := head_parts w v h
  have hselector : selector (UInt8.ofNat (w.val * 64 + v.val / 256 ^ tailLength w)) = w :=
    Fin.ext hdiv
  have hlen := natToBytes_length (tailLength w) v.val
  have hvalue : v.val / 256 ^ tailLength w * 256 ^ tailLength w +
      bytesToNat (natToBytes (tailLength w) v.val) = v.val := by
    rw [bytesToNat_natToBytes]
    exact Nat.div_add_mod' _ _
  simp only [encodeWith, List.cons_append, decode, valueOf, hselector, List.take_left' hlen,
    List.drop_left' hlen, hlen, hmod, hvalue, ↓reduceDIte]

/-- Decoding reads back the shortest encoding, with any trailing bytes. -/
theorem decode_encode (v : Varint) (rest : List UInt8) :
    decode (encode v ++ rest) = .ok (v, rest) :=
  decode_encodeWith _ _ _ _

/-- A read value splits back into the payload of the first byte and the tail bytes. -/
private theorem valueOf_div_mod (head : UInt8) (tail : List UInt8)
    (hlen : tail.length = tailLength (selector head)) :
    valueOf head tail / 256 ^ tailLength (selector head) = head.toNat % 64 ∧
      valueOf head tail % 256 ^ tailLength (selector head) = bytesToNat tail := by
  unfold valueOf
  have hlt := bytesToNat_lt tail
  rw [hlen] at hlt
  generalize tailLength (selector head) = c at hlt ⊢
  have hpos : 0 < 256 ^ c := Nat.pow_pos (by decide)
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

/-- A read value fits the width that its first byte selects. -/
private theorem valueOf_lt_capacity (head : UInt8) (tail : List UInt8)
    (hlen : tail.length = tailLength (selector head)) :
    valueOf head tail < capacity (selector head) := by
  have hpos : 0 < 256 ^ tailLength (selector head) := Nat.pow_pos (by decide)
  have hdiv := (valueOf_div_mod head tail hlen).1
  unfold capacity
  rw [← Nat.div_lt_iff_lt_mul hpos, hdiv]
  omega

/-- Writing a read value at the selected width gives back the bytes that were read. -/
private theorem encodeWith_valueOf (head : UInt8) (tail : List UInt8)
    (hlen : tail.length = tailLength (selector head)) (hv : valueOf head tail < 2 ^ 62)
    (hw : (⟨valueOf head tail, hv⟩ : Varint).val < capacity (selector head)) :
    encodeWith (selector head) ⟨valueOf head tail, hv⟩ hw = head :: tail := by
  obtain ⟨hdiv, hmod⟩ := valueOf_div_mod head tail hlen
  have hhead : UInt8.ofNat ((selector head).val * 64 + head.toNat % 64) = head := by
    simp only [selector]
    rw [Nat.mul_comm, Nat.div_add_mod]
    exact UInt8.ofNat_toNat
  simp only [encodeWith, hdiv, hhead, List.cons.injEq, true_and]
  rw [← natToBytes_mod, hmod, ← hlen, natToBytes_bytesToNat]

/-- Every input that decodes is the writing of its value at the selected width, then the rest.

So the decoder reads only valid encodings, minimal or not. -/
theorem eq_encodeWith_of_decode {head : UInt8} {tail rest : List UInt8} {v : Varint}
    (h : decode (head :: tail) = .ok (v, rest)) :
    ∃ hw, head :: tail = encodeWith (selector head) v hw ++ rest := by
  simp only [decode] at h
  split at h
  · rename_i hlen
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨valueOf_lt_capacity head _ hlen, ?_⟩
    rw [encodeWith_valueOf head _ hlen, List.cons_append, List.take_append_drop]
  · simp at h

/-- The width that the encoder picks is at most any width that holds the value. -/
theorem minWidth_le (v : Varint) (w : Width) (h : v.val < capacity w) : minWidth v ≤ w := by
  -- Closed width literals let the kernel compute each capacity.
  have : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by
    rcases w with ⟨w, hw⟩
    simp only [Fin.ext_iff]
    omega
  unfold minWidth
  rcases this with rfl | rfl | rfl | rfl <;> simp [capacity, tailLength] at h <;>
    repeat' split
  all_goals first | decide | omega

/-- No width writes a value in fewer bytes than the encoder does. -/
theorem length_encode_le (v : Varint) (w : Width) (h : v.val < capacity w) :
    (encode v).length ≤ (encodeWith w v h).length := by
  simp only [encode, length_encodeWith]
  exact Nat.pow_le_pow_right (by decide) (minWidth_le v w h)

/-- The empty input is rejected. -/
theorem decode_nil : decode [] = .error .truncated := rfl

/-- An input shorter than the selected width is rejected. -/
theorem decode_truncated (head : UInt8) (rest : List UInt8)
    (h : rest.length < tailLength (selector head)) :
    decode (head :: rest) = .error .truncated := by
  have : (rest.take (tailLength (selector head))).length ≠ tailLength (selector head) := by
    simp only [List.length_take]
    omega
  simp only [decode, this, ↓reduceDIte]

/-- Every complete integer is accepted, including longer representations of small values.

The value is the payload bits of the first byte followed by the selected tail bytes. -/
theorem decode_ok_of_length (head : UInt8) (rest : List UInt8)
    (h : tailLength (selector head) ≤ rest.length) :
    ∃ hv, decode (head :: rest) = .ok (⟨valueOf head (rest.take (tailLength (selector head))),
      hv⟩, rest.drop (tailLength (selector head))) := by
  have hlen : (rest.take (tailLength (selector head))).length = tailLength (selector head) := by
    simp only [List.length_take]
    exact Nat.min_eq_left h
  exact ⟨valueOf_lt _ _ hlen, by simp only [decode, hlen, ↓reduceDIte]⟩

/-- A nonempty input is rejected exactly when it ends before its selected length. -/
theorem decode_error_iff (head : UInt8) (rest : List UInt8) (error : VarintError) :
    decode (head :: rest) = .error error ↔ rest.length < tailLength (selector head) := by
  cases error
  by_cases h : rest.length < tailLength (selector head)
  · simp [decode_truncated head rest h, h]
  · obtain ⟨_, hv⟩ := decode_ok_of_length head rest (by omega)
    simp [hv, h]

end EthLib.Networking.Quic.Varint
