import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import EthLib.Precompiles.Modexp.Bytes

/-!
# Proofs: `Bytes`

How the call data is read and the output is written.

- A list of `k` bytes holds a big-endian value below `256 ^ k`.
- Writing `n` on `len` bytes gives exactly `len` bytes, which read back as `n % 256 ^ len`.
- Reading past the end of the call data gives zeros.
  So padding the call data with zeros changes no read.
- A read depends only on the bytes it covers.
-/

namespace EthLib.Precompiles.Modexp

/-- Folding from any start value shifts it by one factor of 256 per byte. -/
theorem foldl_bytesToNat (bytes : List UInt8) (acc : Nat) :
    bytes.foldl (fun acc b => acc * 256 + b.toNat) acc
      = acc * 256 ^ bytes.length + bytesToNat bytes := by
  induction bytes generalizing acc with
  | nil => simp [bytesToNat]
  | cons b rest ih =>
    -- Unfold one byte on both sides, then use the induction hypothesis twice.
    have h0 := ih (b.toNat)
    have h1 := ih (acc * 256 + b.toNat)
    simp only [bytesToNat, List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add] at *
    rw [h1, h0, Nat.pow_succ]
    ring

/-- Appending bytes on the right shifts the earlier value left by their count. -/
theorem bytesToNat_append (a b : List UInt8) :
    bytesToNat (a ++ b) = bytesToNat a * 256 ^ b.length + bytesToNat b := by
  rw [bytesToNat, List.foldl_append, foldl_bytesToNat]
  rfl

/-- A byte list of length `n` is worth less than `256 ^ n`. -/
theorem bytesToNat_lt (bytes : List UInt8) : bytesToNat bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [bytesToNat]
  | cons b rest ih =>
    -- The first byte is the most significant one.
    have h := foldl_bytesToNat rest b.toNat
    have hb : b.toNat < 256 := b.toNat_lt
    have hcons : bytesToNat (b :: rest) = b.toNat * 256 ^ rest.length + bytesToNat rest := by
      simpa [bytesToNat] using h
    rw [hcons, List.length_cons, Nat.pow_succ]
    nlinarith [Nat.zero_le (256 ^ rest.length)]

/-- Writing on `len` bytes gives exactly `len` bytes. -/
theorem natToBytes_length (len n : Nat) : (natToBytes len n).length = len := by
  induction len generalizing n with
  | zero => simp [natToBytes]
  | succ len ih => simp [natToBytes, ih]

/-- Writing `n` on `len` bytes and reading it back gives `n % 256 ^ len`. -/
theorem bytesToNat_natToBytes (len n : Nat) :
    bytesToNat (natToBytes len n) = n % 256 ^ len := by
  induction len generalizing n with
  | zero => simp [natToBytes, bytesToNat, Nat.mod_one]
  | succ len ih =>
    -- Split off the lowest byte, which is written last.
    rw [natToBytes, bytesToNat_append, ih, List.length_singleton]
    have : bytesToNat [UInt8.ofNat (n % 256)] = n % 256 := by
      simp [bytesToNat]
    rw [this]
    -- `n % 256^(len+1) = n % 256 + 256 * (n / 256 % 256^len)`.
    have h : n % 256 ^ (len + 1) = n % 256 + 256 * (n / 256 % 256 ^ len) := by
      rw [Nat.pow_succ']
      exact Nat.mod_mul
    rw [h, Nat.pow_one]
    ring

/-- A number below `256 ^ len` survives the round trip through `len` bytes. -/
theorem bytesToNat_natToBytes_of_lt {len n : Nat} (h : n < 256 ^ len) :
    bytesToNat (natToBytes len n) = n := by
  rw [bytesToNat_natToBytes, Nat.mod_eq_of_lt h]

/-- A window of the call data has exactly the `size` bytes asked for. -/
theorem bufferRead_length (data : ByteArray) (start size : Nat) :
    (bufferRead data start size).length = size := by
  simp [bufferRead]

/-- A read of `size` bytes is worth less than `256 ^ size`. -/
theorem readNat_lt (data : ByteArray) (start size : Nat) :
    readNat data start size < 256 ^ size := by
  have := bytesToNat_lt (bufferRead data start size)
  rwa [bufferRead_length] at this

/-- A read of no bytes is `0`. -/
theorem readNat_zero_size (data : ByteArray) (start : Nat) : readNat data start 0 = 0 := by
  simp [readNat, bufferRead, bytesToNat]

/-- Past the end of the call data every byte reads as zero. -/
theorem byteAt_of_size_le {data : ByteArray} {i : Nat} (h : data.size ≤ i) :
    byteAt data i = 0 := by
  simp [byteAt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

/-- Padding the call data with zero bytes on the right changes no byte. -/
theorem byteAt_append_zeros (data : ByteArray) (n i : Nat) :
    byteAt (data ++ ByteArray.mk (Array.replicate n 0)) i = byteAt data i := by
  by_cases h : i < data.size
  · simp [byteAt, ByteArray.data_append, Array.getD_eq_getD_getElem?,
      Array.getElem?_append_left h]
  · have h' : data.size ≤ i := Nat.le_of_not_lt h
    rw [byteAt_of_size_le h']
    -- Past the end of the data, the padding is zeros and beyond it nothing.
    simp only [byteAt, ByteArray.data_append, Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_append_right (by simpa using h'), Array.getElem?_replicate]
    split <;> simp

/-- A read depends only on the bytes it covers. -/
theorem readNat_congr {d₁ d₂ : ByteArray} {start size : Nat}
    (h : ∀ i, start ≤ i → i < start + size → byteAt d₁ i = byteAt d₂ i) :
    readNat d₁ start size = readNat d₂ start size := by
  unfold readNat bufferRead
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  exact h _ (by omega) (by omega)

/-- Padding the call data with zero bytes changes no read. -/
theorem readNat_append_zeros (data : ByteArray) (n start size : Nat) :
    readNat (data ++ ByteArray.mk (Array.replicate n 0)) start size = readNat data start size :=
  readNat_congr fun i _ _ => byteAt_append_zeros data n i

end EthLib.Precompiles.Modexp
