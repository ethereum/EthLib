module

public import EthLib.Base.Proofs.LittleEndian
public import EthLib.Serialization.Ssz.Codec.Deserialize

/-!
# Proofs: integers as bytes

An integer is written and read one byte at a time, the low byte first.

Each step peels one byte off, and leaves the same task one byte narrower.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- An integer of no bytes is written as nothing. -/
theorem uintBytes_zero (value : Nat) : uintBytes 0 value = #[] := rfl

/-- An integer is written as its low byte, then its quotient by 256 one byte narrower. -/
theorem uintBytes_succ (width value : Nat) :
    uintBytes (width + 1) value
      = #[UInt8.ofNat (value % 256)] ++ uintBytes width (value / 256) := by
  -- A byte keeps only the value modulo 256 anyway.
  rw [uintBytes, uintBytes, Base.uintToBytes_toArray_succ, ← UInt8.ofNat_mod_size (x := value)]

/-- No bytes read as the integer zero. -/
theorem readUint_zero (data : Bytes) (start : Nat) : readUint data start 0 = 0 := rfl

/-- An integer is read as its low byte, plus 256 times the integer the next bytes hold. -/
theorem readUint_succ (data : Bytes) (start width : Nat) :
    readUint data start (width + 1)
      = (data[start]?.getD 0).toNat + 256 * readUint data (start + 1) width := by
  simp [readUint, Base.bytesToUint_ofFn_succ, Nat.add_assoc, Nat.add_comm 1]

end EthLib.Serialization.Ssz
