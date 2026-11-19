module

public import EthLib.Serialization.Proofs.Ssz.Packing
public import EthLib.Serialization.Ssz.Codec.Deserialize

/-!
# Proofs: integers as bytes

An integer is written and read one byte at a time, the low byte first.

Each step peels one byte off, and leaves the same task one byte narrower.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- No bytes read as the integer zero. -/
theorem readUint_zero (data : Bytes) (start : Nat) : readUint data start 0 = 0 := rfl

/-- An integer is read as its low byte, plus 256 times the integer the next bytes hold. -/
theorem readUint_succ (data : Bytes) (start width : Nat) :
    readUint data start (width + 1)
      = (data[start]?.getD 0).toNat + 256 * readUint data (start + 1) width := by
  simp [readUint, Base.bytesToUint_ofFn_succ, Nat.add_assoc, Nat.add_comm 1]

end EthLib.Serialization.Ssz
