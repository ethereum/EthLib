module

public import EthLib.Cryptography.Proofs.Hash.Sha256
public import EthLib.Cryptography.Hash.ConcatKdf

/-!
# Proofs: the Concatenation KDF

A successful derivation has exactly the requested length.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.ConcatKdf

/-- The blocks of the derivation are 32 bytes each. -/
theorem blocks_size (z fixedInfo : ByteArray) (i count : Nat) :
    (blocks z fixedInfo i count).size = HASH_LEN * count := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
    simp only [blocks, ByteArray.size_append, Sha256.hash_size, ih, HASH_LEN]
    omega

/-- A successful derivation has exactly the requested length. -/
theorem concatKdf_size {z fixedInfo key : ByteArray} {length : Nat}
    (h : concatKdf z fixedInfo length = .ok key) : key.size = length := by
  unfold concatKdf at h
  by_cases empty : length = 0
  · simp [empty] at h
  by_cases long : 2 ^ 32 - 1 < (length + HASH_LEN - 1) / HASH_LEN
  · simp [empty, long] at h
  by_cases input : 2 ^ 61 ≤ 4 + z.size + fixedInfo.size
  · simp [empty, long, input] at h
  simp only [empty, long, input, ite_false] at h
  -- The blocks cover the output, so the extraction keeps the requested length.
  obtain rfl := Except.ok.inj h
  simp only [ByteArray.size_extract, blocks_size, HASH_LEN]
  omega

end EthLib.Cryptography.Hash.ConcatKdf
