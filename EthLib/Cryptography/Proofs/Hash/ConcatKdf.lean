module

public import EthLib.Cryptography.Proofs.Hash.Sha256
public import EthLib.Cryptography.Hash.ConcatKdf

/-!
# Proofs: the Concatenation KDF

A successful derivation has exactly the requested length.

The kernel checks [RFC 7518](https://www.rfc-editor.org/rfc/rfc7518#appendix-C) Appendix C.
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

/-- A result of the derivation can be compared with an expected one. -/
private instance : DecidableEq (Except ConcatKdfError ByteArray) := fun
  | .ok a, .ok b => if h : a = b then .isTrue (h ▸ rfl) else .isFalse (by simp [h])
  | .error a, .error b => if h : a = b then .isTrue (h ▸ rfl) else .isFalse (by simp [h])
  | .ok _, .error _ => .isFalse (by simp)
  | .error _, .ok _ => .isFalse (by simp)

/--
RFC 7518 Appendix C: the 128-bit key of an ECDH-ES agreement for `A128GCM`.

The other information is `AlgorithmID | PartyUInfo | PartyVInfo | SuppPubInfo`.

Its key is the first 16 bytes of one block.
-/
theorem concatKdf_rfc7518 :
    concatKdf
      ⟨#[158, 86, 217, 29, 129, 113, 53, 211, 114, 131, 66, 131, 191, 132, 38, 156,
        251, 49, 110, 163, 218, 128, 106, 72, 246, 218, 167, 121, 140, 254, 144, 196]⟩
      ⟨#[0, 0, 0, 7, 65, 49, 50, 56, 71, 67, 77, 0, 0, 0, 5, 65, 108, 105, 99, 101,
        0, 0, 0, 3, 66, 111, 98, 0, 0, 0, 128]⟩ 16
      = .ok ⟨#[86, 170, 141, 234, 248, 35, 109, 32, 92, 34, 40, 205, 113, 167, 16, 26]⟩ := by
  decide +kernel

end EthLib.Cryptography.Hash.ConcatKdf
