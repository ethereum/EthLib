module

public import EthLib.Precompiles.Ripemd160
public import EthLib.Cryptography.Proofs.Hash.Ripemd160

/-!
# Proofs: `Ripemd160`

The output of the precompile at address `0x03` is 32 bytes: twelve zero bytes, then the RIPEMD-160 digest.
-/

@[expose] public section

namespace EthLib.Precompiles.Ripemd160

open EthLib.Cryptography.Hash

/-- The padding is twelve bytes. -/
private theorem padding_size :
    (ByteArray.mk (Array.replicate (OUTPUT_BYTES - DIGEST_BYTES) 0)).size = 12 := by
  simp [ByteArray.size, OUTPUT_BYTES, DIGEST_BYTES]

/-- The digest is 20 bytes. -/
private theorem digest_size (data : ByteArray) : (Cryptography.Hash.ripemd160 data).size = 20 :=
  Ripemd160.hash_size data

/-- The output is 32 bytes, whatever the call data. -/
@[simp] theorem ripemd160_size (data : ByteArray) : (ripemd160 data).size = OUTPUT_BYTES := by
  unfold ripemd160
  rw [ByteArray.size_append, padding_size, digest_size]
  rfl

/-- The first twelve bytes are zero. -/
theorem ripemd160_leading_zeros (data : ByteArray) (i : Nat) (within : i < 12) :
    (ripemd160 data)[i]'(by rw [ripemd160_size]; simp [OUTPUT_BYTES]; omega) = 0 := by
  -- Name the bound, so it unfolds together with the output.
  have bound : i < (ripemd160 data).size := by rw [ripemd160_size]; simp [OUTPUT_BYTES]; omega
  change (ripemd160 data)[i]'bound = 0
  unfold EthLib.Precompiles.Ripemd160.ripemd160 at bound ⊢
  -- The zeros are the left part of the concatenation.
  rw [ByteArray.getElem_append_left (by rw [padding_size]; exact within)]
  simp [ByteArray.getElem_eq_getElem_data]

/-- The last twenty bytes are the RIPEMD-160 digest. -/
theorem ripemd160_digest (data : ByteArray) (i : Nat) (within : i < 20) :
    (ripemd160 data)[12 + i]'(by rw [ripemd160_size]; simp [OUTPUT_BYTES]; omega) =
      (Cryptography.Hash.ripemd160 data)[i]'(by rw [digest_size]; omega) := by
  -- Unfold the output with simp, which carries the index bound along.
  simp only [EthLib.Precompiles.Ripemd160.ripemd160]
  -- The digest is the right part of the concatenation, after the twelve zeros.
  rw [ByteArray.getElem_append_right (by rw [padding_size]; omega)]
  simp [padding_size]

/-- Known answer: the call data `"abc"` gives twelve zero bytes, then the digest the paper's vector lists. -/
theorem ripemd160_abc :
    ripemd160 (Ripemd160.ascii "abc") =
      Ripemd160.hexBytes "0000000000000000000000008eb208f7e05d987a9b044a8e98c6b087f15a0bfc" := by
  decide +kernel

/-- Known answer: empty call data gives twelve zero bytes, then the digest of the empty string. -/
theorem ripemd160_empty :
    ripemd160 ByteArray.empty =
      Ripemd160.hexBytes "0000000000000000000000009c1185a5c5e9fc54612808977ee8f548b2258d31" := by
  decide +kernel

end EthLib.Precompiles.Ripemd160
