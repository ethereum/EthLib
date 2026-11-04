module

public import EthLib.Cryptography.Ethash.Hashimoto
public import EthLib.Cryptography.Proofs.Ethash.Cache

/-!
# Proofs: the Ethash proof-of-work function

The mix digest and the result are 32 bytes each, whatever the inputs.

The official vectors of the function are in the Python suite, through the bindings.
-/

@[expose] public section

namespace EthLib.Cryptography.Ethash

/-- The mix digest is 32 bytes: 8 compressed words. -/
theorem size_mixDigest (datasetSize : Nat) (cache : Array Item) (headerHash nonce : ByteArray) :
    (hashimotoLight datasetSize cache headerHash nonce).mixDigest.size = 32 :=
  size_bytesOfWords _

/-- The result is 32 bytes: a Keccak-256 digest. -/
theorem size_result (datasetSize : Nat) (cache : Array Item) (headerHash nonce : ByteArray) :
    (hashimotoLight datasetSize cache headerHash nonce).result.size = 32 := by
  simp [hashimotoLight, ByteArray.size, Hash.Keccak.DIGEST_LEN]

end EthLib.Cryptography.Ethash
