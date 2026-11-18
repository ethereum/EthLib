module

public import EthLib.Cryptography.Hash.Keccak

/-!
# Proofs: Keccak-512

Every Keccak-512 digest is 64 bytes.

The Keccak-512 test vectors are in the Python suite, through the bindings.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

/-- Every digest is 64 bytes, whatever the message. -/
theorem size_keccak512 (msg : ByteArray) : (keccak512 msg).toArray.size = DIGEST_LEN_512 :=
  (keccak512 msg).size_toArray

end EthLib.Cryptography.Hash.Keccak
