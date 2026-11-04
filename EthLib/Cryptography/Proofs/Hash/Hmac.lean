module

public import EthLib.Cryptography.Proofs.Hash.Sha256
public import EthLib.Cryptography.Hash.Hmac

/-!
# Proofs: HMAC-SHA-256

Every HMAC-SHA-256 tag is 32 bytes long.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Hmac

/-- Every tag is 32 bytes long, whatever the key and the message. -/
@[simp] theorem hmac_size (key message : ByteArray) : (hmac key message).size = 32 :=
  Sha256.hash_size _

end EthLib.Cryptography.Hash.Hmac
