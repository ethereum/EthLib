module

public import EthLib.Cryptography.Hash.Sha256

/-!
# HMAC-SHA-256

HMAC-SHA-256, as [RFC 2104 §2](https://www.rfc-editor.org/rfc/rfc2104#section-2) defines it.

The key is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Hmac

/-- The inner pad byte `ipad`. -/
def IPAD : UInt8 := 0x36

/-- The outer pad byte `opad`. -/
def OPAD : UInt8 := 0x5c

/-- The key as one block of `B` bytes, where `B` is the block size of SHA-256. -/
def blockKey (key : ByteArray) : ByteArray :=
  -- A key longer than `B` bytes is first hashed with `H`, to `L` bytes.
  let short := if key.size > Sha256.BLOCK_SIZE_BYTES then Sha256.hash key else key
  -- Step (1): append zeros to the end of `K` to create a `B` byte string.
  short ++ ⟨Array.replicate (Sha256.BLOCK_SIZE_BYTES - short.size) 0⟩

/-- Each byte of a block XORed with one pad byte. -/
def xorPad (block : ByteArray) (pad : UInt8) : ByteArray :=
  ⟨block.data.map (· ^^^ pad)⟩

/--
HMAC-SHA-256 of a message under a secret key: `H(K ^ opad, H(K ^ ipad, text))`.

The key is secret, and this function makes no constant-time claim.
-/
def hmac (key message : ByteArray) : ByteArray :=
  -- Step (1): `K` as a `B` byte string.
  let k := blockKey key
  -- Steps (2) to (4): `H(K XOR ipad, text)`, the inner hash.
  --
  -- Steps (5) to (7): `H(K XOR opad, ...)` of the inner hash, the output.
  Sha256.hash (xorPad k OPAD ++ Sha256.hash (xorPad k IPAD ++ message))

/--
HMAC-SHA-256 of a message under a secret key, as its 32 bytes.

The key is secret, and this function makes no constant-time claim.
-/
def hmac32 (key message : ByteArray) : Vector UInt8 32 :=
  -- The tag is the output of SHA-256, which has 32 bytes.
  ⟨(hmac key message).data, (Sha256.hash32 _).size_toArray⟩

end EthLib.Cryptography.Hash.Hmac
