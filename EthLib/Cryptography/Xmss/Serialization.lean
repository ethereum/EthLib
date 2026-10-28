import EthLib.Cryptography.Xmss.Verify
import EthLib.Cryptography.Xmss.Errors

/-!
# `Xmss.Serialization`

The byte encodings of the public key and the signature.

Every field has a fixed size.

So an encoding is the fields concatenated, with no offsets and no length prefixes.

Decoding checks the total length, then reads each field at its fixed offset.
-/

namespace EthLib.Cryptography.Xmss

open Constants

/-! ## Encoding -/

/-- Encode a public key as 32 bytes.

```text
    [ Merkle root: 16 | public parameter: 16 ]
```
-/
def encodePublicKey (pk : PublicKey) : ByteArray :=
  packBytes pk.merkleRoot ++ packBytes pk.publicParam

/-- Encode a signature as 1208 bytes.

```text
    [ randomizer: 24 | 42 chain values: 672 | 32 siblings: 512 ]
```

- The randomizer comes first, as in the paper's signature tuple.
- Chain values are in chain order.
- Siblings run from the leaf up to the root.
-/
def encodeSignature (sig : Signature) : ByteArray :=
  packBytes sig.randomness ++ packBytes sig.chainElements.flatten
    ++ packBytes sig.merklePath.flatten

/-! ## Decoding -/

/-- Cut a byte field into consecutive 16-byte digests. -/
def splitDigests {n : Nat} (bytes : Vector UInt8 (n * DIGEST_LEN)) : Vector Digest n :=
  -- Byte j of digest i sits at position 16 i + j of the field.
  Vector.ofFn fun i => Vector.ofFn fun j => bytes[i.val * DIGEST_LEN + j.val]'(by
    -- With i < n and j < 16, that position is below 16 n.
    have hi := i.isLt
    have hj := j.isLt
    simp only [DIGEST_LEN] at *
    omega)

/-- Decode a public key from 32 bytes.

Length is the only check: every 32-byte string is a public key.
-/
def decodePublicKey (bytes : ByteArray) : Except XmssError PublicKey :=
  if h : bytes.size = PUB_KEY_SIZE then
    -- The two fields sit at offsets 0 and 16.
    .ok { merkleRoot := readBytes bytes 0 DIGEST_LEN (by simp only [h, PUB_KEY_SIZE]; omega)
          publicParam := readBytes bytes DIGEST_LEN PUBLIC_PARAM_LEN
            (by simp only [h, PUB_KEY_SIZE]; omega) }
  else
    .error (.badPublicKeySize bytes.size)

/-- Decode a signature from 1208 bytes.

Length is the only check: every 1208-byte string decodes.

Decoding does not verify the signature.
-/
def decodeSignature (bytes : ByteArray) : Except XmssError Signature :=
  if h : bytes.size = SIG_SIZE then
    -- The three fields sit at offsets 0, 24 and 696.
    .ok { randomness := readBytes bytes 0 RANDOMNESS_LEN
            (by simp only [h, SIG_SIZE, WOTS_SIG_SIZE]; omega)
          chainElements := splitDigests
            (readBytes bytes RANDOMNESS_LEN (V * DIGEST_LEN)
              (by simp only [h, SIG_SIZE, WOTS_SIG_SIZE]; omega))
          merklePath := splitDigests
            (readBytes bytes WOTS_SIG_SIZE (LOG_LIFETIME * DIGEST_LEN)
              (by simp only [h, SIG_SIZE]; omega)) }
  else
    .error (.badSignatureSize bytes.size)

end EthLib.Cryptography.Xmss
