import EthLib.Cryptography.Xmss.Verify
import EthLib.Cryptography.Xmss.Errors

/-!
# `Xmss.Serialization`

The byte encodings of the public key and the signature.

Every field has a fixed size.

So an encoding is the fields concatenated, with no offsets and no length prefixes.

Decoding checks the total length, then reads each field at its fixed offset.

Source: the leanXMSS specification draft, section "The scheme", paragraph "Serialization".
-/

namespace EthLib.Cryptography.Xmss

open Constants

/-! ## Encoding -/

/-- Encode a public key as 32 bytes.

```text
    [ root: 16 | public parameter: 16 ]
```
-/
def encodePublicKey (pk : PublicKey) : ByteArray :=
  packBytes pk.root ++ packBytes pk.publicParam

/-- Encode one layer's signature as 1200 bytes.

```text
    [ randomizer: 16 | 58 chain values: 928 | 16 siblings: 256 ]
```

- Chain values are in chain order.
- Siblings run from the leaf up to the root.
-/
def encodeLayerSignature (sig : LayerSignature) : ByteArray :=
  packBytes sig.randomizer ++ packDigests sig.chainValues ++ packDigests sig.path

/-- Encode a signature as 2404 bytes.

```text
    [ leaf index: 4 | bottom layer: 1200 | top layer: 1200 ]
```

The leaf index is a little-endian 32-bit word.
-/
def encodeSignature (sig : Signature) : ByteArray :=
  packBytes (littleEndian LEAF_INDEX_SIZE sig.leafIndex.toNat)
    ++ encodeLayerSignature sig.bottom ++ encodeLayerSignature sig.top

/-! ## Decoding -/

/-- Decode a public key from 32 bytes.

Length is the only check: every 32-byte string is a public key.
-/
def decodePublicKey (bytes : ByteArray) : Except XmssError PublicKey :=
  if h : bytes.size = PUB_KEY_SIZE then
    -- The two fields sit at offsets 0 and 16.
    .ok { root := readBytes bytes 0 DIGEST_LEN (by simp only [h, PUB_KEY_SIZE]; omega)
          publicParam := readBytes bytes DIGEST_LEN PUBLIC_PARAM_LEN
            (by simp only [h, PUB_KEY_SIZE]; omega) }
  else
    .error (.badPublicKeySize bytes.size)

/-- Read one layer's signature from the 1200 bytes at an offset. -/
def decodeLayerSignature (bytes : ByteArray) (offset : Nat)
    (h : offset + LAYER_SIG_SIZE ≤ bytes.size) : LayerSignature where
  -- The randomizer, then the chain values at 16, then the siblings at 944.
  randomizer := readBytes bytes offset RANDOMIZER_LEN
    (by simp only [LAYER_SIG_SIZE] at h; omega)
  chainValues := splitDigests (readBytes bytes (offset + RANDOMIZER_LEN) (V * DIGEST_LEN)
    (by simp only [LAYER_SIG_SIZE] at h; omega))
  path := splitDigests
    (readBytes bytes (offset + RANDOMIZER_LEN + V * DIGEST_LEN) (LAYER_HEIGHT * DIGEST_LEN)
      (by simp only [LAYER_SIG_SIZE] at h; omega))

/-- Decode a signature from 2404 bytes.

Length is the only check: every 2404-byte string decodes.

Decoding does not verify the signature.
-/
def decodeSignature (bytes : ByteArray) : Except XmssError Signature :=
  if h : bytes.size = SIG_SIZE then
    -- The leaf index, then the bottom layer at 4, then the top layer at 1204.
    .ok { leafIndex := UInt32.ofNat (fromLittleEndian
            (readBytes bytes 0 LEAF_INDEX_SIZE (by simp only [h, SIG_SIZE]; omega)))
          bottom := decodeLayerSignature bytes LEAF_INDEX_SIZE
            (by simp only [h, SIG_SIZE]; omega)
          top := decodeLayerSignature bytes (LEAF_INDEX_SIZE + LAYER_SIG_SIZE)
            (by simp only [h, SIG_SIZE]; omega) }
  else
    .error (.badSignatureSize bytes.size)

end EthLib.Cryptography.Xmss
