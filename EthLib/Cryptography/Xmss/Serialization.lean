module

public import EthLib.Cryptography.Xmss.Verify
public import EthLib.Cryptography.Xmss.Errors

/-!
# leanXMSS byte encodings

The byte encodings of the public key and the signature.

Every field has a fixed size.

So an encoding is the fields concatenated, with no offsets and no length prefixes.

Decoding checks the total length, then reads each field at its fixed offset.

Source: the leanXMSS specification draft, section "The scheme", paragraph "Serialization".
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open Constants

/-! ## Encoding -/

/-- Encode a public key as 32 bytes: the 16-byte root, then the 16-byte public parameter. -/
def encodePublicKey (pk : PublicKey) : ByteArray :=
  packBytes pk.root.bytes ++ packBytes pk.publicParam.bytes

/-- Encode one layer's signature as 1200 bytes.

The bytes are the randomizer (16), the 58 chain values (928), then the 16 siblings (256).

- Chain values are in chain order.
- Siblings run from the leaf up to the root.
-/
def encodeLayerSignature (sig : LayerSignature) : ByteArray :=
  -- `rho | y_0 | ... | y_{v-1} | pi_0 | ... | pi_{h-1}`, `16 (1 + v + h) = 1200` bytes.
  packBytes sig.randomizer.bytes ++ packDigests sig.chainValues ++ packDigests sig.path

/-- Encode a signature as 2404 bytes.

The bytes are the leaf index (4), the bottom layer (1200), then the top layer (1200).

The leaf index is a little-endian 32-bit word.
-/
def encodeSignature (sig : Signature) : ByteArray :=
  -- `LE_32(idx)`, the bottom layer's signature, then the top layer's: `4 + 1200 + 1200`.
  packBytes (uintToBytes LEAF_INDEX_SIZE sig.leafIndex.toNat)
    ++ encodeLayerSignature sig.bottom ++ encodeLayerSignature sig.top

/-! ## Decoding -/

/-- Decode a public key from 32 bytes.

Length is the only check: every 32-byte string is a public key.
-/
def decodePublicKey (bytes : ByteArray) : Except XmssError PublicKey :=
  if bytes.size = PUB_KEY_SIZE then
    -- The two fields sit at offsets 0 and 16.
    .ok { root := Hash.Keccak.Lanes2.read bytes 0
          publicParam := Hash.Keccak.Lanes2.read bytes DIGEST_LEN }
  else
    .error (.badPublicKeySize bytes.size)

/-- Read one layer's signature from the 1200 bytes at an offset, which the buffer holds.

The caller proves that the buffer holds them; past its end, the bytes would read as zero. -/
def decodeLayerSignature (bytes : ByteArray) (offset : Nat)
    (_h : offset + LAYER_SIG_SIZE ≤ bytes.size) : LayerSignature where
  -- The randomizer, then the chain values at 16, then the siblings at 944.
  randomizer := Hash.Keccak.Lanes2.read bytes offset
  chainValues := splitDigests V bytes (offset + RANDOMIZER_LEN)
  path := splitDigests LAYER_HEIGHT bytes (offset + RANDOMIZER_LEN + V * DIGEST_LEN)

/-- Read the leaf index from the first 4 bytes of a buffer, as a little-endian word. -/
def decodeLeafIndex (bytes : ByteArray) (h : LEAF_INDEX_SIZE ≤ bytes.size) : LeafIndex :=
  -- Four bytes hold at most `2^32 - 1`, so the conversion drops nothing.
  UInt32.ofNat (bytesToUint (readBytes bytes 0 LEAF_INDEX_SIZE (by omega)))

/-- Decode a signature from 2404 bytes.

Length is the only check: every 2404-byte string decodes.

Decoding does not verify the signature.
-/
def decodeSignature (bytes : ByteArray) : Except XmssError Signature :=
  if h : bytes.size = SIG_SIZE then
    -- The leaf index, then the bottom layer at 4, then the top layer at 1204.
    .ok { leafIndex := decodeLeafIndex bytes (by simp only [h, SIG_SIZE]; omega)
          bottom := decodeLayerSignature bytes LEAF_INDEX_SIZE
            (by simp only [h, SIG_SIZE]; omega)
          top := decodeLayerSignature bytes (LEAF_INDEX_SIZE + LAYER_SIG_SIZE)
            (by simp only [h, SIG_SIZE]; omega) }
  else
    .error (.badSignatureSize bytes.size)

/-- The leaf index a 2404-byte signature carries.

It reads only the first 4 bytes.

It does not verify the signature, so the index is only what the signer claims.

A caller can use it to require a given leaf before verifying.

For example, a proof of possession requires leaf 0.
-/
def signatureIndex (bytes : ByteArray) : Except XmssError LeafIndex :=
  -- The whole signature must be there, as for decoding, so a truncated one is rejected.
  if h : bytes.size = SIG_SIZE then
    .ok (decodeLeafIndex bytes (by simp only [h, SIG_SIZE]; omega))
  else
    .error (.badSignatureSize bytes.size)

end EthLib.Cryptography.Xmss
