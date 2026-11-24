module

public import EthLib.Cryptography.Xmss.Verify
public import EthLib.Cryptography.Xmss.Errors

/-!
# leanXMSS byte encodings

The public key and the signature as bytes: fixed-size fields, concatenated with no offsets or length prefixes.

Source: the leanXMSS specification draft, section "The scheme", paragraph "Serialization".
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open Constants

/-! ## Encoding -/

/-- Encode a public key as 32 bytes. -/
def encodePublicKey (pk : PublicKey) : ByteArray :=
  -- The root, then the public parameter: 16 bytes each.
  packBytes pk.root.bytes ++ packBytes pk.publicParam.bytes

/-- Encode one layer's signature as 1200 bytes. -/
def encodeLayerSignature (sig : LayerSignature) : ByteArray :=
  -- The randomizer: 16 bytes.
  packBytes sig.randomizer.bytes
    -- The 58 chain values, in chain order: 928 bytes.
    ++ packDigests sig.chainValues
    -- The 16 siblings, from the leaf up to the root: 256 bytes.
    ++ packDigests sig.path

/-- Encode a signature as 2404 bytes. -/
def encodeSignature (sig : Signature) : ByteArray :=
  -- The leaf index, as a little-endian 32-bit word: 4 bytes.
  packBytes (uintToBytes LEAF_INDEX_SIZE sig.leafIndex.toNat)
    -- The bottom layer's signature: 1200 bytes.
    ++ encodeLayerSignature sig.bottom
    -- The top layer's signature: 1200 bytes.
    ++ encodeLayerSignature sig.top

/-! ## Decoding -/

/-- Decode a public key from 32 bytes. -/
def decodePublicKey (bytes : ByteArray) : Except XmssError PublicKey :=
  -- Length is the only check: every 32-byte string is a public key.
  if bytes.size = PUB_KEY_SIZE then
    -- The root at offset 0, then the public parameter at 16.
    .ok { root := Hash.Keccak.Lanes2.read bytes 0
          publicParam := Hash.Keccak.Lanes2.read bytes DIGEST_LEN }
  else
    .error (.badPublicKeySize bytes.size)

/-- Read one layer's signature from the 1200 bytes at an offset.

The buffer must hold them; past its end, the bytes would read as zero. -/
def decodeLayerSignature (bytes : ByteArray) (offset : Nat)
    (_h : offset + LAYER_SIG_SIZE ≤ bytes.size) : LayerSignature where
  -- The randomizer, at the offset.
  randomizer := Hash.Keccak.Lanes2.read bytes offset
  -- The 58 chain values, 16 bytes after it.
  chainValues := splitDigests V bytes (offset + RANDOMIZER_LEN)
  -- The 16 siblings, 944 bytes after it.
  path := splitDigests LAYER_HEIGHT bytes (offset + RANDOMIZER_LEN + V * DIGEST_LEN)

/-- Read the leaf index from the first 4 bytes of a buffer, as a little-endian word. -/
def decodeLeafIndex (bytes : ByteArray) (h : LEAF_INDEX_SIZE ≤ bytes.size) : LeafIndex :=
  -- Four bytes hold at most `2^32 - 1`, so the conversion drops nothing.
  UInt32.ofNat (bytesToUint (readBytes bytes 0 LEAF_INDEX_SIZE (by omega)))

/-- Decode a signature from 2404 bytes, without verifying it. -/
def decodeSignature (bytes : ByteArray) : Except XmssError Signature :=
  -- Length is the only check: every 2404-byte string decodes.
  if h : bytes.size = SIG_SIZE then
    .ok {
      -- The leaf index, at offset 0.
      leafIndex := decodeLeafIndex bytes (by simp only [h, SIG_SIZE]; omega)
      -- The bottom layer, at offset 4.
      bottom := decodeLayerSignature bytes LEAF_INDEX_SIZE
        (by simp only [h, SIG_SIZE]; omega)
      -- The top layer, at offset 1204.
      top := decodeLayerSignature bytes (LEAF_INDEX_SIZE + LAYER_SIG_SIZE)
        (by simp only [h, SIG_SIZE]; omega) }
  else
    .error (.badSignatureSize bytes.size)

/-- The leaf index that a 2404-byte signature claims, read without verifying the signature.

A caller can require a given leaf before verifying; a proof of possession requires leaf 0. -/
def signatureIndex (bytes : ByteArray) : Except XmssError LeafIndex :=
  -- The whole signature must be there, as for decoding, so a truncated one is rejected.
  if h : bytes.size = SIG_SIZE then
    -- Only the first 4 bytes are read.
    .ok (decodeLeafIndex bytes (by simp only [h, SIG_SIZE]; omega))
  else
    .error (.badSignatureSize bytes.size)

end EthLib.Cryptography.Xmss
