module

public import EthLib.Cryptography.Sphincs.Verify
public import EthLib.Cryptography.Sphincs.Errors

/-!
# leanSPHINCS byte encodings

The byte encodings of the public key and the signature.

Every field has a fixed size.

So an encoding is the fields concatenated, with no offsets and no length prefixes.

Decoding checks the total length, then reads each field at its fixed offset.

Source: [FIPS 205][fips205] §9.1 and §9.2, for the public key and the order of a signature.

leanSPHINCS puts each layer's counter before its chain values.

[fips205]: https://doi.org/10.6028/NIST.FIPS.205
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open Constants

/-! ## Encoding -/

/-- Encode a public key as 32 bytes, `PK.seed | PK.root`.

```text
    [ PK.seed: 16 | PK.root: 16 ]
```
-/
def encodePublicKey (pk : PublicKey) : ByteArray :=
  packBytes pk.pkSeed ++ packBytes pk.root

/-- The 176 bytes of one FORS tree's opening.

```text
    [ secret: 16 | 10 path nodes: 160 ]
```

The path nodes run from height 0 up to height 9.
-/
def treeOpeningBytes (opening : TreeOpening) : Vector UInt8 TREE_OPENING_SIZE :=
  opening.secret ++ opening.path.flatten

/-- Encode the openings of the 24 FORS trees, tree 0 first: 4224 bytes. -/
def encodeFors (openings : Vector TreeOpening FORS_TREES) : ByteArray :=
  -- Opening `kappa` lands at bytes `176 kappa` to `176 kappa + 175`.
  packBytes (openings.map treeOpeningBytes).flatten

/-- Encode one layer's signature: 1156 bytes on a lower layer, 1188 on the top one.

```text
    [ counter: 4 | 64 chain values: 1024 | h siblings: 16 h ]
```

- The counter is `BE_32(c)`, a big-endian 32-bit word.
- Chain values are in chain order.
- Siblings run from the leaf up to the root.
-/
def encodeLayerSignature {layer : Layer} (sig : LayerSignature layer) : ByteArray :=
  packBytes (toByte COUNTER_LEN sig.counter.toNat) ++ packDigests sig.chainValues
    ++ packDigests sig.path

/-- Encode a signature as 7740 bytes.

```text
    [ randomizer: 16 | FORS: 4224 | bottom: 1156 | middle: 1156 | top: 1188 ]
```

The layers run from the bottom up.
-/
def encodeSignature (sig : Signature) : ByteArray :=
  packBytes sig.randomizer ++ encodeFors sig.fors ++ encodeLayerSignature sig.bottom
    ++ encodeLayerSignature sig.middle ++ encodeLayerSignature sig.top

/-! ## Decoding -/

/-- Decode a public key from 32 bytes.

Length is the only check: every 32-byte string is a public key.
-/
def decodePublicKey (bytes : ByteArray) : Except SphincsError PublicKey :=
  if h : bytes.size = PUB_KEY_SIZE then
    -- The two fields sit at offsets 0 and 16.
    .ok { pkSeed := readBytes bytes 0 N (by simp only [h, PUB_KEY_SIZE]; omega)
          root := readBytes bytes N N (by simp only [h, PUB_KEY_SIZE]; omega) }
  else
    .error (.badPublicKeySize bytes.size)

/-- Read one FORS tree's opening from its 176 bytes: the secret, then the path at 16. -/
def treeOpeningOfBytes (bytes : Vector UInt8 TREE_OPENING_SIZE) : TreeOpening where
  secret := Vector.ofFn fun j => bytes[j.val]'(by
    have := j.isLt
    simp only [TREE_OPENING_SIZE] at *
    omega)
  path := splitDigests (Vector.ofFn fun j => bytes[N + j.val]'(by
    have := j.isLt
    simp only [TREE_OPENING_SIZE] at *
    omega))

/-- Read the 24 FORS openings from the 4224 bytes at an offset: tree `kappa` at `176 kappa`. -/
def decodeFors (bytes : ByteArray) (offset : Nat)
    (h : offset + FORS_TREES * TREE_OPENING_SIZE ≤ bytes.size) : Vector TreeOpening FORS_TREES :=
  (splitChunks (readBytes bytes offset (FORS_TREES * TREE_OPENING_SIZE) h)).map treeOpeningOfBytes

/-- Read one layer's signature from the bytes at an offset. -/
def decodeLayerSignature (layer : Layer) (bytes : ByteArray) (offset : Nat)
    (h : offset + layerSigSize layer.height ≤ bytes.size) : LayerSignature layer where
  -- The counter, then the chain values at 4, then the siblings at 1028.
  counter := UInt32.ofNat (toInt (readBytes bytes offset COUNTER_LEN
    (by simp only [layerSigSize] at h; omega)))
  chainValues := splitDigests (readBytes bytes (offset + COUNTER_LEN) (V * N)
    (by simp only [layerSigSize] at h; omega))
  path := splitDigests (readBytes bytes (offset + COUNTER_LEN + V * N) (layer.height * N)
    (by simp only [layerSigSize] at h; omega))

/-- The FORS openings follow the randomizer. -/
def forsOffset : Nat := RANDOMIZER_LEN

/-- The bottom layer follows the 24 FORS openings. -/
def bottomOffset : Nat := forsOffset + FORS_TREES * TREE_OPENING_SIZE

/-- The middle layer follows the bottom one. -/
def middleOffset : Nat := bottomOffset + layerSigSize LOWER_HEIGHT

/-- The top layer follows the middle one, and ends the signature. -/
def topOffset : Nat := middleOffset + layerSigSize LOWER_HEIGHT

/-- Decode a signature from 7740 bytes.

Length is the only check: every 7740-byte string decodes.

Decoding does not verify the signature.
-/
def decodeSignature (bytes : ByteArray) : Except SphincsError Signature :=
  if h : bytes.size = SIG_SIZE then
    -- The randomizer, then FORS at 16, the layers at 4240, 5396 and 6552.
    .ok { randomizer := readBytes bytes 0 RANDOMIZER_LEN (by simp only [h, SIG_SIZE]; decide)
          fors := decodeFors bytes forsOffset (by simp only [h, SIG_SIZE, forsOffset]; decide)
          bottom := decodeLayerSignature .bottom bytes bottomOffset
            (by simp only [h, SIG_SIZE, bottomOffset, forsOffset, Layer.height]; decide)
          middle := decodeLayerSignature .middle bytes middleOffset
            (by
              simp only [h, SIG_SIZE, middleOffset, bottomOffset, forsOffset, Layer.height]
              decide)
          top := decodeLayerSignature .top bytes topOffset
            (by simp only [h, SIG_SIZE, topOffset, middleOffset, bottomOffset, forsOffset,
              Layer.height]; decide) }
  else
    .error (.badSignatureSize bytes.size)

end EthLib.Cryptography.Sphincs
