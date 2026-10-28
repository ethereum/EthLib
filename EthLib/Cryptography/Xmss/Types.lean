import EthLib.Cryptography.Xmss.Constants

/-!
# `Xmss.Types`

Fixed-size byte objects, with the length carried in the type.

- Indexing is total, so reading a field needs no bounds proof and cannot panic.
- Sizes stop being side conditions dragged through proofs.
- These are abbreviations, so equal-length objects stay interchangeable.

Untyped bytes survive at two edges only: hash inputs and serialization.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## Objects -/

/-- A hash value.

Chain values, Merkle nodes and leaves are all digests. -/
abbrev Digest := Vector UInt8 DIGEST_LEN

/-- The public parameter `P`, hashed into every call.

It makes one key's hash functions independent of another's. -/
abbrev PublicParam := Vector UInt8 PUBLIC_PARAM_LEN

/-- The address `A` hashed after the public parameter.

It names the call site of one hash inside one key. -/
abbrev Address := Vector UInt8 ADDRESS_LEN

/-- The randomizer `rho` under which a one-time key's digest is a codeword.

It is part of the signature. -/
abbrev Randomizer := Vector UInt8 RANDOMIZER_LEN

/-- The message to sign: a 256-bit message hash, not a document. -/
abbrev Message := Vector UInt8 MESSAGE_LEN

/-- A 32-byte seed.

The secret key is one, and the scheme's seed `S` derived from it is another. -/
abbrev Seed := Vector UInt8 SEED_LEN

/-- A leaf index, below `2^32`.

- Its top 16 bits name the bottom tree.
- Its low 16 bits name the leaf inside that tree.

Each leaf index may sign only one message, ever. -/
abbrev LeafIndex := UInt32

/-- One of the two layers of trees. -/
inductive Layer where
  /-- Layer 0: `2^16` trees, whose keys sign messages. -/
  | bottom
  /-- Layer 1: one tree, whose keys sign the roots of the bottom trees. -/
  | top
  deriving DecidableEq, Repr

/-- The layer's number `l` in the specification: 0 at the bottom, 1 at the top. -/
def Layer.toNat : Layer → Nat
  | .bottom => 0
  | .top => 1

/-! ## Little-endian integers -/

/-- `LE_{8k}(z)`: the `k` low bytes of `z`, least significant first.

Example: `littleEndian 2 0x1234 = #v[0x34, 0x12]`. -/
def littleEndian (k z : Nat) : Vector UInt8 k :=
  -- Byte `i` holds bits `8i` to `8i + 7`.
  Vector.ofFn fun i => UInt8.ofNat (z / 256 ^ i.val)

/-- `LE^-1`: the integer whose little-endian bytes these are.

Example: `fromLittleEndian #v[0x34, 0x12] = 0x1234`. -/
def fromLittleEndian {k : Nat} (bytes : Vector UInt8 k) : Nat :=
  -- Horner's rule from the most significant byte down.
  bytes.toArray.foldr (fun byte acc => byte.toNat + 256 * acc) 0

/-! ## Crossing to and from untyped bytes -/

/-- The bytes of a fixed-size object, in order.

Examples:
* `(packBytes #v[10, 20]).data = #[10, 20]`
* `(packBytes #v[10, 20]).size = 2`
-/
def packBytes {n : Nat} (v : Vector UInt8 n) : ByteArray :=
  -- The length invariant is discarded, not checked: every object has one.
  ⟨v.toArray⟩

/-- The bytes of a list of digests, in order. -/
def packDigests {n : Nat} (ds : Vector Digest n) : ByteArray :=
  -- Digest `i` lands at bytes `16i` to `16i + 15`.
  packBytes ds.flatten

/-- Read the `n` bytes of a buffer that start at an offset.

The caller proves the buffer has room, so the read needs no fallback byte.

Example, with `b = ByteArray.mk #[10, 20, 30, 40]`:
* `readBytes b 1 2 _ = #v[20, 30]`
-/
def readBytes (b : ByteArray) (offset n : Nat) (h : offset + n ≤ b.size) :
    Vector UInt8 n :=
  -- Every index below the object's length lands inside the buffer.
  Vector.ofFn fun i => b.data[offset + i.val]'(by
    simp only [ByteArray.size] at h
    omega)

/-- Read a fixed-size object out of a buffer at an offset.

Returns nothing when the buffer has no room for the object.

Never pads and never truncates.

Examples, with `b = ByteArray.mk #[10, 20, 30, 40]`:
* `unpackBytes? 4 b = some #v[10, 20, 30, 40]`
* `unpackBytes? 2 b 1 = some #v[20, 30]`
* `unpackBytes? 2 b 3 = none`
-/
def unpackBytes? (n : Nat) (b : ByteArray) (offset : Nat := 0) :
    Option (Vector UInt8 n) :=
  -- The guard is the whole validation: a buffer without room is rejected.
  if h : offset + n ≤ b.size then some (readBytes b offset n h) else none

/-- Cut a byte field into consecutive 16-byte digests. -/
def splitDigests {n : Nat} (bytes : Vector UInt8 (n * DIGEST_LEN)) : Vector Digest n :=
  -- Byte j of digest i sits at position 16 i + j of the field.
  Vector.ofFn fun i => Vector.ofFn fun j => bytes[i.val * DIGEST_LEN + j.val]'(by
    -- With i < n and j < 16, that position is below 16 n.
    have hi := i.isLt
    have hj := j.isLt
    simp only [DIGEST_LEN] at *
    omega)

end EthLib.Cryptography.Xmss
