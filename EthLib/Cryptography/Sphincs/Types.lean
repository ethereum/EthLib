module

public import EthLib.Cryptography.Sphincs.Constants
public import EthLib.Base.BigEndian
public import EthLib.Cryptography.HashSig

/-!
# leanSPHINCS types

Fixed-size byte objects, with the length carried in the type, and the layers of the hypertree.

- Indexing is total, so reading a field needs no bounds proof and cannot panic.
- Sizes stop being side conditions dragged through proofs.
- The types are abbreviations, so equal-length objects stay interchangeable.

Integers are read and written big-endian, as FIPS 205's `toInt` and `toByte` do.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Byte conversions and ordered vectors -/

export EthLib.Base (packBytes readBytes)
export EthLib.Cryptography.HashSig (unpackBytes? ofFnInOrder)

/-- `toInt(X, k)` (FIPS 205 Algorithm 2): the integer whose big-endian bytes these are.

For example, `[0x12, 0x34]` reads as `0x1234`. -/
def toInt {k : Nat} (x : Vector UInt8 k) : Nat :=
  EthLib.Base.bytesToNat x.toList

/-- `toByte(x, k)` (FIPS 205 Algorithm 3): the `k` low bytes of `x`, most significant first.

A larger `x` keeps only `x % 256^k`.

For example, `toByte 2 0x1234` is `[0x12, 0x34]`. -/
def toByte (k x : Nat) : Vector UInt8 k :=
  ⟨(EthLib.Base.natToBytes k x).toArray, by simp [EthLib.Base.natToBytes_length]⟩

/-! ## Objects -/

/-- A hash value of `n` bytes.

Chain values, Merkle nodes, FORS secrets and leaves are all digests. -/
abbrev Digest := Vector UInt8 N

/-- `PK.seed`, hashed first into every addressed call.

It makes one key's hash functions independent of another's. -/
abbrev PkSeed := Vector UInt8 N

/-- `ADRS`, the address hashed after `PK.seed`.

It names the call site of one hash inside one key. -/
abbrev Adrs := Vector UInt8 ADRS_LEN

/-- The randomizer `R` hashed with the message into the message digest.

It is part of the signature. -/
abbrev Randomizer := Vector UInt8 RANDOMIZER_LEN

/-- The message to sign: a 256-bit message hash, not a document. -/
abbrev Message := Vector UInt8 MESSAGE_LEN

/-- `SK.seed`, the 32-byte secret seed every secret derives from. -/
abbrev Seed := Vector UInt8 SEED_LEN

/-- One 32-byte output of Keccak-256, before it is cut to a digest. -/
abbrev HashOutput := Vector UInt8 HASH_LEN

/-- A codeword of WOTS+C: one position on each of the 64 chains. -/
abbrev Codeword := Vector (Fin CHAIN_LENGTH) V

/-! ## The layers of the hypertree

The layers are counted from the bottom, as the layer word of an address counts them.

- Layer 0, the bottom: `2^18` trees of height 8, each leaf signing one FORS instance.
- Layer 1, the middle: `2^10` trees of height 8.
- Layer 2, the top: one tree of height 10, whose root is `PK.root`.
-/

/-- One of the three layers of the hypertree. -/
inductive Layer where
  /-- Layer 0: its one-time keys sign FORS public keys. -/
  | bottom
  /-- Layer 1: its one-time keys sign the roots of bottom trees. -/
  | middle
  /-- Layer 2: one tree, whose one-time keys sign the roots of middle trees. -/
  | top
  deriving DecidableEq, Repr

/-- The layer's number `l`, counted from the bottom: the layer word of its addresses. -/
def Layer.toNat : Layer → Nat
  | .bottom => 0
  | .middle => 1
  | .top => 2

/-- `h_l`: the height of each tree of the layer. -/
def Layer.height : Layer → Nat
  | .bottom => LOWER_HEIGHT
  | .middle => LOWER_HEIGHT
  | .top => TOP_HEIGHT

/-- `beta_l`: the index bits below the layer, the heights of the layers under it added. -/
def Layer.below : Layer → Nat
  | .bottom => 0
  | .middle => LOWER_HEIGHT
  | .top => 2 * LOWER_HEIGHT

/-! ## Where a one-time key sits -/

/-- A one-time key `K = (l, tau, e)`: its layer, its tree on that layer and its leaf in that tree.

The leaf is FIPS 205's key pair address. -/
structure OtsKey where
  /-- The layer of the key. -/
  layer : Layer
  /-- The tree of the layer that holds the key. -/
  tree : Nat
  /-- The key's leaf in that tree, below `2^h` for the layer's height `h`. -/
  leaf : Nat
  deriving DecidableEq, Repr

/-- `K_l(idx)`: the key of a layer on the way from index `idx` up to the root (FIPS 205 §7).

The bits below the layer are dropped, and what is left splits into a tree and a leaf.

- Bottom: tree `idx >> 8`, leaf `idx mod 2^8`.
- Middle: tree `idx >> 16`, leaf `(idx >> 8) mod 2^8`.
- Top: tree 0, leaf `idx >> 16`.
-/
def OtsKey.ofIndex (layer : Layer) (idx : Nat) : OtsKey where
  layer := layer
  tree := idx >>> (layer.below + layer.height)
  leaf := (idx >>> layer.below) % 2 ^ layer.height

/-! ## Lists of digests -/

/-- The bytes of a list of digests, in order. -/
def packDigests {n : Nat} (ds : Vector Digest n) : ByteArray :=
  -- Digest `i` lands at bytes `16i` to `16i + 15`.
  packBytes ds.flatten

/-- Cut a byte field into `n` consecutive chunks of `m` bytes. -/
def splitChunks {n m : Nat} (bytes : Vector UInt8 (n * m)) : Vector (Vector UInt8 m) n :=
  -- Byte j of chunk i sits at position m i + j of the field.
  Vector.ofFn fun i => Vector.ofFn fun j => bytes[i.val * m + j.val]'(by
    -- With i < n and j < m, that position is below m n.
    have hi := i.isLt
    have hj := j.isLt
    have := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at this
    omega)

/-- Cut a byte field into consecutive 16-byte digests. -/
def splitDigests {n : Nat} (bytes : Vector UInt8 (n * N)) : Vector Digest n :=
  splitChunks bytes

end EthLib.Cryptography.Sphincs
