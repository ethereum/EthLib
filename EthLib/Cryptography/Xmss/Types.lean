module

public import EthLib.Base.Bytes
public import EthLib.Base.LittleEndian
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Cryptography.HashSig
public import EthLib.Cryptography.Xmss.Constants

/-!
# leanXMSS types

Fixed-size objects, held as Keccak lanes.

Every object of the scheme is 16 or 32 bytes, so it is two or four lanes.

A lane is 8 bytes, least significant first, as in FIPS 202 §3.1.2 and Appendix B.1.

So an object and every hash input made of objects needs no byte moved.

Bytes appear only in serialization.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

export EthLib.Cryptography.Hash.Keccak (Lanes2 Lanes4)

/-! ## Objects -/

/-- A hash value: 16 bytes, as two lanes.

Chain values, Merkle nodes and leaves are all digests. -/
abbrev Digest := Lanes2

/-- The public parameter `P`, hashed into every call: 16 bytes, as two lanes.

It makes one key's hash functions independent of another's. -/
abbrev PublicParam := Lanes2

/-- The randomizer `rho` under which a one-time key's digest is a codeword: 16 bytes.

It is part of the signature. -/
abbrev Randomizer := Lanes2

/-- The message to sign: a 256-bit message hash, not a document, as four lanes. -/
abbrev Message := Lanes4

/-- A 32-byte seed, as four lanes.

The secret key is one, and the scheme's seed `S` derived from it is another. -/
abbrev Seed := Lanes4

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

/-! ## Little-endian integers

The conversions `LE_{8k}` and `LE^-1` of the paper are the shared little-endian ones.
-/

export EthLib.Base (uintToBytes bytesToUint)

/-! ## Hash inputs

A hash input is a string of lanes, so its length in bytes is a multiple of 8. -/

/-- The lanes of a list of digests, in order: digest `i` is lanes `2i` and `2i + 1`. -/
def digestLanes {n : Nat} (ds : Vector Digest n) : Array UInt64 :=
  ds.toArray.foldl (fun acc d => (acc.push d.lo).push d.hi) (Array.emptyWithCapacity (2 * n))

/-! ## Crossing to and from untyped bytes -/

export EthLib.Base (packBytes readBytes)
export EthLib.Cryptography.HashSig (unpackBytes?)

/-- The bytes of a list of digests, in order. -/
def packDigests {n : Nat} (ds : Vector Digest n) : ByteArray :=
  -- Digest `i` lands at bytes `16i` to `16i + 15`.
  packBytes (ds.map (·.bytes)).flatten

/-- Cut the `16 n` bytes at an offset of a buffer into consecutive digests. -/
def splitDigests (n : Nat) (bytes : ByteArray) (offset : Nat) : Vector Digest n :=
  -- Digest i sits at bytes offset + 16 i to offset + 16 i + 15.
  Vector.ofFn fun i => Hash.Keccak.Lanes2.read bytes (offset + 16 * i.val)

/-! ## Computing a vector in order -/

export EthLib.Cryptography.HashSig (ofFnInOrder)

end EthLib.Cryptography.Xmss
