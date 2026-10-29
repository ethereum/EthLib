import EthLib.Cryptography.Sphincs.Types

/-!
# `Sphincs.Address`

Addresses keep the hash inputs of a key distinct.

Every hash call of a key is `H(P | A | M)`, and the address `A` names the call site.

One hash for every call site would expose many targets at once, and a preimage among `M` targets costs `2^128 / M`.

Giving each call site its own address removes that discount.

Source: `fieldBytes`, `hashDomainFields` and `keygenDomainFields` in [FORS/Scheme.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean).
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## The encoding -/

/-- The 16 bytes of one address.

```text
    [ lo: 4 | hi: 3 | type + 32 step: 1 | layer: 1 | tree: 4 | zero: 3 ]
```

- `type < 32` says what the call computes.
- `step < 8` is a chain step, zero outside chain steps.
- `layer` and `tree` locate a hypertree call, and are zero outside the hypertree.
- `hi < 2^24` and `lo < 2^32` locate the call inside its type.
- Every field is little-endian.
-/
def encodeAddress (type : Fin 32) (step : Fin 8) (layer : Fin 256) (tree : UInt32)
    (hi : Fin (2 ^ 24)) (lo : UInt32) : Address :=
  -- Type and step share one byte: the type in bits 0 to 4, the step in bits 5 to 7.
  littleEndian 4 lo.toNat ++ littleEndian 3 hi.val ++ littleEndian 1 (type.val + 32 * step.val)
    ++ littleEndian 1 layer.val ++ littleEndian 4 tree.toNat ++ littleEndian 3 0

/-! ## Address types -/

/-- What one hash call computes. -/
inductive AddressType where
  /-- The starts of two chains of a one-time key, from the seed. -/
  | prf
  /-- One step along a chain. -/
  | chain
  /-- A one-time key's Merkle leaf, from its chain ends. -/
  | leaf
  /-- A Merkle parent in the hypertree, from its two children. -/
  | node
  /-- The digest whose digits a one-time key signs, from the message and a counter. -/
  | encoding
  /-- The public parameter, from the seed. -/
  | param
  /-- The randomizer of a message, from the seed. -/
  | rnd
  /-- The message digest, which picks the FORS instance and its leaves. -/
  | msg
  /-- The secrets of two FORS leaves, from the seed. -/
  | forsPrf
  /-- A FORS leaf, from its secret. -/
  | forsLeaf
  /-- A FORS parent, from its two children. -/
  | forsNode
  deriving DecidableEq, Repr

/-- The type code the scheme assigns.

Codes 6, 8 to 11, 13 and 16 belong to configurations this key does not have. -/
def AddressType.code : AddressType → Fin 32
  | .prf => 0
  | .chain => 1
  | .leaf => 2
  | .node => 3
  | .encoding => 4
  | .param => 5
  | .rnd => 7
  | .msg => 12
  | .forsPrf => 14
  | .forsLeaf => 15
  | .forsNode => 17

/-! ## The hypertree

A one-time key's calls carry its layer and tree, and its leaf in `lo`.

The bottom layer has the most trees, `2^17`, so a tree number fits its 4 bytes. -/

/-- An address of a one-time key: its layer and tree, and its leaf in `lo`. -/
def keyAddress (type : AddressType) (step : Fin 8) (key : OtsKey) (hi : Fin (2 ^ 24)) : Address :=
  encodeAddress type.code step ⟨key.layer.toNat, by cases key.layer <;> decide⟩
    (UInt32.ofNat key.tree) hi (UInt32.ofNat key.leaf)

/-- The start of chains `2j` and `2j + 1` of a key: `hi = j`. -/
def addrPrf (key : OtsKey) (j : Fin (V / 2)) : Address :=
  keyAddress .prf 0 key (j.castLE (by decide))

/-- The step of chain `i` from position `mu` to `mu + 1`: `hi = i`, and the step is `mu`. -/
def addrChain (key : OtsKey) (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) : Address :=
  keyAddress .chain (mu.castLE (by decide)) key (i.castLE (by decide))

/-- The Merkle leaf of a key: `hi = 0`. -/
def addrLeaf (key : OtsKey) : Address :=
  keyAddress .leaf 0 key 0

/-- The digest a key signs, from its message and a counter: `hi = 0`. -/
def addrEncoding (key : OtsKey) : Address :=
  keyAddress .encoding 0 key 0

/-- Node `j` on level `lambda` of a tree: `hi = lambda`, `lo = j`. -/
def addrNode (layer : Layer) (tree : Nat) (level : Fin (TOP_HEIGHT + 1)) (j : Nat) : Address :=
  encodeAddress AddressType.node.code 0 ⟨layer.toNat, by cases layer <;> decide⟩
    (UInt32.ofNat tree) (level.castLE (by decide)) (UInt32.ofNat j)

/-! ## Calls outside the hypertree

These carry a zero layer and a zero tree. -/

/-- The public parameter: every field zero. -/
def addrParam : Address :=
  encodeAddress AddressType.param.code 0 0 0 0 0

/-- The randomizer of a message: every field zero. -/
def addrRnd : Address :=
  encodeAddress AddressType.rnd.code 0 0 0 0 0

/-- Call `call` of the message digest: `hi` is the call number, every other field zero.

The digest needs 266 bits, so it takes two calls, 0 and 1. -/
def addrMsg (call : Fin DIGEST_CALLS) : Address :=
  encodeAddress AddressType.msg.code 0 0 0 (call.castLE (by decide)) 0

/-! ## FORS

A FORS call carries its instance `idx` in `lo`, and its tree `kappa` and a position in `hi`.

```text
    hi = kappa + 64 * position,   kappa < 64
```
-/

/-- `kappa + 64 p`: position `p` of tree `kappa`.

Positions below `16 * 2^10` keep it below `2^24`. -/
def forsHi (kappa : Fin FORS_TREES) (position : Fin (16 * 2 ^ FORS_HEIGHT)) : Fin (2 ^ 24) :=
  ⟨kappa.val + 64 * position.val, by
    -- `kappa < 24` and `position < 16384`, so the sum is below `64 * 16384 = 2^20`.
    have := kappa.isLt
    have := position.isLt
    simp only [FORS_TREES, FORS_HEIGHT] at *
    omega⟩

/-- The position of a FORS leaf or pair: its index. -/
def forsLeafPosition (leaf : Fin (2 ^ FORS_HEIGHT)) : Fin (16 * 2 ^ FORS_HEIGHT) :=
  leaf.castLE (by decide)

/-- The position of node `j` on level `lambda` of a FORS tree: `lambda + 16 j`. -/
def forsNodePosition (level : Fin 16) (j : Fin (2 ^ FORS_HEIGHT)) : Fin (16 * 2 ^ FORS_HEIGHT) :=
  ⟨level.val + 16 * j.val, by
    -- `lambda < 16` fills the low 4 bits, and `j` the bits above.
    have := level.isLt
    have := j.isLt
    simp only [FORS_HEIGHT] at *
    omega⟩

/-- The secrets of leaves `2p` and `2p + 1` of tree `kappa` of instance `idx`: `hi = kappa + 64 p`. -/
def addrForsPrf (idx : Nat) (kappa : Fin FORS_TREES) (p : Fin (2 ^ FORS_HEIGHT / 2)) : Address :=
  encodeAddress AddressType.forsPrf.code 0 0 0
    (forsHi kappa (forsLeafPosition (p.castLE (by decide)))) (UInt32.ofNat idx)

/-- Leaf `l` of tree `kappa` of instance `idx`: `hi = kappa + 64 l`. -/
def addrForsLeaf (idx : Nat) (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT)) : Address :=
  encodeAddress AddressType.forsLeaf.code 0 0 0 (forsHi kappa (forsLeafPosition l))
    (UInt32.ofNat idx)

/-- Node `j` on level `lambda` of tree `kappa` of instance `idx`: `hi = kappa + 64 (lambda + 16 j)`.

The scheme hashes levels 1 to 9: the two nodes of level 9 are the tree's part of the FORS key. -/
def addrForsNode (idx : Nat) (kappa : Fin FORS_TREES) (level : Fin 16) (j : Fin (2 ^ FORS_HEIGHT)) :
    Address :=
  encodeAddress AddressType.forsNode.code 0 0 0 (forsHi kappa (forsNodePosition level j))
    (UInt32.ofNat idx)

end EthLib.Cryptography.Sphincs
