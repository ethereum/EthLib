import EthLib.Cryptography.Xmss.Types

/-!
# `Xmss.Address`

Addresses keep the hash inputs of a key distinct.

Every hash call of a key is `H(P | A | M)`, and `A` names the call site.

One hash for every call site would expose many targets at once:

```text
per key   2^32 leaf indices x 58 chains x 3 steps   ~ 2^40
```

Finding one preimage among `M` targets costs `2^128 / M`.

Giving each call site its own address removes the discount.

Source: the leanXMSS specification draft, section "Address encoding".
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## The encoding -/

/-- `enc(tau, mu, hi, lo)`: the 16 bytes of one address.

```text
    [ lo: 4 | hi: 3 | tau + 32 mu: 1 | zero: 8 ]
```

- `tau < 32` is the address type.
- `mu < 8` is a chain position, zero outside chain steps.
- `hi < 2^24` and `lo < 2^32` locate the call inside its type.
- Every field is little-endian.
-/
def encodeAddress (tau : Fin 32) (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    Address :=
  -- Type and position share one byte: `tau` in bits 0 to 4, `mu` in bits 5 to 7.
  littleEndian 4 lo.toNat ++ littleEndian 3 hi.val
    ++ littleEndian 1 (tau.val + 32 * mu.val) ++ littleEndian 8 0

/-! ## Address types -/

/-- What one hash call computes. -/
inductive AddressType where
  /-- The start of two chains, from the seed. -/
  | prf
  /-- One step along a chain. -/
  | chain
  /-- A one-time key's Merkle leaf, from its chain ends. -/
  | leaf
  /-- A Merkle parent, from its two children. -/
  | node
  /-- The public parameter, from the seed. -/
  | param
  /-- The base of a one-time signature's randomizers. -/
  | rnd
  /-- The digest a one-time key signs. -/
  | msg
  deriving DecidableEq, Repr

/-- The type code `tau` the specification assigns. -/
def AddressType.code : AddressType → Fin 32
  | .prf => 0
  | .chain => 1
  | .leaf => 2
  | .node => 3
  | .param => 5
  | .rnd => 7
  | .msg => 12

/-! ## The two layers -/

/-- `hi_l(a) = a + 2^23 l`: the top layer sets bit 23 of `hi`.

The two layers share one public parameter, so this bit is what separates them. -/
def layerHi (layer : Layer) (a : Fin (2 ^ 23)) : Fin (2 ^ 24) :=
  ⟨a.val + 2 ^ 23 * layer.toNat, by
    -- `a < 2^23` and the layer adds at most `2^23`.
    have := a.isLt
    cases layer <;> simp only [Layer.toNat] <;> omega⟩

/-! ## The addresses of a key

- `e` is a one-time key's index on its layer.
- `j` is a node's index on its level.
-/

/-- `A_prf(l, e, j)`: the start of chains `2j` and `2j + 1` of key `e`. -/
def addrPrf (layer : Layer) (e : UInt32) (j : Fin (V / 2)) : Address :=
  encodeAddress AddressType.prf.code 0 (layerHi layer (j.castLE (by decide))) e

/-- `A_chain(l, e, mu)`: the step from position `mu` of every chain of key `e`.

The chain index is not in the address: it follows the value in the hash input. -/
def addrChain (layer : Layer) (e : UInt32) (mu : Fin (CHAIN_LENGTH - 1)) : Address :=
  encodeAddress AddressType.chain.code (mu.castLE (by decide)) (layerHi layer 0) e

/-- `A_leaf(l, e)`: the Merkle leaf of key `e`. -/
def addrLeaf (layer : Layer) (e : UInt32) : Address :=
  encodeAddress AddressType.leaf.code 0 (layerHi layer 0) e

/-- `A_node(l, lambda, j)`: node `j` on level `lambda` of a layer. -/
def addrNode (layer : Layer) (level : Fin (LAYER_HEIGHT + 1)) (j : UInt32) : Address :=
  encodeAddress AddressType.node.code 0 (layerHi layer (level.castLE (by decide))) j

/-- `A_param`: the public parameter. -/
def addrParam : Address :=
  encodeAddress AddressType.param.code 0 0 0

/-- `A_rnd(l, e)`: the randomizer base of key `e`. -/
def addrRnd (layer : Layer) (e : UInt32) : Address :=
  encodeAddress AddressType.rnd.code 0 (layerHi layer 0) e

/-- `A_msg(l, e)`: the digest key `e` signs. -/
def addrMsg (layer : Layer) (e : UInt32) : Address :=
  encodeAddress AddressType.msg.code 0 (layerHi layer 0) e

end EthLib.Cryptography.Xmss
