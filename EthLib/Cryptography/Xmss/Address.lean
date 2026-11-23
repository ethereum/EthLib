module

public import EthLib.Cryptography.Xmss.Types

/-!
# leanXMSS addresses

The address `A` of each hash call `H(P | A | M)` of a key, which names the call site.

Source: the leanXMSS specification draft, section "Address encoding".
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## The encoding -/

/-- `enc(tau, mu, hi, lo)`: the 16 bytes of one address, as two lanes.

The bytes are `lo` (4), `hi` (3), `tau + 32 mu` (1), then 8 zero bytes.

- `tau < 32` is the address type.
- `mu < 8` is a chain position, zero outside chain steps.
- `hi < 2^24` and `lo < 2^32` locate the call inside its type.
- Every field is little-endian.

The first lane holds bytes 0 to 7, least significant first, and the second lane is zero.

So `lo` is bits 0 to 31 of the first lane, `hi` bits 32 to 55, and the type byte bits 56 to 63.

Each call site gets its own address, so that the hash inputs of a key stay distinct:

- Over its `2^32` leaf indices, a key makes `2^32 * 58 * 3`, about `2^40`, chain steps alone.
- One hash for every call site would expose all of them as targets at once.
- Finding one preimage among `M` targets costs `2^128 / M`.
- Distinct addresses remove that discount.

The address plays the part of the tweak of [ePrint 2025/055][hbms], §7.1, with its own layout.

[hbms]: https://eprint.iacr.org/2025/055
-/
def encodeAddress (tau : Fin 32) (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    Address :=
  -- `enc(tau, mu, hi, lo) = LE_32(lo) | LE_24(hi) | LE_8(tau + 32 mu) | 0^64`.
  --
  -- Type and position share one byte: `tau` in bits 0 to 4, `mu` in bits 5 to 7.
  ⟨lo.toUInt64 ||| (UInt64.ofNat hi.val <<< 32) ||| (UInt64.ofNat (tau.val + 32 * mu.val) <<< 56),
    0⟩

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
  -- Layer 0 keeps `a`, and layer 1 adds `2^23`.
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
  -- The pair index `j` sits in `hi`, under the layer bit, and the key in `lo`.
  encodeAddress AddressType.prf.code 0 (layerHi layer (j.castLE (by decide))) e

/-- `A_chain(l, e, mu)`: the step from position `mu` of every chain of key `e`.

The chain index is not in the address: it follows the value in the hash input. -/
def addrChain (layer : Layer) (e : UInt32) (mu : Fin (CHAIN_LENGTH - 1)) : Address :=
  -- The position goes in `mu`, and `hi` holds only the layer bit.
  encodeAddress AddressType.chain.code (mu.castLE (by decide)) (layerHi layer 0) e

/-- `A_leaf(l, e)`: the Merkle leaf of key `e`. -/
def addrLeaf (layer : Layer) (e : UInt32) : Address :=
  -- Only the type, the layer and the key vary.
  encodeAddress AddressType.leaf.code 0 (layerHi layer 0) e

/-- `A_node(l, lambda, j)`: node `j` on level `lambda` of a layer. -/
def addrNode (layer : Layer) (level : Fin (LAYER_HEIGHT + 1)) (j : UInt32) : Address :=
  -- The level goes in `hi`, under the layer bit, and the node index in `lo`.
  encodeAddress AddressType.node.code 0 (layerHi layer (level.castLE (by decide))) j

/-- `A_param`: the public parameter. -/
def addrParam : Address :=
  -- The two layers share the parameter, so every field but the type is zero.
  encodeAddress AddressType.param.code 0 0 0

/-- `A_rnd(l, e)`: the randomizer base of key `e`. -/
def addrRnd (layer : Layer) (e : UInt32) : Address :=
  -- Only the type, the layer and the key vary.
  encodeAddress AddressType.rnd.code 0 (layerHi layer 0) e

/-- `A_msg(l, e)`: the digest key `e` signs. -/
def addrMsg (layer : Layer) (e : UInt32) : Address :=
  -- Only the type, the layer and the key vary.
  encodeAddress AddressType.msg.code 0 (layerHi layer 0) e

end EthLib.Cryptography.Xmss
