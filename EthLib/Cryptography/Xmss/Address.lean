module

public import EthLib.Cryptography.Xmss.Types

/-!
# leanXMSS addresses

The addresses of the hash calls `H(P | A | M)` of the scheme, and their 16-byte encoding `A`.

Source: the leanXMSS specification draft, section "Address encoding".
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## The two layers -/

/-- `hi_l(a) = a + 2^23 l`: the top layer sets bit 23 of `hi`.

The two layers share one public parameter, so this bit is what separates them. -/
def layerHi (layer : Layer) (a : Fin (2 ^ 23)) : Fin (2 ^ 24) :=
  -- Layer 0 keeps `a`, and layer 1 adds `2^23`.
  ⟨a.val + 2 ^ 23 * layer.toNat, by
    -- `a < 2^23` and the layer adds at most `2^23`.
    have := a.isLt
    cases layer <;> simp only [Layer.toNat] <;> omega⟩

/-! ## Addresses -/

/-- An address of the specification: which hash call of a key it is.

Each constructor is one kind of address, named as in the specification. -/
inductive Address where
  /-- `A_prf(l, e, j)`: the derivation that starts chains `2j` and `2j + 1` of key `e`.

  - `layer`: the layer `l`, bottom or top.
  - `e`: the one-time key's index on its layer.
  - `j`: the pair of chains, from 0 to 28, since 29 derivations start the 58 chains. -/
  | prf (layer : Layer) (e : UInt32) (j : Fin (V / 2))
  /-- `A_chain(l, e, mu)`: one step of every chain of key `e`, from position `mu` to `mu + 1`.

  - `layer`: the layer `l`, bottom or top.
  - `e`: the one-time key's index on its layer.
  - `mu`: the position the step starts from, from 0 to 2.

  The chain index is not in the address: it follows the value in the hash input. -/
  | chain (layer : Layer) (e : UInt32) (mu : Fin (CHAIN_LENGTH - 1))
  /-- `A_leaf(l, e)`: the Merkle leaf of key `e`, from its 58 chain ends.

  - `layer`: the layer `l`, bottom or top.
  - `e`: the one-time key's index on its layer. -/
  | leaf (layer : Layer) (e : UInt32)
  /-- `A_node(l, lambda, j)`: node `j` on level `lambda` of a layer, from its two children.

  - `layer`: the layer `l`, bottom or top.
  - `level`: the level `lambda`, used from 1 to 16, since level 0 holds the leaves.
  - `j`: the node's index on its level, counted across all the trees of the layer. -/
  | node (layer : Layer) (level : Fin (LAYER_HEIGHT + 1)) (j : UInt32)
  /-- `A_param`: the public parameter `P`, from the scheme seed.

  It takes no argument: both layers share one parameter. -/
  | param
  /-- `A_rnd(l, e)`: the base of the randomizers that key `e` tries.

  - `layer`: the layer `l`, bottom or top.
  - `e`: the one-time key's index on its layer. -/
  | rnd (layer : Layer) (e : UInt32)
  /-- `A_msg(l, e)`: the digest key `e` signs, one hash per randomizer trial.

  - `layer`: the layer `l`, bottom or top.
  - `e`: the one-time key's index on its layer. -/
  | msg (layer : Layer) (e : UInt32)
  deriving DecidableEq, Repr

/-! ## The four fields of an address -/

/-- `tau`: the type code the specification assigns to each kind of call. -/
@[inline] def Address.tau : Address → Fin 32
  | .prf .. => 0
  | .chain .. => 1
  | .leaf .. => 2
  | .node .. => 3
  | .param => 5
  | .rnd .. => 7
  | .msg .. => 12

/-- `mu`: the position of a chain step, and zero at every other address. -/
@[inline] def Address.mu : Address → Fin 8
  | .chain _ _ mu => mu.castLE (by decide)
  | .prf .. | .leaf .. | .node .. | .param | .rnd .. | .msg .. => 0

/-- `hi`: the layer bit above the pair of chains or the level, and zero for the parameter. -/
@[inline] def Address.hi : Address → Fin (2 ^ 24)
  -- `A_prf`: `hi = hi_l(j)`.
  | .prf layer _ j => layerHi layer (j.castLE (by decide))
  -- `A_node`: `hi = hi_l(lambda)`.
  | .node layer level _ => layerHi layer (level.castLE (by decide))
  -- `A_param = enc(5, 0, 0, 0)`: `hi = 0`, with no layer bit.
  | .param => 0
  -- `A_chain`, `A_leaf`, `A_rnd` and `A_msg`: `hi = hi_l(0)`.
  | .chain layer .. | .leaf layer _ | .rnd layer _ | .msg layer _ => layerHi layer 0

/-- `lo`: the key, the index of a node, or zero for the parameter. -/
@[inline] def Address.lo : Address → UInt32
  | .prf _ e _ | .chain _ e _ | .leaf _ e | .rnd _ e | .msg _ e => e
  | .node _ _ j => j
  | .param => 0

/-! ## The encoding -/

/-- `enc(tau, mu, hi, lo)`: the encoding of an address, the 16 bytes its hash reads, as two lanes.

The bytes are `lo` (4), `hi` (3), `tau + 32 mu` (1), then 8 zero bytes.

- `tau < 32` is the type of the call.
- `mu < 8` is a chain position, zero outside chain steps.
- `hi < 2^24` and `lo < 2^32` locate the call inside its type.
- Every field is little-endian.

The first lane holds bytes 0 to 7, least significant first, and the second lane is zero.

So `lo` is bits 0 to 31 of the first lane, `hi` bits 32 to 55, and the type byte bits 56 to 63.

Each hash call of a key gets its own address, so that the hash inputs of the key stay distinct:

- Over its `2^32` leaf indices, a key makes `2^32 * 58 * 3`, about `2^40`, chain steps alone.
- One address shared by every call would expose all of them as targets at once.
- Finding one preimage among `M` targets costs `2^128 / M`.
- Distinct addresses, with the chain index in the payload, remove that discount.

The address plays the part of the tweak of [ePrint 2025/055][hbms], §7.1, with its own layout.

[hbms]: https://eprint.iacr.org/2025/055
-/
@[inline] def Address.encode (address : Address) : Lanes2 :=
  -- `enc(tau, mu, hi, lo) = LE_32(lo) | LE_24(hi) | LE_8(tau + 32 mu) | 0^64`.
  --
  -- Type and position share one byte: `tau` in bits 0 to 4, `mu` in bits 5 to 7.
  ⟨address.lo.toUInt64 ||| (UInt64.ofNat address.hi.val <<< 32)
      ||| (UInt64.ofNat (address.tau.val + 32 * address.mu.val) <<< 56),
    0⟩

end EthLib.Cryptography.Xmss
