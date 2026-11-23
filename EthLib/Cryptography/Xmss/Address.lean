module

public import EthLib.Cryptography.Xmss.Types

/-!
# leanXMSS addresses

The call sites of the hash calls `H(P | A | M)` of the scheme, and their addresses `A`.

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

/-! ## Call sites

- `e` is a one-time key's index on its layer.
- `j` is the index of a pair of chains of a key, or of a node on its level.
-/

/-- A hash call of the scheme, with the arguments its address holds.

Each constructor is one kind of address of the specification. -/
inductive CallSite where
  /-- `A_prf(l, e, j)`: the start of chains `2j` and `2j + 1` of key `e`. -/
  | prf (layer : Layer) (e : UInt32) (j : Fin (V / 2))
  /-- `A_chain(l, e, mu)`: the step from position `mu` of every chain of key `e`.

  The chain index is not in the address: it follows the value in the hash input. -/
  | chain (layer : Layer) (e : UInt32) (mu : Fin (CHAIN_LENGTH - 1))
  /-- `A_leaf(l, e)`: the Merkle leaf of key `e`, from its chain ends. -/
  | leaf (layer : Layer) (e : UInt32)
  /-- `A_node(l, lambda, j)`: node `j` on level `lambda` of a layer, from its two children. -/
  | node (layer : Layer) (level : Fin (LAYER_HEIGHT + 1)) (j : UInt32)
  /-- `A_param`: the public parameter, from the seed. -/
  | param
  /-- `A_rnd(l, e)`: the base of the randomizers of key `e`. -/
  | rnd (layer : Layer) (e : UInt32)
  /-- `A_msg(l, e)`: the digest key `e` signs. -/
  | msg (layer : Layer) (e : UInt32)
  deriving DecidableEq, Repr

/-! ## The four fields of an address -/

/-- `tau`: the type code the specification assigns to each kind of call. -/
@[inline] def CallSite.tau : CallSite → Fin 32
  | .prf .. => 0
  | .chain .. => 1
  | .leaf .. => 2
  | .node .. => 3
  | .param => 5
  | .rnd .. => 7
  | .msg .. => 12

/-- `mu`: the position of a chain step, and zero at every other call site. -/
@[inline] def CallSite.mu : CallSite → Fin 8
  | .chain _ _ mu => mu.castLE (by decide)
  | _ => 0

/-- `hi`: the layer bit above the pair of chains or the level, and zero for the parameter. -/
@[inline] def CallSite.hi : CallSite → Fin (2 ^ 24)
  -- `A_prf`: `hi = hi_l(j)`.
  | .prf layer _ j => layerHi layer (j.castLE (by decide))
  -- `A_node`: `hi = hi_l(lambda)`.
  | .node layer level _ => layerHi layer (level.castLE (by decide))
  -- `A_param`: `hi = 0`, since the two layers share the parameter.
  | .param => 0
  -- `A_chain`, `A_leaf`, `A_rnd` and `A_msg`: `hi = hi_l(0)`.
  | .chain layer .. | .leaf layer _ | .rnd layer _ | .msg layer _ => layerHi layer 0

/-- `lo`: the key, the index of a node, or zero for the parameter. -/
@[inline] def CallSite.lo : CallSite → UInt32
  | .prf _ e _ | .chain _ e _ | .leaf _ e | .rnd _ e | .msg _ e => e
  | .node _ _ j => j
  | .param => 0

/-! ## The encoding -/

/-- `enc(tau, mu, hi, lo)`: the address of a call site, the 16 bytes its hash reads, as two lanes.

The bytes are `lo` (4), `hi` (3), `tau + 32 mu` (1), then 8 zero bytes.

- `tau < 32` is the type of the call.
- `mu < 8` is a chain position, zero outside chain steps.
- `hi < 2^24` and `lo < 2^32` locate the call inside its type.
- Every field is little-endian.

The first lane holds bytes 0 to 7, least significant first, and the second lane is zero.

So `lo` is bits 0 to 31 of the first lane, `hi` bits 32 to 55, and the type byte bits 56 to 63.

Each call site gets its own address, so that the hash inputs of a key stay distinct:

- Over its `2^32` leaf indices, a key makes `2^32 * 58 * 3`, about `2^40`, chain steps alone.
- One hash for every call site would expose all of them as targets at once.
- Finding one preimage among `M` targets costs `2^128 / M`.
- Distinct addresses, with the chain index in the payload, remove that discount.

The address plays the part of the tweak of [ePrint 2025/055][hbms], §7.1, with its own layout.

[hbms]: https://eprint.iacr.org/2025/055
-/
@[inline] def CallSite.encode (site : CallSite) : Address :=
  -- `enc(tau, mu, hi, lo) = LE_32(lo) | LE_24(hi) | LE_8(tau + 32 mu) | 0^64`.
  --
  -- Type and position share one byte: `tau` in bits 0 to 4, `mu` in bits 5 to 7.
  ⟨site.lo.toUInt64 ||| (UInt64.ofNat site.hi.val <<< 32)
      ||| (UInt64.ofNat (site.tau.val + 32 * site.mu.val) <<< 56),
    0⟩

end EthLib.Cryptography.Xmss
