module

public import EthLib.Cryptography.Sphincs.Types

/-!
# leanSPHINCS addresses

Addresses keep the hash inputs of a key distinct.

Every addressed hash call of a key is `H(PK.seed | ADRS | M)`.

The address `ADRS` names the call site.

One hash for every call site would expose many targets at once.

A preimage among `M` targets then costs `2^128 / M`.

Giving each call site its own address removes that discount.

The address is FIPS 205's: eight big-endian 32-bit words.

leanSPHINCS adds one address type, for the WOTS+C encoding.

Source: FIPS 205 §4.2 and §4.3, and Appendix A of [main.tex][main].

[main]: https://github.com/leanEthereum/leanVM/blob/5e3ade21d339a45e1b3b0dba97ad9300ab50e49b/doc/lean_sphincs/main.tex
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## The encoding -/

/-- `enc(l, tau, t, u_1, u_2, u_3)`: the 32 bytes of one address.

```text
    [ layer: 4 | tree: 12 | type: 4 | u_1: 4 | u_2: 4 | u_3: 4 ]
```

- `layer` is the hypertree layer, counted from the bottom.
- `tree` is the tree on that layer, written as a 96-bit word, so its first 4 bytes are zero.
- `type` says what the call computes, and gives the meaning of the last three words.
- `u_1` is the key pair address.
- `u_2` is the chain address or the tree height.
- `u_3` is the hash address or the tree index.
- Every word is big-endian.
-/
def encodeAdrs (layer : UInt32) (tree : UInt64) (type keyPair word2 word3 : UInt32) : Adrs :=
  toByte 4 layer.toNat ++ toByte 12 tree.toNat ++ toByte 4 type.toNat ++ toByte 4 keyPair.toNat
    ++ toByte 4 word2.toNat ++ toByte 4 word3.toNat

/-! ## Address types -/

/-- What one hash call computes: the address types of FIPS 205 §4.2, and the WOTS+C encoding. -/
inductive AdrsType where
  /-- `WOTS_HASH`: one step along a chain. -/
  | wotsHash
  /-- `WOTS_PK`: a one-time key's Merkle leaf, from its chain ends. -/
  | wotsPk
  /-- `TREE`: a Merkle node of the hypertree, from its two children. -/
  | tree
  /-- `FORS_TREE`: a FORS leaf from its secret, or a FORS node from its two children. -/
  | forsTree
  /-- `FORS_ROOTS`: the FORS public key, from the roots of the FORS trees. -/
  | forsRoots
  /-- `WOTS_PRF`: the start of one chain of a one-time key, from `SK.seed`. -/
  | wotsPrf
  /-- `FORS_PRF`: the secret of one FORS leaf, from `SK.seed`. -/
  | forsPrf
  /-- `WOTS_ENC`: the digest whose digits a one-time key signs, from the message and a counter.

  FIPS 205 has no such type, since WOTS+ has no counter. -/
  | wotsEnc
  deriving DecidableEq, Repr

/-- The type word: FIPS 205's codes 0 to 6, and 7 for the WOTS+C encoding. -/
def AdrsType.code : AdrsType → UInt32
  | .wotsHash => 0
  | .wotsPk => 1
  | .tree => 2
  | .forsTree => 3
  | .forsRoots => 4
  | .wotsPrf => 5
  | .forsPrf => 6
  | .wotsEnc => 7

/-! ## Addresses of one key

An address of a one-time key or a FORS instance carries a layer, a tree and a type.

Each word holds its value modulo `2^32`, and the tree modulo `2^64`.

Every value that an honest call puts there fits.

- A tree is below `2^18`, and a leaf below `2^10`.
- A FORS tree index is below `24 * 2^10`.
- A chain index, a chain position, a height and a node index are below `2^10`. -/

/-- `ADRS` of a type in tree `tree` of a layer, with its last three words. -/
def adrs (type : AdrsType) (layer : Layer) (tree keyPair word2 word3 : Nat) : Adrs :=
  encodeAdrs (UInt32.ofNat layer.toNat) (UInt64.ofNat tree) type.code (UInt32.ofNat keyPair)
    (UInt32.ofNat word2) (UInt32.ofNat word3)

/-- An address of a one-time key `K = (l, tau, e)`: its tree's, with its leaf as the key pair. -/
def keyAdrs (type : AdrsType) (key : OtsKey) (word2 word3 : Nat) : Adrs :=
  adrs type key.layer key.tree key.leaf word2 word3

/-! ## WOTS+C and the hypertree -/

/-- `ADRS_chain(K, i, mu) = enc(l, tau, 0, e, i, mu)`: the step of chain `i` from position `mu`.

The hash address is the position the step leaves. -/
def adrsChain (key : OtsKey) (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) : Adrs :=
  keyAdrs .wotsHash key i.val mu.val

/-- `ADRS_pk(K) = enc(l, tau, 1, e, 0, 0)`: the Merkle leaf of a one-time key. -/
def adrsPk (key : OtsKey) : Adrs :=
  keyAdrs .wotsPk key 0 0

/-- `ADRS_node(l, tau, z, j) = enc(l, tau, 2, 0, z, j)`: node `j` at height `z` of a tree.

The key pair word is zero, as FIPS 205's `xmss_node` leaves it. -/
def adrsNode (layer : Layer) (tree z j : Nat) : Adrs :=
  adrs .tree layer tree 0 z j

/-- `ADRS_prf(K, i) = enc(l, tau, 5, e, i, 0)`: the start of chain `i` of a one-time key. -/
def adrsPrf (key : OtsKey) (i : Fin V) : Adrs :=
  keyAdrs .wotsPrf key i.val 0

/-- `ADRS_enc(K) = enc(l, tau, 7, e, 0, 0)`: the digest a one-time key signs. -/
def adrsEnc (key : OtsKey) : Adrs :=
  keyAdrs .wotsEnc key 0 0

/-! ## FORS

The FORS instance of index `idx` is FIPS 205's at the bottom key `K_0(idx) = (0, tau, e)`.

Its addresses hold layer 0, tree `tau` and key pair `e`. -/

/-- `ADRS_fors(idx, z, j) = enc(0, tau, 3, e, z, j)`: a FORS leaf (`z = 0`) or node.

The tree index `j` counts the nodes at height `z` across the trees. -/
def adrsFors (idx z j : Nat) : Adrs :=
  keyAdrs .forsTree (OtsKey.ofIndex .bottom idx) z j

/-- `ADRS_roots(idx) = enc(0, tau, 4, e, 0, 0)`: the FORS public key of instance `idx`. -/
def adrsRoots (idx : Nat) : Adrs :=
  keyAdrs .forsRoots (OtsKey.ofIndex .bottom idx) 0 0

/-- `ADRS_fprf(idx, j) = enc(0, tau, 6, e, 0, j)`: the secret of the FORS leaf of tree index `j`. -/
def adrsFprf (idx j : Nat) : Adrs :=
  keyAdrs .forsPrf (OtsKey.ofIndex .bottom idx) 0 j

end EthLib.Cryptography.Sphincs
