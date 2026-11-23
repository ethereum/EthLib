module

public import EthLib.Cryptography.Merkle.Tree
public import EthLib.Cryptography.Xmss.Ots

/-!
# The leanXMSS trees

The Merkle trees of one layer, whose leaves are the layer's one-time keys.

On layer `l`, the node `X_{lambda,j}` hashes its two children, for `1 <= lambda <= 16`.

- The top layer is one tree, with root `X_{16,0}`.
- The bottom layer is `2^16` trees whose node indices are global.
- Level `lambda` of the bottom layer has `2^(32 - lambda)` nodes.
- Bottom tree `b` holds the nodes `j` with `floor(j / 2^(16 - lambda)) = b`.
- Its root is `X_{16,b}`.

A signature carries its key's path: the sibling of every node on the way up.

For example, in a tree of height 2 with leaves `l_0` to `l_3`, the path of `l_2` holds two nodes:

- `l_3`, its sibling on level 0.
- `X_{1,0}`, the sibling of its parent on level 1.

The trees of a layer are Merkle trees whose node hash reads the node's position into its address.

Every definition takes the hash `H`.

A node computes its left subtree, then its right subtree, then its own hash.

Source: the leanXMSS specification draft, section "Trees".

Each tree is the Merkle tree of Construction 1 of [ePrint 2025/055][hbms], §3.3.

The bottom layer's node indices are global across its trees, which Construction 1 does not need.

[hbms]: https://eprint.iacr.org/2025/055
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4)

/-! ## Nodes -/

/-- The parent at a position, from its two children.

The address holds the level modulo 17, and the index within the level.

The tree hashes only at levels 1 to 16, so the address names the true level. -/
def nodeHash (publicParam : PublicParam) (layer : Layer) (p : Merkle.Position)
    (left right : Digest) :
    m Digest :=
  -- `X_{lambda,j} = Th(P, A_node(l, lambda, j), X_{lambda-1,2j} | X_{lambda-1,2j+1})`.
  --
  -- The payload is the left child, then the right child.
  th H publicParam (.node layer (Fin.ofNat _ p.level) (UInt32.ofNat p.index))
    #[left.lo, left.hi, right.lo, right.hi]

/-- `X_{0,j}`: the leaf of one-time key `j`. -/
def leaves (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (j : Nat) : m Digest :=
  otsPublicLeaf H publicParam prf layer (UInt32.ofNat j)

/-- `X_{level,j}`: node `j` on `level` of a layer.

Computing it evaluates the `2^level` leaves below it. -/
def node (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (level j : Nat) : m Digest :=
  Merkle.node (nodeHash H publicParam layer) (leaves H publicParam prf layer) ⟨level, j⟩

/-- Every node under node `j` on `level` of a layer, each computed once.

Its top value is `X_{level,j}`.

It holds the `level` lowest siblings of every key below that node: the whole path at level 16. -/
def build (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (level j : Nat) :
    m (Merkle.Built Digest) :=
  Merkle.build (nodeHash H publicParam layer) (leaves H publicParam prf layer) ⟨level, j⟩

/-! ## The path -/

/-- The path of key `e`, from the leaf up, level 0 first. -/
def path (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : Nat) :
    m (Vector Digest LAYER_HEIGHT) :=
  -- `pi_lambda = X_{lambda, floor(e / 2^lambda) xor 1}`, where `xor 1` flips the low bit.
  Merkle.path (nodeHash H publicParam layer) (leaves H publicParam prf layer) LAYER_HEIGHT e

/-- `Tree.fold(l, e, X, pi)`: the root a path leads to from the leaf of key `e`. -/
def fold (publicParam : PublicParam) (layer : Layer) (e : Nat) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) : m Digest :=
  Merkle.climb (nodeHash H publicParam layer) ⟨0, e⟩ leaf pi.toList

end EthLib.Cryptography.Xmss
