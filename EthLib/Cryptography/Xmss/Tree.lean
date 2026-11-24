module

public import EthLib.Cryptography.Merkle.Tree
public import EthLib.Cryptography.Xmss.Ots

/-!
# The leanXMSS trees

The Merkle trees of one layer, whose leaves are the layer's one-time keys.

Source: the leanXMSS specification draft, section "Trees".

Each tree is the Merkle tree of Construction 1 of [ePrint 2025/055][hbms], §3.3.

The global indices of the bottom layer are not part of Construction 1.

[hbms]: https://eprint.iacr.org/2025/055
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4)

/-! ## Nodes -/

/-- The parent at a position, from its two children. -/
def nodeHash (publicParam : PublicParam) (layer : Layer) (p : Merkle.Position)
    (left right : Digest) :
    m Digest :=
  -- `X_{lambda,j} = Th(P, A_node(l, lambda, j), X_{lambda-1,2j} | X_{lambda-1,2j+1})`.
  -- The tree hashes only at levels 1 to 16, so the level modulo 17 in the address is the level.
  --
  -- The bottom layer is `2^16` trees, with node indices global across the layer.
  --
  -- So level `lambda` of the bottom layer has `2^(32 - lambda)` nodes.
  th H publicParam (.node layer (Fin.ofNat _ p.level) (UInt32.ofNat p.index))
    -- The payload is the left child, then the right child.
    #[left.lo, left.hi, right.lo, right.hi]

/-- `X_{0,j}`: the leaf of one-time key `j`. -/
def leaves (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (j : Nat) : m Digest :=
  otsPublicLeaf H publicParam prf layer (UInt32.ofNat j)

/-- `X_{level,j}`: node `j` on `level` of a layer. -/
def node (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (level j : Nat) : m Digest :=
  -- The left subtree first, then the right one, then the node's own hash: `2^level` leaves in all.
  Merkle.node (nodeHash H publicParam layer) (leaves H publicParam prf layer) ⟨level, j⟩

/-- Every node under node `j` on `level` of a layer, each computed once. -/
def build (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (level j : Nat) :
    m (Merkle.Built Digest) :=
  -- The top value is `X_{level,j}`.
  -- It holds the `level` lowest siblings of every key below, so at level 16 the whole path.
  --
  -- The top layer is one tree, with root `X_{16,0}`.
  --
  -- Bottom tree `b` has root `X_{16,b}`.
  --
  -- It holds the nodes `j` on level `lambda` with `floor(j / 2^(16 - lambda)) = b`.
  Merkle.build (nodeHash H publicParam layer) (leaves H publicParam prf layer) ⟨level, j⟩

/-! ## The path -/

/-- The path of key `e`: the sibling of every node on the way up, level 0 first. -/
def path (publicParam : PublicParam) (prf : SeedPrf m) (layer : Layer) (e : Nat) :
    m (Vector Digest LAYER_HEIGHT) :=
  -- `pi_lambda = X_{lambda, floor(e / 2^lambda) xor 1}`, where `xor 1` flips the low bit.
  -- For example, at height 2 the path of leaf 2 is leaf 3, then `X_{1,0}`.
  Merkle.path (nodeHash H publicParam layer) (leaves H publicParam prf layer) LAYER_HEIGHT e

/-- `Tree.fold(l, e, X, pi)`: the root a path leads to from the leaf of key `e`. -/
def fold (publicParam : PublicParam) (layer : Layer) (e : Nat) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) : m Digest :=
  -- Start at the leaf on level 0, and hash in one sibling per level.
  Merkle.climb (nodeHash H publicParam layer) ⟨0, e⟩ leaf pi.toList

end EthLib.Cryptography.Xmss
