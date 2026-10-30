import EthLib.Cryptography.Vrf.Hash

/-!
# `Vrf.Tree`

The tree over the `2^32` leaf secrets, and the root a leaf and a path lead to.

For `1 <= lambda <= 32`:

```text
    X_{0,j} = leaf(s_j)
    X_{lambda,j} = node(X_{lambda-1,2j}, X_{lambda-1,2j+1})
```

The root is `X_{32,0}`.

The path of index `i` holds the sibling of `i`'s ancestor on each level, from the leaf up.

How the holder derives the secrets is not part of the specification.

Source: [EIP-CRYPTO draft](https://github.com/kevaundray/EIPs/blob/fd2c9c53994eb1e7705011e0e4c53327bd61bdcc/EIPS/eip-crypto.md), section "VRF tree", `vrf_verify` and "Generation and opening".
-/

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-! ## Nodes -/

/-- `X_{level,j}`: node `j` on `level` of the tree over the secrets `s_i`.

Computing it evaluates the `2^level` leaves below it. -/
def node (secrets : UInt32 → Digest) : (level j : Nat) → Digest
  | 0, j => leafHash (secrets (UInt32.ofNat j))
  -- The children of node `j` on level `l + 1` are `2j` and `2j + 1` on level `l`.
  | l + 1, j => nodeHash (node secrets l (2 * j)) (node secrets l (2 * j + 1))

/-- The root: the one node on level 32. -/
def root (secrets : UInt32 → Digest) : Digest :=
  node secrets VRF_TREE_HEIGHT 0

/-! ## Opening -/

/-- The sibling of index `i`'s ancestor on `level`: that ancestor with its low bit flipped. -/
def siblingIndex (i level : Nat) : Nat :=
  (i >>> level) ^^^ 1

/-- The path of index `i`, from the leaf up.

```text
    pi_lambda = X_{lambda, floor(i / 2^lambda) xor 1}
```
-/
def path (secrets : UInt32 → Digest) (i : UInt32) : Vector Digest VRF_TREE_HEIGHT :=
  Vector.ofFn fun level => node secrets level (siblingIndex i.toNat level)

/-- The opening at index `i`: its secret and its path. -/
def opening (secrets : UInt32 → Digest) (i : UInt32) : Opening where
  secret := secrets i
  path := path secrets i

/-! ## Climbing a path -/

namespace Internal

/-- Hash the node held on `level` with its sibling into their parent.

Bit `level` of the index says which child the held node is. -/
def climbStep (i : UInt32) (level : Nat) (current sibling : Digest) : Digest :=
  if (i.toNat >>> level) % 2 == 0 then
    -- Bit zero: the held node is the left child.
    nodeHash current sibling
  else
    -- Bit one: the held node is the right child.
    nodeHash sibling current

/-- Climb the bottom `levels` levels of a path, starting from a leaf. -/
def climbUpto (i : UInt32) (pi : Vector Digest VRF_TREE_HEIGHT) (leaf : Digest) :
    (levels : Nat) → levels ≤ VRF_TREE_HEIGHT → Digest
  | 0, _ => leaf
  -- The last step folds in the sibling on `l`, after climbing the `l` levels below it.
  | l + 1, h => climbStep i l (climbUpto i pi leaf l (by omega)) (pi[l]'(by omega))

end Internal

/-- The root that the leaf at index `i` and a path lead to. -/
def pathRoot (i : UInt32) (leaf : Digest) (pi : Vector Digest VRF_TREE_HEIGHT) : Digest :=
  Internal.climbUpto i pi leaf VRF_TREE_HEIGHT (Nat.le_refl _)

end EthLib.Cryptography.Vrf
