import EthLib.Cryptography.Sphincs.Tree

/-!
# `Sphincs.Fors`

FORS, the few-time signature under each bottom leaf: 24 trees of 1024 leaves.

Each bottom leaf `idx` has its own FORS instance.

A FORS leaf is the hash of a secret.

The message digest picks one leaf in every tree, and the signature reveals that leaf's secret.

Tree `kappa` of instance `idx`, for `1 <= lambda <= 9`:

```text
    s_l          = H_{l mod 2}(P | A_fprf(idx, kappa, floor(l / 2)) | S)
    Y_{0,l}      = Th(P, A_fleaf(idx, kappa, l), s_l)
    Y_{lambda,j} = Th(P, A_fnode(idx, kappa, lambda, j), Y_{lambda-1,2j} | Y_{lambda-1,2j+1})
```

No tree has a root hash.

The FORS key is the two nodes of level 9 of every tree, 48 digests, and no hash folds them.

- `t_kappa[0] = Y_{9,0}` covers leaves 0 to 511 of tree `kappa`.
- `t_kappa[1] = Y_{9,1}` covers leaves 512 to 1023.

The bottom one-time key signs those 768 bytes directly.

An opening reveals a leaf's secret and its 10 path nodes.

The last path node is the other level-9 node, which the verifier needs in the key.

Source: FORS of [FIPS 205](https://doi.org/10.6028/NIST.FIPS.205) §8, without its root hash, as [leanSPHINCS.tex](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/leanSPHINCS.tex) §4 specifies.

The algorithms follow `forsNode`, `forsKey`, `treeOpen`, `treeRecover` and `forsRecover` in [FORS/Scheme.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean).
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Keys and openings -/

/-- A FORS key: the two level-9 nodes of each of the 24 trees, left node first. -/
abbrev ForsKey := Vector (Digest × Digest) FORS_TREES

/-- The opening of one FORS tree at one leaf. -/
structure TreeOpening where
  /-- The secret of the leaf the message digest picked. -/
  secret : Digest
  /-- The leaf's 10 path nodes, from level 0 up; the last is the other level-9 node. -/
  path : Vector Digest FORS_HEIGHT
  deriving DecidableEq

/-- A node index as a position in a tree: its low 10 bits.

Honest indices are below `2^10` already, so this changes nothing for them. -/
def forsIndex (j : Nat) : Fin (2 ^ FORS_HEIGHT) :=
  ⟨j % 2 ^ FORS_HEIGHT, Nat.mod_lt _ (by decide)⟩

/-! ## Secrets and leaves -/

/-- The secret of leaf `l` of tree `kappa` of instance `idx`.

Leaves `2p` and `2p + 1` take the two halves of one hash of the seed. -/
def forsSecret (pp : PublicParam) (seed : Seed) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) : Digest :=
  -- The pair `p = floor(l / 2)` names the hash, and the low bit of `l` names the half.
  let pair : Fin (2 ^ FORS_HEIGHT / 2) :=
    ⟨l.val / 2, by have := l.isLt; simp only [FORS_HEIGHT] at *; omega⟩
  halfOf ⟨l.val % 2, Nat.mod_lt _ (by decide)⟩
    (thFull pp (addrForsPrf idx kappa pair) (packBytes seed))

/-- Leaf `l` of tree `kappa` of instance `idx`: the hash of its secret. -/
def forsLeafHash (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT))
    (secret : Digest) : Digest :=
  th pp (addrForsLeaf idx kappa l) (packBytes secret)

/-- The parent at index `j` on `level` of tree `kappa` of instance `idx`, from its two children. -/
def forsNodeHash (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (level : Fin FORS_HEIGHT)
    (j : Nat) (left right : Digest) : Digest :=
  -- The payload is the left child, then the right child.
  th pp (addrForsNode idx kappa (level.castLE (by decide)) (forsIndex j))
    (packBytes left ++ packBytes right)

/-! ## Nodes -/

/-- `Y_{level,j}`: node `j` on `level` of tree `kappa` of instance `idx`.

Levels stop at 9: the tree is never hashed into a root. -/
def forsNode (pp : PublicParam) (seed : Seed) (idx : Nat) (kappa : Fin FORS_TREES) :
    (level : Nat) → level < FORS_HEIGHT → (j : Nat) → Digest
  -- A leaf hashes its own secret.
  | 0, _, j => forsLeafHash pp idx kappa (forsIndex j) (forsSecret pp seed idx kappa (forsIndex j))
  -- The children of node `j` on level `l + 1` are `2j` and `2j + 1` on level `l`.
  | l + 1, h, j => forsNodeHash pp idx kappa ⟨l + 1, h⟩ j
      (forsNode pp seed idx kappa l (by omega) (2 * j))
      (forsNode pp seed idx kappa l (by omega) (2 * j + 1))

/-- The FORS key of instance `idx`: the two level-9 nodes of every tree. -/
def forsKey (pp : PublicParam) (seed : Seed) (idx : Nat) : ForsKey :=
  Vector.ofFn fun kappa =>
    (forsNode pp seed idx kappa (FORS_HEIGHT - 1) (by decide) 0,
      forsNode pp seed idx kappa (FORS_HEIGHT - 1) (by decide) 1)

/-- The bytes of a FORS key, the message the bottom one-time key signs.

```text
    [ t_0[0] | t_0[1] | t_1[0] | t_1[1] | ... | t_23[1] ],   48 * 16 = 768 bytes
```
-/
def forsKeyBytes (key : ForsKey) : ByteArray :=
  -- Entry `2 kappa + b` is node `b` of tree `kappa`.
  packDigests (Vector.ofFn fun i : Fin (2 * FORS_TREES) =>
    let pair := key[i.val / 2]'(by have := i.isLt; omega)
    if i.val % 2 = 0 then pair.1 else pair.2)

/-! ## Signing -/

/-- The opening of tree `kappa` of instance `idx` at leaf `l`: its secret and its path.

```text
    pi_lambda = Y_{lambda, floor(l / 2^lambda) xor 1},   lambda < 10
```
-/
def treeOpen (pp : PublicParam) (seed : Seed) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) : TreeOpening where
  secret := forsSecret pp seed idx kappa l
  path := Vector.ofFn fun level =>
    forsNode pp seed idx kappa level level.isLt (siblingIndex l level)

/-- `Fts.sign`: the opening of every tree, each at the leaf the digest picked for it. -/
def forsSign (pp : PublicParam) (seed : Seed) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) : Vector TreeOpening FORS_TREES :=
  Vector.ofFn fun kappa => treeOpen pp seed idx kappa leaves[kappa]

/-! ## Recovering the key -/

namespace Internal

/-- Hash the node held on `level` with its sibling into their parent.

Bit `level` of the leaf index says which child the held node is. -/
def forsClimbStep (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (l : Nat)
    (level : Fin (FORS_HEIGHT - 1)) (current sibling : Digest) : Digest :=
  -- The parent sits one level up, at the index with one more bit shifted out.
  let parent : Fin FORS_HEIGHT := ⟨level.val + 1, by omega⟩
  if (l >>> level.val) % 2 == 0 then
    -- Bit zero: the held node is the left child.
    forsNodeHash pp idx kappa parent (l >>> (level.val + 1)) current sibling
  else
    -- Bit one: the held node is the right child.
    forsNodeHash pp idx kappa parent (l >>> (level.val + 1)) sibling current

/-- Climb the bottom `levels` levels of a FORS path, starting from a leaf. -/
def forsClimbUpto (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (l : Nat)
    (pi : Vector Digest FORS_HEIGHT) (leaf : Digest) :
    (levels : Nat) → levels ≤ FORS_HEIGHT - 1 → Digest
  | 0, _ => leaf
  -- The last step folds in the sibling on `k`, after climbing the `k` levels below it.
  | k + 1, h => forsClimbStep pp idx kappa l ⟨k, by omega⟩
      (forsClimbUpto pp idx kappa l pi leaf k (by omega))
      (pi[k]'(by simp only [FORS_HEIGHT] at *; omega))

end Internal

/-- The two level-9 nodes of tree `kappa` that an opening at leaf `l` leads to.

The leaf climbs 9 levels to its level-9 node.

The last path node is the other one, and bit 9 of `l` puts the two in order. -/
def treeRecover (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT))
    (opening : TreeOpening) : Digest × Digest :=
  -- Step 1: the leaf, from its revealed secret.
  let leaf := forsLeafHash pp idx kappa l opening.secret
  -- Step 2: climb levels 0 to 8, which reaches the leaf's level-9 node.
  let reached :=
    Internal.forsClimbUpto pp idx kappa l opening.path leaf (FORS_HEIGHT - 1) (Nat.le_refl _)
  -- Step 3: the last path node is the other level-9 node.
  let other := opening.path[FORS_HEIGHT - 1]'(by decide)
  if (l.val >>> (FORS_HEIGHT - 1)) % 2 == 0 then (reached, other) else (other, reached)

/-- `Fts.recover`: the FORS key the openings lead to, each at the leaf the digest picked. -/
def forsRecover (pp : PublicParam) (idx : Nat) (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) : ForsKey :=
  Vector.ofFn fun kappa => treeRecover pp idx kappa leaves[kappa] openings[kappa]

end EthLib.Cryptography.Sphincs
