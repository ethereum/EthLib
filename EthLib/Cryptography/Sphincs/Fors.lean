module

public import EthLib.Cryptography.Sphincs.Tree

/-!
# FORS

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

Source: FORS of [FIPS 205](https://doi.org/10.6028/NIST.FIPS.205) §8, without its root hash.

leanSPHINCS.tex §4 specifies that change:
<https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/leanSPHINCS.tex>

The algorithms follow five definitions of FORS/Scheme.lean:
<https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean>

They are `forsNode`, `forsKey`, `treeOpen`, `treeRecover` and `forsRecover`.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Keys and openings -/

/-- A FORS key: the two level-9 nodes of each of the 24 trees, left node first. -/
abbrev ForsKey := Vector (Digest × Digest) FORS_TREES

/-- The opening of one FORS tree at one leaf. -/
structure TreeOpening where
  /-- The secret of the leaf the message digest picked. -/
  secret : Digest
  /-- The leaf's 10 path nodes, from level 0 up.

  The last is the other level-9 node. -/
  path : Vector Digest FORS_HEIGHT
  deriving DecidableEq

/-- A node index as a position in a tree: its low 10 bits.

Honest indices are below `2^10` already, so this changes nothing for them. -/
def forsIndex (j : Nat) : Fin (2 ^ FORS_HEIGHT) :=
  ⟨j % 2 ^ FORS_HEIGHT, Nat.mod_lt _ (by decide)⟩

/-! ## Secrets and leaves -/

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-- The secret of leaf `l` of tree `kappa` of instance `idx`.

Leaves `2p` and `2p + 1` take the two halves of one derivation from the seed. -/
def forsSecret (pp : PublicParam) (prf : SeedPrf m) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) : m Digest := do
  -- The pair `p = floor(l / 2)` names the derivation, and the low bit of `l` names the half.
  let pair : Fin (2 ^ FORS_HEIGHT / 2) :=
    ⟨l.val / 2, by have := l.isLt; simp only [FORS_HEIGHT] at *; omega⟩
  return halfOf ⟨l.val % 2, Nat.mod_lt _ (by decide)⟩
    (← prf pp (addrForsPrf idx kappa pair) .empty)

/-- Leaf `l` of tree `kappa` of instance `idx`: the hash of its secret. -/
def forsLeafHash (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT))
    (secret : Digest) : m Digest :=
  th H pp (addrForsLeaf idx kappa l) (packBytes secret)

/-- The parent at index `j` on `level` of tree `kappa` of instance `idx`, from its two children.

The address holds the level modulo 16 and the index modulo `2^10`.

A FORS tree hashes only at levels 1 to 9, so the address names the true position. -/
def forsNodeHash (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (level j : Nat)
    (left right : Digest) : m Digest :=
  -- The payload is the left child, then the right child.
  th H pp (addrForsNode idx kappa (Fin.ofNat _ level) (forsIndex j))
    (packBytes left ++ packBytes right)

/-- `Y_{0,j}`: leaf `j` of tree `kappa` of instance `idx`, the hash of its secret. -/
def forsLeaves (pp : PublicParam) (prf : SeedPrf m) (idx : Nat) (kappa : Fin FORS_TREES)
    (j : Nat) : m Digest := do
  forsLeafHash H pp idx kappa (forsIndex j) (← forsSecret pp prf idx kappa (forsIndex j))

/-! ## Nodes -/

/-- `Y_{level,j}`: node `j` on `level` of tree `kappa` of instance `idx`.

Levels stop at 9: the tree is never hashed into a root. -/
def forsNode (pp : PublicParam) (prf : SeedPrf m) (idx : Nat) (kappa : Fin FORS_TREES)
    (level j : Nat) : m Digest :=
  Merkle.node (forsNodeHash H pp idx kappa) (forsLeaves H pp prf idx kappa) level j

/-- The FORS key of instance `idx`: the two level-9 nodes of every tree, tree 0 first. -/
def forsKey (pp : PublicParam) (prf : SeedPrf m) (idx : Nat) : m ForsKey :=
  ofFnInOrder FORS_TREES fun kappa => do
    let left ← forsNode H pp prf idx kappa (FORS_HEIGHT - 1) 0
    let right ← forsNode H pp prf idx kappa (FORS_HEIGHT - 1) 1
    return (left, right)

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

The path is the one of a tree of height 10, so its last node is the other level-9 node.

```text
    pi_lambda = Y_{lambda, floor(l / 2^lambda) xor 1},   lambda < 10
```
-/
def treeOpen (pp : PublicParam) (prf : SeedPrf m) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) : m TreeOpening := do
  let secret ← forsSecret pp prf idx kappa l
  let path ←
    Merkle.path (forsNodeHash H pp idx kappa) (forsLeaves H pp prf idx kappa) FORS_HEIGHT l
  return { secret, path }

/-- `Fts.sign`: the opening of every tree, each at the leaf the digest picked for it.

The trees are opened in order, tree 0 first. -/
def forsSign (pp : PublicParam) (prf : SeedPrf m) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) : m (Vector TreeOpening FORS_TREES) :=
  ofFnInOrder FORS_TREES fun kappa => treeOpen H pp prf idx kappa leaves[kappa]

/-! ## Recovering the key -/

/-- The two level-9 nodes of tree `kappa` that an opening at leaf `l` leads to.

The leaf climbs 9 levels to its level-9 node.

The last path node is the other one, and bit 9 of `l` puts the two in order. -/
def treeRecover (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (l : Fin (2 ^ FORS_HEIGHT))
    (opening : TreeOpening) : m (Digest × Digest) := do
  -- Step 1: the leaf, from its revealed secret.
  let leaf ← forsLeafHash H pp idx kappa l opening.secret
  -- Step 2: climb levels 0 to 8, which reaches the leaf's level-9 node.
  let reached ← Merkle.climb (forsNodeHash H pp idx kappa) 0 l leaf
    (opening.path.toList.take (FORS_HEIGHT - 1))
  -- Step 3: the last path node is the other level-9 node.
  return Merkle.ordered (l.val >>> (FORS_HEIGHT - 1)) reached
    (opening.path[FORS_HEIGHT - 1]'(by decide))

/-- `Fts.recover`: the FORS key the openings lead to, each at the leaf the digest picked.

The trees are recovered in order, tree 0 first. -/
def forsRecover (pp : PublicParam) (idx : Nat) (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) : m ForsKey :=
  ofFnInOrder FORS_TREES fun kappa => treeRecover H pp idx kappa leaves[kappa] openings[kappa]

end EthLib.Cryptography.Sphincs
