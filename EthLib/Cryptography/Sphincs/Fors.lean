module

public import EthLib.Cryptography.Sphincs.Tree

/-!
# FORS

FORS, the few-time signature under each bottom leaf: 24 trees of 1024 leaves.

Each bottom leaf `idx` has its own FORS instance, at the bottom key `K_0(idx) = (0, tau, e)`.

A FORS leaf is the hash of a secret.

The message digest picks one leaf in every tree, and the signature reveals that leaf's secret.

Node indices run across the trees.

In tree `kappa`, node `j` at height `z` has tree index `kappa 2^(a - z) + j`.

Leaf `s` of tree `kappa` is `Y_{0,s}`, the hash of its secret `sk_{kappa,s}`.

The tree's nodes are `Y_{z,j}` for `1 <= z <= a`, and its root is `Y^kappa_{a,0}`.

The FORS public key `Fors.key(idx)` is one digest, which the bottom one-time key signs.

An opening reveals a leaf's secret and its 10 path nodes.

Source: FORS of [FIPS 205][fips205] §8, with 24 trees of height 10 as in [leanSPHINCS.tex][note] §1.

[note]: https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/leanSPHINCS.tex
[fips205]: https://doi.org/10.6028/NIST.FIPS.205
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Openings -/

/-- The opening of one FORS tree at one leaf. -/
structure TreeOpening where
  /-- The secret of the leaf the message digest picked. -/
  secret : Digest
  /-- The leaf's 10 path nodes, from height 0 up. -/
  path : Vector Digest FORS_HEIGHT
  deriving DecidableEq

/-- The tree index of node `j` at height `z` of tree `kappa`: `kappa 2^(a - z) + j`.

It counts the nodes at height `z` across the trees, as FIPS 205's `fors_node` does. -/
def forsTreeIndex (kappa : Fin FORS_TREES) (z j : Nat) : Nat :=
  kappa.val * 2 ^ (FORS_HEIGHT - z) + j

/-! ## Secrets and leaves -/

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-- `sk_{kappa,s}`: the secret of leaf `s` of tree `kappa` of instance `idx`.

It is FIPS 205's `fors_skGen`, one `PRF` call. -/
def forsSecret (prf : Prf m) (idx : Nat) (kappa : Fin FORS_TREES) (s : Nat) : m Digest :=
  -- Algorithm 14, lines 2 to 5.
  --
  -- `sk_{kappa,s} = PRF(PK.seed, SK.seed, ADRS_fprf(idx, kappa 2^a + s))`.
  prf (adrsFprf idx (forsTreeIndex kappa 0 s))

/-- `Y_{0,s}`: leaf `s` of tree `kappa` of instance `idx`, `F` of its secret. -/
def forsLeafHash (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES) (s : Nat)
    (secret : Digest) : m Digest :=
  -- Algorithm 15, lines 3 to 5.
  --
  -- `Y_{0,s} = F(PK.seed, ADRS_fors(idx, 0, kappa 2^a + s), sk_{kappa,s})`.
  th H pkSeed (adrsFors idx 0 (forsTreeIndex kappa 0 s)) (packBytes secret)

/-- The parent at a position of tree `kappa` of instance `idx`, from its children.

The position's level is the height `z`, and its index is the index `j`. -/
def forsNodeHash (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES) (p : Merkle.Position)
    (left right : Digest) : m Digest :=
  -- Algorithm 15, lines 9 to 11.
  --
  -- `Y_{z,j} = H(PK.seed, ADRS_fors(idx, z, kappa 2^(a-z) + j), Y_{z-1,2j} | Y_{z-1,2j+1})`.
  --
  -- The payload is the left child, then the right child.
  th H pkSeed (adrsFors idx p.level (forsTreeIndex kappa p.level p.index))
    (packBytes left ++ packBytes right)

/-- `Y_{0,s}`, computed from the secret: leaf `s` of tree `kappa` of instance `idx`. -/
def forsLeaves (pkSeed : PkSeed) (prf : Prf m) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Nat) : m Digest := do
  forsLeafHash H pkSeed idx kappa s (← forsSecret prf idx kappa s)

/-! ## Nodes and the public key -/

/-- `Y_{z,j}`: node `j` at height `z` of tree `kappa` of instance `idx`, FIPS 205's `fors_node`. -/
def forsNode (pkSeed : PkSeed) (prf : Prf m) (idx : Nat) (kappa : Fin FORS_TREES)
    (z j : Nat) : m Digest :=
  Merkle.node (forsNodeHash H pkSeed idx kappa) (forsLeaves H pkSeed prf idx kappa) ⟨z, j⟩

/-- `Y^kappa_{a,0}`: the root of tree `kappa` of instance `idx`. -/
def forsRoot (pkSeed : PkSeed) (prf : Prf m) (idx : Nat) (kappa : Fin FORS_TREES) : m Digest :=
  Merkle.root (forsNodeHash H pkSeed idx kappa) (forsLeaves H pkSeed prf idx kappa) FORS_HEIGHT

/-- `T_k` over the roots of the 24 trees, tree 0 first: the FORS public key of instance `idx`.

The input has `48 + 24 * 16 = 432` bytes. -/
def forsPkFromRoots (pkSeed : PkSeed) (idx : Nat) (roots : Vector Digest FORS_TREES) :
    m Digest :=
  -- Algorithm 17, lines 22 to 24: `Fors.key(idx) = T_k(PK.seed, ADRS_roots(idx), Y^0_{a,0} | ...)`.
  th H pkSeed (adrsRoots idx) (packDigests roots)

/-- `Fors.key(idx)`: the FORS public key of instance `idx`, from the roots of its trees. -/
def forsKey (pkSeed : PkSeed) (prf : Prf m) (idx : Nat) : m Digest := do
  let roots ← ofFnInOrder FORS_TREES fun kappa => forsRoot H pkSeed prf idx kappa
  forsPkFromRoots H pkSeed idx roots

/-! ## Signing -/

/-- Every node of tree `kappa` of instance `idx`, each computed once.

Its top value is the tree's root `Y^kappa_{a,0}`, and it holds the path of each leaf. -/
def forsBuild (pkSeed : PkSeed) (prf : Prf m) (idx : Nat) (kappa : Fin FORS_TREES) :
    m (Merkle.Built Digest) :=
  Merkle.build (forsNodeHash H pkSeed idx kappa) (forsLeaves H pkSeed prf idx kappa)
    ⟨FORS_HEIGHT, 0⟩

/-- The opening of tree `kappa` of instance `idx` at leaf `s`, with the tree's root.

The opening is the leaf's secret and its path `P_z = Y_{z, floor(s / 2^z) xor 1}`, for `z < 10`.

One build of the tree gives both the path and the root. -/
def treeOpen (pkSeed : PkSeed) (prf : Prf m) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) : m (TreeOpening × Digest) := do
  let secret ← forsSecret prf idx kappa s.val
  let tree ← forsBuild H pkSeed prf idx kappa
  return ({ secret, path := tree.path FORS_HEIGHT s.val }, tree.value)

/-- `Fors.sign(idx, s)`: the opening of every tree, at the leaf the digest picked for it.

It also gives `Fors.key(idx)`, `T_k` over the roots of the trees it built.

Its openings are FIPS 205's `fors_sign`, and the trees are opened in order, tree 0 first. -/
def forsSign (pkSeed : PkSeed) (prf : Prf m) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    m (Vector TreeOpening FORS_TREES × Digest) := do
  let opened ← ofFnInOrder FORS_TREES fun kappa => treeOpen H pkSeed prf idx kappa leaves[kappa]
  let key ← forsPkFromRoots H pkSeed idx (opened.map Prod.snd)
  return (opened.map Prod.fst, key)

/-! ## Recovering the key -/

/-- The root of tree `kappa` that an opening at leaf `s` leads to.

The leaf is `F` of the revealed secret, and it climbs all 10 heights with the path. -/
def treeRecover (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) (opening : TreeOpening) : m Digest := do
  -- Step 1: the leaf, from its revealed secret.
  let leaf ← forsLeafHash H pkSeed idx kappa s.val opening.secret
  -- Step 2: climb from height 0 to the root.
  Merkle.climb (forsNodeHash H pkSeed idx kappa) ⟨0, s.val⟩ leaf opening.path.toList

/-- `Fors.recover(idx, s, openings)`: the FORS public key that the openings lead to.

It is FIPS 205's `fors_pkFromSig`: the trees are recovered in order, tree 0 first, then `T_k`. -/
def forsRecover (pkSeed : PkSeed) (idx : Nat) (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) : m Digest := do
  let roots ← ofFnInOrder FORS_TREES fun kappa =>
    treeRecover H pkSeed idx kappa leaves[kappa] openings[kappa]
  forsPkFromRoots H pkSeed idx roots

end EthLib.Cryptography.Sphincs
