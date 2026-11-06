module

public import EthLib.Cryptography.Proofs.HashSig.Oracle
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.EvalDist.Sum
public import Mathlib.Data.BitVec

/-!
# leanSPHINCS with FORS: the scheme

This file specifies the hash-based signature scheme that the security proof models.

A FORS few-time key sits under every bottom leaf of a hypertree of WOTS+C one-time keys.

## Shape

The key has a height `h` of at most 28: an index has `h` bits.

The key has `d` layers, and every layer below the top has the same height `ℓ`, at least 6.

The top layer has the rest of the height, `h - ℓ (d - 1)`.

A pruned key has one layer, and key generation builds only a subtree of `2^b` of its leaves.

A full key (`b = h`) and a layered key build the whole top layer.

FORS has `k` trees of height `a`.

## FORS

- A FORS leaf is the hash of a secret.
- One seed hash gives the secrets of leaves `2t` and `2t + 1`, as its two 16-byte halves.
- A FORS tree is hashed up to level `a - 1` only, so no hash joins its two top nodes into a root.
- The FORS key is the `2k` top nodes, and the bottom WOTS+C key signs them with no further hash.
- The message digest has `h + k a` bits: the index, then the `k` leaf indices.
- The digest comes from `ceil((h + k a) / 256)` digest calls with distinct addresses.
- The index lies in the first digest call.
- An opening holds, for each tree, the secret of the selected leaf and its `a` path nodes.
- The last path node is the other top node, and the verifier orders the two top nodes by index.

## Layers

At every layer, a WOTS+C key with 64 chains of length 4 and target sum 128 signs a message.

That message is the FORS key at the bottom layer, and above it the 16-byte root of the tree below.

The layers are numbered from the top, so layer 0 is the top layer.

The signer signs them from the bottom up, and stops at the first layer whose counter search fails.

## Hash inputs

Key generation first hashes the seed `S0` into the scheme seed `S = H(leanSPHINCS || S0)`.

Every other hash input is `P || A || payload`, so the payload starts at byte 32.

Here `P` is the 16-byte public parameter and `A` is the 16-byte address of the call.

The address starts with a 32-bit field `lo` and a 24-bit field `hi`.

One byte holds the type and the chain step, and one byte holds the layer, counted from the bottom.

Four bytes hold the tree, and three zero bytes end the address.

FORS hashes use the types 14 (secret derivation), 15 (leaf) and 17 (node).

They hold the index in `lo`, and the tree and the position in `hi`.

The message digest hashes `m || R`, without the root, since `P` binds the key.

The randomizer hash takes `S || m`.

The model is one random oracle on these inputs.

Only the verification costs depend on the concrete hash function.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

export EthLib.Cryptography.HashSig
  (digestBits hashOutputBits HashInput HashOutput HashSpec OracleWorld truncateHash)

/-! ## The instance: parameters, types, and hash-input layout -/

def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def counterBits : Nat := 32
def winternitzBits : Nat := 2
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 64
def targetSum : Nat := 128
/-- The number of randomizers that the signer tries per signature. -/
def digestAttemptLimit : Nat := 2 ^ 32
/-- The number of encoding counters that the signer tries per one-time signature. -/
def encodingAttemptLimit : Nat := 2 ^ 32

/-- The shape and the lifetime of a key.

The key is a hypertree, and one layer gives a single tree.

Its top layer keeps a subtree: the kept instances are the indices that land in it.

A full or a layered key keeps all indices. -/
class Params where
  /-- `h`, the height of the key: the number of bits of an index. -/
  totalHeight : Nat
  /-- `d`, the number of layers. -/
  numLayers : Nat
  /-- `k`, the number of FORS trees. -/
  forsTrees : Nat
  /-- `a`, the height of a FORS tree. -/
  forsHeight : Nat
  /-- `ℓ`, the height of every layer below the top one. -/
  lowerHeight : Nat
  /-- `b`, the height of the kept subtree of the top layer. -/
  subtreeHeight : Nat
  /-- `N`, the largest number of messages that the key signs. -/
  signatureLimit : Nat
  numLayers_pos : 0 < numLayers
  lowerHeight_ge : 6 ≤ lowerHeight
  /-- The top layer is at least as tall as the others. -/
  lower_le : lowerHeight * numLayers ≤ totalHeight
  /-- The index fields fit the digest and the 32-bit address fields. -/
  totalHeight_le : totalHeight ≤ 28
  /-- The kept subtree lies in the top layer. -/
  below_le : lowerHeight * (numLayers - 1) ≤ subtreeHeight
  subtreeHeight_le : subtreeHeight ≤ totalHeight
  forsTrees_pos : 0 < forsTrees
  /-- The tree fits the 6 bits of the address field `hi` that hold it. -/
  forsTrees_le : forsTrees ≤ 64
  /-- A tree has two top nodes below its root. -/
  forsHeight_ge : 2 ≤ forsHeight
  /-- A level and a node of a tree fit the rest of `hi`. -/
  forsHeight_le : forsHeight ≤ 12

export Params (totalHeight numLayers forsTrees forsHeight lowerHeight subtreeHeight signatureLimit)

/-- A pruned key: one tree of height `h`, of which key generation builds a subtree of height `b`.

The public parameter places that subtree, and `b = h` gives the full key.

FORS has `k` trees of height `a`, and the key signs at most `N` messages.

With one layer, the height of the lower layers plays no role, and it is set to 6. -/
abbrev Params.pruned (h b k a N : Nat) (hh : h ≤ 28 := by decide) (h6 : 6 ≤ h := by decide)
    (hb : b ≤ h := by decide) (hk : 0 < k := by decide) (hk' : k ≤ 64 := by decide)
    (ha : 2 ≤ a := by decide) (ha' : a ≤ 12 := by decide) : Params where
  totalHeight := h
  numLayers := 1
  forsTrees := k
  forsHeight := a
  lowerHeight := 6
  subtreeHeight := b
  signatureLimit := N
  numLayers_pos := Nat.one_pos
  lowerHeight_ge := Nat.le_refl 6
  lower_le := h6
  totalHeight_le := hh
  below_le := Nat.zero_le b
  subtreeHeight_le := hb
  forsTrees_pos := hk
  forsTrees_le := hk'
  forsHeight_ge := ha
  forsHeight_le := ha'

/-- A layered key: `d` layers of total height `h`, with the layers below the top of height `ℓ`.

The top layer has the rest, `h - ℓ (d - 1)`, and key generation builds all of it.

FORS has `k` trees of height `a`, and the key signs at most `N` messages. -/
abbrev Params.layered (h d ℓ k a N : Nat) (hd : 0 < d := by decide) (hℓ : 6 ≤ ℓ := by decide)
    (hle : ℓ * d ≤ h := by decide) (hh : h ≤ 28 := by decide) (hk : 0 < k := by decide)
    (hk' : k ≤ 64 := by decide) (ha : 2 ≤ a := by decide) (ha' : a ≤ 12 := by decide) : Params where
  totalHeight := h
  numLayers := d
  forsTrees := k
  forsHeight := a
  lowerHeight := ℓ
  subtreeHeight := h
  signatureLimit := N
  numLayers_pos := hd
  lowerHeight_ge := hℓ
  lower_le := hle
  totalHeight_le := hh
  below_le := Nat.le_trans (Nat.mul_le_mul_left ℓ (Nat.sub_le d 1)) hle
  subtreeHeight_le := Nat.le_refl h
  forsTrees_pos := hk
  forsTrees_le := hk'
  forsHeight_ge := ha
  forsHeight_le := ha'

variable [Params]

/-- The height of the top layer, the tallest one: `h - ℓ (d - 1)`. -/
def maxLayerHeight : Nat := totalHeight - lowerHeight * (numLayers - 1)

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := Digest
abbrev Counter := BitVec counterBits
/-- A layer, with `0` the top one. -/
abbrev Layer := Fin numLayers
/-- An index: the bottom leaf and the FORS instance that a digest selects. -/
abbrev Index := Fin (2 ^ totalHeight)
/-- A tree of a layer, numbered within the layer.

The type holds `2^h` values, which is enough for every layer. -/
abbrev TreeIndex := Fin (2 ^ totalHeight)
/-- A leaf of a tree of a layer.

The type fits the top layer, the tallest, and a layer of height `j` uses the values below `2^j`. -/
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
/-- A pair of chains `(2t, 2t + 1)` of a one-time key, `t < 32`: one seed derivation. -/
abbrev ChainPair := Fin 32
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
abbrev Encoding := ChainIndex → Digit

/-! ### FORS types -/

/-- A FORS tree `κ`. -/
abbrev FTree := Fin forsTrees
/-- A leaf, or a node index at any level, of a FORS tree. -/
abbrev FLeaf := Fin (2 ^ forsHeight)
/-- A pair of leaves `(2t, 2t + 1)` of a FORS tree: one seed derivation. -/
abbrev FPair := Fin (2 ^ (forsHeight - 1))
/-- A hashed level `1` to `a - 1` of a FORS tree, stored as the level minus one.

The type also holds level `a`, whose address no algorithm uses. -/
abbrev FLevel := Fin forsHeight

/-- The height of a layer: the rest of `h` at the top, and `ℓ` below. -/
def layerHeight (lay : Layer) : Nat := if lay.val = 0 then maxLayerHeight else lowerHeight

/-- The top layer, layer 0. -/
def topLayer : Layer := ⟨0, Params.numLayers_pos⟩

/-- The number of index bits below a layer: the sum of the heights of the layers under it. -/
def heightBelow (lay : Layer) : Nat := lowerHeight * (numLayers - 1 - lay.val)

/-- The second 16 bytes of a hash output, bytes 16 to 31.

The seed derivations of chain starts and FORS secrets use them, and so does the randomizer walk. -/
def upperHash (output : HashOutput) : Digest :=
  output.extractLsb' digestBits digestBits

/-- The half of a hash output for chain or leaf `n`: the first for even `n`, the second for odd. -/
def hashHalf (n : Nat) (output : HashOutput) : Digest :=
  if n % 2 = 0 then truncateHash output else upperHash output

/-! ### The message digest -/

/-- The message digest has `h + k a` bits: an index and the `k` leaf indices. -/
def messageDigestBits : Nat := totalHeight + forsTrees * forsHeight

/-- The number of digest calls: `ceil((h + k a) / 256)`. -/
def digestCalls : Nat := (messageDigestBits + hashOutputBits - 1) / hashOutputBits

theorem digestCalls_pos : 0 < digestCalls := by
  have hk := Params.forsTrees_pos
  have ha := Params.forsHeight_ge
  unfold digestCalls messageDigestBits hashOutputBits
  have : 1 ≤ forsTrees * forsHeight := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

/-- A digest call. -/
abbrev DigestCall := Fin digestCalls

/-- The first digest call, which holds the index. -/
def firstCall : DigestCall := ⟨0, digestCalls_pos⟩

abbrev MessageDigest := BitVec messageDigestBits

/-- The outputs of the digest calls as one number, call 0 in the low 256 bits. -/
def digestValue (outputs : DigestCall → HashOutput) : Nat :=
  ∑ call : DigestCall, (outputs call).toNat * 2 ^ (hashOutputBits * call.val)

/-- The message digest: the low `h + k a` bits of the concatenated calls. -/
def truncateMessageDigest (outputs : DigestCall → HashOutput) : MessageDigest :=
  BitVec.ofNat messageDigestBits (digestValue outputs)

/-- The FORS key of an instance: the two nodes at level `a - 1` of every tree.

No hash folds it: the WOTS+C encoding hashes the `2k` nodes whole. -/
abbrev ForsKey := FTree → Digest × Digest

/-- A public key: the root of the top tree and the public parameter `P`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- The signature of one layer: the WOTS+C counter, the chain values and the authentication path. -/
structure LayerSignature (lay : Layer) where
  counter : Counter
  chainValues : ChainIndex → Digest
  path : Fin (layerHeight lay) → Digest
deriving DecidableEq

/-- The opening of one FORS tree: the secret of the selected leaf and its `a` path nodes. -/
structure TreeOpening where
  secret : Digest
  path : Fin forsHeight → Digest
deriving DecidableEq

/-- A signature: the randomizer, the FORS opening, and the signature of every layer.

It serializes to `16 + 16 k (a + 1) + 1028 d + 16 h` bytes. -/
structure Signature where
  randomness : Randomness
  fors : FTree → TreeOpening
  layers : (lay : Layer) → LayerSignature lay
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The address of a hash call.

It holds a type below 32, a chain step below 8, the layer counted from the bottom and the tree.

It also holds two fields, `hi` below `2^24` and `lo` below `2^32`. -/
structure TweakFields where
  tag : BitVec 5
  step : BitVec 3
  layer : BitVec 8
  tree : BitVec 32
  hi : BitVec 24
  lo : BitVec 32
deriving DecidableEq

/-- The 16 address bytes `lo || hi || (type + 32 step) || layer || tree || 0^3`.

The fields `lo`, `hi` and the tree take 4, 3 and 4 bytes, least significant byte first. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  bytesLE 4 fields.lo ++ bytesLE 3 fields.hi ++ bytesLE 1 (fields.step ++ fields.tag) ++
    bytesLE 1 fields.layer ++ bytesLE 4 fields.tree ++ bytesLE 3 0

/-- The address of a call outside the hypertree, with layer and tree 0. -/
def tweakFields (tag step hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, 0, 0, BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-- The layer byte of a layer, which counts the layers from the bottom. -/
def layerByte (lay : Layer) : Nat := numLayers - 1 - lay.val

/-- The address of a call in a tree of a layer. -/
def treeFields (tag step : Nat) (lay : Layer) (tree : TreeIndex) (hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, BitVec.ofNat 8 (layerByte lay),
    BitVec.ofNat 32 tree.val, BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-! ### FORS addresses -/

/-- The slot `κ + 64 p` of position `p` in tree `κ` of an instance. -/
def forsSlot (κ : FTree) (position : Nat) : Nat := κ.val + 64 * position

/-- The position of node `node` at level `level` of a tree: `level + 16 node`. -/
def nodePosition (level node : Nat) : Nat := level + 16 * node

/-- The domains of the hashes that verification computes.

Seed derivations have domains of their own.

A FORS node domain at `level` names a node at tree level `level + 1`.

The scheme hashes the levels 1 to `a - 1`, and no algorithm uses the address of a root. -/
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
      (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | forsLeaf (index : Index) (κ : FTree) (leaf : FLeaf)
  | forsNode (index : Index) (κ : FTree) (level : FLevel) (node : FLeaf)
  | message (call : DigestCall)
deriving DecidableEq

/-- The address of a hash domain.

The types are 1 for a chain step, 2 for a one-time leaf, 3 for a tree node and 4 for an encoding.

The types are 15 for a FORS leaf, 17 for a FORS node and 12 for a digest call.

In a tree, `lo` is the leaf or the node index, and `hi` is the chain or the node level.

A chain step also carries its step, and a hash of the hypertree carries its layer and its tree.

In a FORS instance, `lo` is the index.

There `hi` is `κ + 64 leaf` for a leaf, and `κ + 64 (j + 16 node)` for a node at tree level `j`.

A digest call carries its number in `hi`. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay tree leaf chainIdx step => treeFields 1 step lay tree chainIdx leaf
  | .leaf lay tree leaf => treeFields 2 0 lay tree 0 leaf
  | .node lay tree level nodeIdx => treeFields 3 0 lay tree level nodeIdx
  | .encoding lay tree leaf => treeFields 4 0 lay tree 0 leaf
  | .forsLeaf index κ leaf => tweakFields 15 0 (forsSlot κ leaf.val) index
  | .forsNode index κ level node =>
      tweakFields 17 0 (forsSlot κ (nodePosition (level.val + 1) node.val)) index
  | .message call => tweakFields 12 0 call.val 0

/-- The exact 16 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The input `P || A || payload` of every tweakable hash call and of every digest call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ message

/-- The input `P || A || S || m` of the randomizer hash of a message, with address type 7. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes ⟨7#5, 0#3, 0#8, 0#32, 0#24, 0#32⟩ ++
    bytesLE 32 seed ++ bytesLE 32 message

/-- The pair of chains a chain of a one-time key belongs to. -/
def chainPair (chain : ChainIndex) : ChainPair :=
  ⟨chain.val / 2, by have h : chain.val < 64 := chain.isLt; omega⟩

/-- The pair of leaves a leaf of a FORS tree belongs to. -/
def leafPair (leaf : FLeaf) : FPair :=
  ⟨leaf.val / 2, by
    have h := leaf.isLt
    have ha := Params.forsHeight_ge
    have : 2 ^ forsHeight = 2 * 2 ^ (forsHeight - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    omega⟩

/-- The seed derivations, one hash each.

A one-time derivation gives the starts of chains `2t` and `2t + 1` of the key at a leaf.

A FORS derivation gives the secrets of leaves `2t` and `2t + 1` of a tree of an instance.

These values are the two 16-byte halves of the hash.

The parameter and a surrogate are the first 16 bytes of their hash. -/
inductive KeygenDomain where
  | parameter
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (pair : ChainPair)
  | fors (index : Index) (κ : FTree) (pair : FPair)
  | surrogate (level : Fin maxLayerHeight)
deriving DecidableEq

/-- The address of a seed derivation.

The types are 5 for the parameter, 0 for a one-time derivation and 13 for a surrogate.

The type is 14 for the secrets of a pair of FORS leaves.

A one-time derivation holds the chain pair in `hi`, the leaf in `lo`, the layer and the tree.

A FORS derivation holds the tree and the leaf pair in `hi` and the index in `lo`.

A surrogate holds its level in `hi`. -/
def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0 0
  | .ots lay tree leaf pair => treeFields 0 0 lay tree pair leaf
  | .fors index κ pair => tweakFields 14 0 (forsSlot κ pair.val) index
  | .surrogate level => tweakFields 13 0 level 0

/-- The 11 ASCII bytes of `leanSPHINCS`, the tag of the scheme seed. -/
def seedTag : HashInput := [0x6c, 0x65, 0x61, 0x6e, 0x53, 0x50, 0x48, 0x49, 0x4e, 0x43, 0x53]

/-- The 43-byte input `leanSPHINCS || S0`, whose hash is the scheme seed `S`.

Every seed derivation uses `S`.

This input has no parameter and no address. -/
def schemeSeedInput (seed : MasterSeed) : HashInput :=
  seedTag ++ bytesLE 32 seed

/-- The input `P || A || S` of a seed derivation.

The derivation of the parameter uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (keygenDomainFields domain) ++ bytesLE 32 seed

/-!
### The target-sum code

A digest splits into `v = 64` digits of `w = 2` bits.

The code is the set of words with digit sum `T = 128`.
-/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- The bit offset of a two-bit digit. -/
def digitOffset (i : ChainIndex) : Nat := winternitzBits * i.val

/-- The digits `x_i` of a digest, two bits each from the low end. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- A digest decodes exactly when its 64 digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if Valid (digestEncoding digest) then some (digestEncoding digest) else none

end TargetSum

/-!
## The algorithms

The hash and verification routines come first, then key generation and signing.

The hashing routines work in any monad that can query the hash.
-/

namespace Concrete

export EthLib.Cryptography.HashSig (oracleHash)

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The tweakable hash `Th(P, A, M)`: the first 16 bytes of `H(P || A || M)`. -/
def tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-! ### The index -/

/-- The tree of a layer on the path of an index: the index bits above the layer. -/
def treeIndexAt (index : Index) (lay : Layer) : TreeIndex :=
  ⟨index.val / 2 ^ (heightBelow lay + layerHeight lay),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

theorem layerHeight_le (lay : Layer) : layerHeight lay ≤ maxLayerHeight := by
  unfold layerHeight
  split
  · exact le_refl _
  · have h1 := Params.lower_le
    have h2 := Params.numLayers_pos
    unfold maxLayerHeight
    have : lowerHeight * numLayers = lowerHeight * (numLayers - 1) + lowerHeight := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega

/-- The child of a leaf: the tree below it, or at the bottom layer the FORS instance below it.

For a layer of height `j`, it is `tree * 2^j + leaf` modulo `2^h`. -/
def childTree (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : TreeIndex :=
  ⟨(tree.val * 2 ^ layerHeight lay + leaf.val) % 2 ^ totalHeight,
    Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The leaf of a layer on the path of an index: the bits of the index in the layer. -/
def leafIndexAt (index : Index) (lay : Layer) : LeafIndex :=
  ⟨index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (layerHeight_le lay))⟩

/-! ### The one-time signature -/

/-- A node index at level `0` read as a leaf index. -/
def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ maxLayerHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Walk `steps` chain steps from position `start`.

The step onto position `p + 1` carries the step number `p`.

A step past the end of the chain gives zero. -/
def chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalk parameter lay tree leaf chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay tree leaf chainIdx ⟨start + steps, hstep⟩)
          (bytesLE 16 previous)
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay tree leaf chainIdx digit.val (chainLength - 1 - digit.val) value

/-- The bytes `pk_0 || ... || pk_{v-1}` of the chain ends. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- The one-time leaf: the hash of the `v` chain ends. -/
def leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay tree leaf) (leafPayload endpoints)

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

/-- The FORS key as bytes: the two top nodes of each of the `k` trees, in order. -/
def rootsPayload (tops : ForsKey) : HashInput :=
  (List.ofFn tops).flatMap fun pair => nodePayload pair.1 pair.2

/-- The message of a WOTS+C key above the bottom layer: the 16-byte root of the tree below. -/
def rootPayload (root : Digest) : HashInput := bytesLE 16 root

/-- The encoding of `M` with counter `c`: hash `M || c` under the encoding address, then decode.

The input has `36 + 32 k` bytes at the bottom layer and 52 bytes above it. -/
def encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (message ++ bytesLE 4 counter)
  return TargetSum.decodeDigest digest

/-- The leaf that the verifier recovers, or nothing if the counter does not encode the message. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (counter : Counter) (values : ChainIndex → Digest) :
    m (Option Digest) := do
  let some encoding ← encode parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value

/-! ### The tree -/

/-- Fold a leaf and a path over `levels` levels of a tree. -/
def treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← treeFold parameter lay tree leaf path levels value
      let sibling := path levels
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload current sibling)

/-! ### FORS -/

/-- A FORS leaf: the hash of its secret. -/
def forsLeafHash (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (secret : Digest) : m Digest :=
  tweakableHash parameter (.forsLeaf index κ leaf) (bytesLE 16 secret)

/-- Fold a FORS leaf and a path over `levels` levels. -/
def forsFold (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (path : Fin forsHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← forsFold parameter index κ leaf path levels value
      if hlevel : levels < forsHeight then
        let sibling := path ⟨levels, hlevel⟩
        let node : FLeaf := ⟨leaf.val / 2 ^ (levels + 1),
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt⟩
        if leaf.val.testBit levels then
          tweakableHash parameter (.forsNode index κ ⟨levels, hlevel⟩ node)
            (nodePayload sibling current)
        else
          tweakableHash parameter (.forsNode index κ ⟨levels, hlevel⟩ node)
            (nodePayload current sibling)
      else
        pure 0

/-- The two top nodes of a tree in index order, from the reached node and the last path node.

The reached node is node 1 exactly when `bit`, the top bit of the leaf index, is set. -/
def orderTops (bit : Bool) (current sibling : Digest) : Digest × Digest :=
  if bit then (sibling, current) else (current, sibling)

/-- The last level of a FORS path, whose node is the other node at level `a - 1`. -/
def topLevel : Fin forsHeight := ⟨forsHeight - 1, by have := Params.forsHeight_ge; omega⟩

/-- The two nodes at level `a - 1` of a FORS tree that an opening reaches.

The verifier folds the leaf over `a - 1` levels, and the last path node is the other top node. -/
def treeRecover (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (opening : TreeOpening) : m (Digest × Digest) := do
  let value ← forsLeafHash parameter index κ leaf opening.secret
  let node ← forsFold parameter index κ leaf opening.path (forsHeight - 1) value
  return orderTops (leaf.val.testBit (forsHeight - 1)) node (opening.path topLevel)

/-- The FORS key that an opening reaches.

No hash joins a tree into a root or the key into one value: the encoding hashes the key whole. -/
def forsRecover (parameter : PublicParameter) (index : Index) (leaves : FTree → FLeaf)
    (opening : FTree → TreeOpening) : m ForsKey :=
  sequenceFin fun κ => treeRecover parameter index κ (leaves κ) (opening κ)

/-! ### The message digest -/

/-- The payload `m || R` of a digest call, so that `P || A || m || R` has 80 bytes.

The root is not hashed, since `P` binds the key, so the root argument is unused. -/
def messageDigestPayload (_root : Digest) (message : Message) (randomness : Randomness) :
    HashInput :=
  bytesLE 32 message ++ bytesLE 16 randomness

/-- One untruncated digest call. -/
def messageDigestCall (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) : m HashOutput :=
  oracleHash (tweakableHashInput parameter (.message call)
    (messageDigestPayload root message randomness))

/-- The index: the low `h` bits of the digest. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin

/-- The index read from the first digest call, which holds it. -/
def blockIndex (first : HashOutput) : Index :=
  (first.extractLsb' 0 totalHeight).toFin

/-- The message digest `Digest(P, m, R)`: the calls, concatenated and cut to `h + k a` bits.

The root is not an input of the hash. -/
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let outputs ← sequenceFin fun call => messageDigestCall parameter root message randomness call
  return truncateMessageDigest outputs

/-- The bit offset `h + a κ` of the leaf index of tree `κ`. -/
def leafOffset (κ : FTree) : Nat := totalHeight + forsHeight * κ.val

/-- The leaf indices of a digest. -/
def digestLeaves (digest : MessageDigest) : FTree → FLeaf := fun κ =>
  (digest.extractLsb' (leafOffset κ) forsHeight).toFin

/-! ### Verification -/

/-- Read a layer's path, returning zero outside its height. -/
def signaturePath (signature : Signature) (lay : Layer) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then (signature.layers lay).path ⟨level, hlevel⟩ else 0

/-- The walk up the layers: with fuel `r + 1` it enters at layer `r`.

The WOTS+C key of each layer signs the message: the FORS key at the bottom, a root above it.

The walk returns the fold of the top layer, which verification compares with the public root. -/
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → HashInput → m (Option Digest)
  | 0, _ => pure none
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        let part := signature.layers lay
        let some value ← otsLeaf parameter lay tree leaf message part.counter part.chainValues
          | return none
        let root ←
          treeFold parameter lay tree leaf (signaturePath signature lay) (layerHeight lay) value
        if remaining = 0 then
          return some root
        else
          verifyLayers parameter index signature remaining (rootPayload root)
      else
        pure none

/-- Verification `Ver(pk, m, sigma)`: recompute the digest and recover the FORS key.

Then walk the layers, recovering each one-time leaf and folding its path, and compare the root. -/

def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let forsKey ← forsRecover publicKey.parameter index (digestLeaves digest) signature.fors
  let some root ← verifyLayers publicKey.parameter index signature numLayers (rootsPayload forsKey)
    | return false
  return decide (root = publicKey.root)

/-! ### Signing -/

/-- The top layer holds one tree, at index `0`. -/
def rootTree : TreeIndex := ⟨0, Nat.two_pow_pos _⟩

/-- Run the `n` computations from the last index down, stopping on the first failure. -/
def sequenceDep : {n : Nat} → {α : Fin n → Type} →
    ((i : Fin n) → m (Option (α i))) → m (Option ((i : Fin n) → α i))
  | 0, _, _ => pure (some fun i => Fin.elim0 i)
  | _ + 1, α, computation => do
      let some last ← computation (Fin.last _) | return none
      let some init ← sequenceDep (α := fun i => α i.castSucc) fun i => computation i.castSucc
        | return none
      return some (Fin.lastCases last init)

/-- Run the layers from the bottom up, stopping on failure. -/
def sequenceLayers {α : Layer → Type}
    (computation : (lay : Layer) → m (Option (α lay))) : m (Option ((lay : Layer) → α lay)) :=
  sequenceDep computation

attribute [irreducible] verify

end Concrete

/-! ### Pruning -/

section Pruning

/-- The position `s` of the kept subtree: the low `h - b` bits of `P`, as a little-endian number.

It is 0 for a full or a layered key. -/
def subtreePosition (parameter : PublicParameter) : Nat :=
  parameter.toNat % 2 ^ (totalHeight - subtreeHeight)

/-- An index lands when it lies in the kept subtree, from `s * 2^b` to `(s + 1) * 2^b - 1`. -/
def Landed (parameter : PublicParameter) (index : Index) : Prop :=
  index.val / 2 ^ subtreeHeight = subtreePosition parameter

instance (parameter : PublicParameter) (index : Index) : Decidable (Landed parameter index) :=
  inferInstanceAs (Decidable (index.val / 2 ^ subtreeHeight = subtreePosition parameter))

/-- The height of the kept part of the tree of a layer.

At the top layer it is `b` minus the index bits below that layer, and below it the whole tree. -/
def keptHeight (lay : Layer) : Nat :=
  if lay.val = 0 then subtreeHeight - heightBelow lay else layerHeight lay

/-- The position of the kept part among the nodes of its level: `s` at the top layer, 0 below. -/
def keptPosition (parameter : PublicParameter) (lay : Layer) : Nat :=
  if lay.val = 0 then subtreePosition parameter else 0

end Pruning

/-- One seed derivation, cut to its first 16 bytes: the parameter and the surrogates. -/
def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

/-- One seed derivation, all 32 bytes.

Its two halves are the starts of two chains or the secrets of two FORS leaves. -/
def deriveOutput {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m HashOutput :=
  Concrete.oracleHash (keygenHashInput parameter domain seed)

/-- The step of a randomizer walk, with its lowest bit set.

So the walk `R0 + i * step` does not return to `R0` in fewer than `2^128` steps. -/
def walkStep (half : Randomness) : Randomness := half ||| 1#digestBits

/-- The randomizer hash of a message: its first half is the base `R0`, its second gives the step. -/
def deriveRandomizer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) : m (Randomness × Randomness) := do
  let output ← Concrete.oracleHash (randomizerHashInput parameter seed message)
  return (truncateHash output, walkStep (upperHash output))

/-- The scheme seed `S`: the whole 32-byte hash of `leanSPHINCS || S0`. -/
def schemeSeed {m : Type → Type} [Monad m] [HasQuery HashSpec m] (seed : MasterSeed) :
    m MasterSeed :=
  Concrete.oracleHash (schemeSeedInput seed)

/-- A uniform 32-byte seed. -/
noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

open Concrete

/-- The secret key: the scheme seed `S`, not the seed `S0` of the key, with `P` and the root. -/
structure SecretKey where
  seed : MasterSeed
  parameter : PublicParameter
  root : Digest

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The starts of the 64 chains of the one-time key at a leaf, from 32 seed derivations.

Chains `2t` and `2t + 1` start at the two halves of derivation `t`. -/
def otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun pair : ChainPair =>
    deriveOutput parameter (.ots lay tree leaf pair) seed
  return fun chainIdx => hashHalf chainIdx.val (outputs (chainPair chainIdx))

/-- The chain ends of the one-time key at a leaf. -/
def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let secrets ← otsSecrets parameter lay tree leaf seed
  sequenceFin fun chainIdx =>
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secrets chainIdx)

/-- Try at most `attempts` counters from `counter` up, and sign with the first that encodes. -/
def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : HashInput) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let secrets ← otsSecrets parameter lay tree leaf seed
          let values ← sequenceFin fun chainIdx =>
            chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val (secrets chainIdx)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf seed message attempts (counter + 1)

/-- The one-time signature: the least counter below `2^32` that encodes, then the chain values. -/
def otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : HashInput) :
    m (Option (Counter × (ChainIndex → Digest))) :=
  otsSignFrom parameter lay tree leaf seed message encodingAttemptLimit 0

/-- A node of the tree, computed from the one-time keys below it. -/
def treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← oneTimePublicKey parameter lay tree leaf seed
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← treeNode parameter lay tree seed level (2 * nodeIdx)
      let right ← treeNode parameter lay tree seed level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)

/-- The surrogate sibling at a level above the kept part, derived from the seed.

A level at or above the height of the top layer gives zero. -/
def surrogate (parameter : PublicParameter) (seed : MasterSeed) (level : Nat) : m Digest :=
  if hlevel : level < maxLayerHeight then deriveKey parameter (.surrogate ⟨level, hlevel⟩) seed
  else pure 0

/-- The node `steps` levels above the kept part: its root folded with `steps` surrogates. -/
def spineNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) :
    Nat → m Digest
  | 0 => treeNode parameter lay tree seed (keptHeight lay) (keptPosition parameter lay)
  | steps + 1 => do
      let below ← spineNode parameter lay tree seed steps
      let sibling ← surrogate parameter seed (keptHeight lay + steps)
      let nodeIdx := keptPosition parameter lay / 2 ^ steps
      if nodeIdx.testBit 0 then
        tweakableHash parameter (.node lay tree (keptHeight lay + steps + 1) (nodeIdx / 2))
          (nodePayload sibling below)
      else
        tweakableHash parameter (.node lay tree (keptHeight lay + steps + 1) (nodeIdx / 2))
          (nodePayload below sibling)

/-- The root of the tree of a layer: the top of the spine.

Below the top layer the kept part is the whole tree, so the spine has no step. -/
def treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : m Digest :=
  spineNode parameter lay tree seed (layerHeight lay - keptHeight lay)

/-- The authentication path of a kept leaf.

It holds nodes of the kept part below the kept height, and surrogates from that level on. -/
def treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) : m (Fin (layerHeight lay) → Digest) :=
  sequenceFin fun level =>
    if level.val < keptHeight lay then
      treeNode parameter lay tree seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      surrogate parameter seed level.val

end Seeded

namespace Seeded

open Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The secret of one FORS leaf, by its own derivation of its pair.

Key generation and signing instead derive each pair once for both of its leaves. -/
def forsSecret (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (seed : MasterSeed) : m Digest := do
  let output ← deriveOutput parameter (.fors index κ (leafPair leaf)) seed
  return hashHalf leaf.val output

/-- A node of a FORS tree at tree level `level`.

A level-1 node derives its pair of leaves once: the two halves of the hash are their secrets. -/
def forsNode (parameter : PublicParameter) (index : Index) (κ : FTree) (seed : MasterSeed) :
    Nat → Nat → m Digest
  | 0, node => do
      let leaf : FLeaf := ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let secret ← forsSecret parameter index κ leaf seed
      forsLeafHash parameter index κ leaf secret
  | 1, node => do
      let left : FLeaf := ⟨2 * node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let right : FLeaf := ⟨(2 * node + 1) % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let output ← deriveOutput parameter (.fors index κ (leafPair left)) seed
      let leftLeaf ← forsLeafHash parameter index κ left (hashHalf 0 output)
      let rightLeaf ← forsLeafHash parameter index κ right (hashHalf 1 output)
      tweakableHash parameter (.forsNode index κ ⟨0, by have := Params.forsHeight_ge; omega⟩
        ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) (nodePayload leftLeaf rightLeaf)
  | level + 2, node => do
      let left ← forsNode parameter index κ seed (level + 1) (2 * node)
      let right ← forsNode parameter index κ seed (level + 1) (2 * node + 1)
      if hlevel : level + 1 < forsHeight then
        tweakableHash parameter (.forsNode index κ ⟨level + 1, hlevel⟩
          ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) (nodePayload left right)
      else
        pure 0

/-- The FORS key of an instance: the two nodes at level `a - 1` of every tree. -/
def forsKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) : m ForsKey :=
  sequenceFin fun κ => do
    let left ← forsNode parameter index κ seed (forsHeight - 1) 0
    let right ← forsNode parameter index κ seed (forsHeight - 1) 1
    return (left, right)

/-- The opening of one tree at a leaf.

One derivation gives the secret and the sibling leaf, the path node at level 0.

The last path node, at level `a - 1`, is the top node that the verifier does not compute. -/
def treeOpen (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (seed : MasterSeed) : m TreeOpening := do
  let output ← deriveOutput parameter (.fors index κ (leafPair leaf)) seed
  let sibling : FLeaf := ⟨Nat.xor leaf.val 1 % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  let siblingLeaf ← forsLeafHash parameter index κ sibling (hashHalf sibling.val output)
  let path ← sequenceFin fun level : Fin forsHeight =>
    if level.val = 0 then pure siblingLeaf
    else forsNode parameter index κ seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return ⟨hashHalf leaf.val output, path⟩

/-- The FORS opening: the opening of every tree. -/
def forsOpen (parameter : PublicParameter) (index : Index) (leaves : FTree → FLeaf)
    (seed : MasterSeed) : m (FTree → TreeOpening) :=
  sequenceFin fun κ => treeOpen parameter index κ (leaves κ) seed

/-- Key generation from the scheme seed `S`: derive the public parameter, then build the root.

The public parameter places the kept subtree, and the root is that of the top layer. -/
def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← deriveKey 0 .parameter seed
  let root ← treeRoot parameter topLayer rootTree seed
  return (⟨root, parameter⟩, ⟨seed, parameter, root⟩)

/-- Key generation: hash the seed `S0` into the scheme seed `S`, then generate from `S`. -/
def keygen (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let master ← schemeSeed seed
  keygenFromSeed master

/-- One attempt of the randomizer search: the index from the first digest call, if it lands. -/
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option Index) := do
  let first ← messageDigestCall secretKey.parameter secretKey.root message randomness firstCall
  if Landed secretKey.parameter (blockIndex first) then
    return some (blockIndex first)
  else
    return none

/-- The message of the WOTS+C key at a leaf: the root of the tree below it.

At the bottom layer it is the FORS key of the instance below it. -/
def keyMessage (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) : m HashInput :=
  if hbelow : lay.val + 1 < numLayers then do
    let root ← treeRoot parameter ⟨lay.val + 1, hbelow⟩ (childTree lay tree leaf) seed
    return rootPayload root
  else do
    let key ← forsKey parameter (childTree lay tree leaf) seed
    return rootsPayload key

/-- The message of the WOTS+C key of a layer on the path of an index. -/
def layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) : m HashInput :=
  keyMessage secretKey.parameter secretKey.seed lay (treeIndexAt index lay) (leafIndexAt index lay)

/-- The signature of one layer: the one-time signature of its message, then its path. -/
def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    m (Option (LayerSignature lay)) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  let some (counter, values) ← otsSign secretKey.parameter lay tree leaf secretKey.seed message
    | return none
  let path ← treePath secretKey.parameter lay tree secretKey.seed leaf
  return some ⟨counter, values, path⟩

/-- Try the randomizers `R, R + step, R + 2 step` and onwards, and stop at the first that lands. -/
def signDigestLoop (secretKey : SecretKey) (message : Message) (step : Randomness) :
    Nat → Randomness → m (Option (Randomness × Index))
  | 0, _ => pure none
  | attempts + 1, randomness => do
      match ← signAttempt secretKey message randomness with
      | some index => return some (randomness, index)
      | none => signDigestLoop secretKey message step attempts (randomness + step)

/-- Signing: derive the base `R0` and the step `delta` of the walk, in one hash of `S` and `m`.

Then walk `R0, R0 + delta` and onwards until the index lands in the kept subtree.

Then compute the digest and open FORS.

At every layer, sign the message of the layer below with WOTS+C and attach the path. -/

def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let walk ← deriveRandomizer secretKey.parameter secretKey.seed message
  let some (randomness, _) ← signDigestLoop secretKey message walk.2 digestAttemptLimit walk.1
    | return none
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  let index := digestIndex digest
  let opening ← forsOpen secretKey.parameter index (digestLeaves digest) secretKey.seed
  let some layers ← sequenceLayers (fun lay => signLayer secretKey index lay) | return none
  return some ⟨randomness, opening, layers⟩

end Seeded

end SphincsSecurity
