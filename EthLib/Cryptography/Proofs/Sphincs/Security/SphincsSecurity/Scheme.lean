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

It is SLH-DSA (FIPS 205) on Keccak-256, with WOTS+C one-time keys.

A FORS few-time key sits under every bottom leaf of a hypertree of WOTS+C one-time keys.

## Shape

The key has a height `h` of at most 28: an index has `h` bits.

The key has `d` layers, and every layer below the top has the same height `ℓ`, at least 6.

The top layer has the rest of the height, `h - ℓ (d - 1)`.

Key generation builds the whole top layer.

FORS has `k` trees of height `a`, as in FIPS 205.

## FORS

- A FORS leaf is `F` of a secret, and every secret is one `PRF` call on `SK.seed`.
- A FORS tree is hashed up to its root.
- The FORS public key is `T_k` of the `k` roots, a 16-byte message that the bottom WOTS+C key signs.
- An opening holds, for each tree, the secret of the selected leaf and its `a` path nodes.

## The message digest

- `H_msg` makes `ceil(m / 32)` calls on `R || PK.seed || PK.root || M || BE_32(i)`.
- These calls hash the message `M` itself: only `PRF_msg` frames it as `M'`.
- The digest splits as in Algorithm 19 of FIPS 205.
- The FORS leaves come first, read most significant bit first.
- The tree index and the bottom leaf follow, as big-endian integers.

## Layers

At every layer, a WOTS+C key with 64 chains of length 4 and target sum 128 signs a 16-byte message.

That message is the FORS public key at the bottom layer, and above it the root of the tree below.

The layers are numbered from the top, so layer 0 is the top layer.

The signer signs them from the bottom up, and stops at the first layer whose counter search fails.

## Keys and hash inputs

The secret key is a 32-byte seed, which is FIPS 205's `SK.seed`.

The public seed is `PK.seed = Trunc_16(H(leanSPHINCS || SK.seed || 0))`.

The secret PRF key is `SK.prf = H(leanSPHINCS || SK.seed || 1)`, all 32 bytes.

An addressed hash input is `PK.seed || ADRS || payload`.

`ADRS` is FIPS 205's 32-byte address, eight big-endian words.

They hold the layer, the tree in three words, the type and the key pair.

The last two words hold the chain or the height, and the hash address or the tree index.

The randomizer is `R = Trunc_16(H(SK.prf || PK.seed || M'))`.

Here `M' = 0x00 || 11 || leanSPHINCS || M` frames the message under the context `leanSPHINCS`.

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

Key generation builds the whole top layer, so every index lands.

The kept subtree of the signer is then the whole top tree. -/
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
  /-- The node indices of the FORS trees fit their 32-bit address word. -/
  forsTrees_le : forsTrees ≤ 64
  /-- A FORS tree has at least two levels. -/
  forsHeight_ge : 2 ≤ forsHeight
  /-- The node indices of a FORS tree fit their 32-bit address word. -/
  forsHeight_le : forsHeight ≤ 12
  /-- Key generation builds the whole top layer, so every index lands. -/
  full : subtreeHeight = totalHeight

export Params (totalHeight numLayers forsTrees forsHeight lowerHeight subtreeHeight signatureLimit)

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
  full := rfl

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
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
abbrev Encoding := ChainIndex → Digit

/-! ### FORS types -/

/-- A FORS tree `κ`. -/
abbrev FTree := Fin forsTrees
/-- A leaf, or a node index at any level, of a FORS tree. -/
abbrev FLeaf := Fin (2 ^ forsHeight)
/-- A hashed level `1` to `a` of a FORS tree, stored as the level minus one.

Level `a` is the root of the tree. -/
abbrev FLevel := Fin forsHeight

/-- The height of a layer: the rest of `h` at the top, and `ℓ` below. -/
def layerHeight (lay : Layer) : Nat := if lay.val = 0 then maxLayerHeight else lowerHeight

/-- The top layer, layer 0. -/
def topLayer : Layer := ⟨0, Params.numLayers_pos⟩

/-- The number of index bits below a layer: the sum of the heights of the layers under it. -/
def heightBelow (lay : Layer) : Nat := lowerHeight * (numLayers - 1 - lay.val)

/-- The second 16 bytes of a hash output, bytes 16 to 31.

The step of the randomizer walk uses them, and a full key never takes that step. -/
def upperHash (output : HashOutput) : Digest :=
  output.extractLsb' digestBits digestBits

/-!
### The message digest

The digest is FIPS 205's split of `m` bytes, read from `ceil(m / 32)` calls.
-/

/-- The fields of the message digest: an index and the `k` leaf indices, `h + k a` bits. -/
def messageDigestBits : Nat := totalHeight + forsTrees * forsHeight

/-- The height of the bottom layer, whose leaf is the last field of the digest. -/
def bottomHeight : Nat := layerHeight ⟨numLayers - 1, Nat.sub_lt Params.numLayers_pos Nat.one_pos⟩

/-- The bytes of the FORS leaves, of the tree index and of the bottom leaf, `m` bytes in all.

These are the byte counts of Algorithm 19 of FIPS 205. -/
def mdBytes : Nat := (forsTrees * forsHeight + 7) / 8
def treeIndexBytes : Nat := (totalHeight - bottomHeight + 7) / 8
def leafIndexBytes : Nat := (bottomHeight + 7) / 8
def digestBytes : Nat := mdBytes + treeIndexBytes + leafIndexBytes

/-- The number of `H_msg` calls: `ceil(m / 32)`. -/
def digestCalls : Nat := (digestBytes + 31) / 32

theorem digestCalls_pos : 0 < digestCalls := by
  have hk := Params.forsTrees_pos
  have ha := Params.forsHeight_ge
  have : 2 ≤ forsTrees * forsHeight := le_trans ha (Nat.le_mul_of_pos_left _ hk)
  unfold digestCalls digestBytes mdBytes
  omega

/-- A digest call. -/
abbrev DigestCall := Fin digestCalls

/-- The first digest call. -/
def firstCall : DigestCall := ⟨0, digestCalls_pos⟩

/-- The fields of a digest, packed least significant first.

The index is in the low `h` bits, and the leaf of tree `κ` starts at bit `h + a κ`. -/
abbrev MessageDigest := BitVec messageDigestBits

/-- The outputs of the digest calls as one number, call 0 in the low 256 bits. -/
def digestValue (outputs : DigestCall → HashOutput) : Nat :=
  ∑ call : DigestCall, (outputs call).toNat * 2 ^ (hashOutputBits * call.val)

/-- The FORS key of an instance: the roots of its `k` trees.

`T_k` compresses them into the FORS public key. -/
abbrev ForsKey := FTree → Digest

/-- A public key `PK.seed || PK.root`: the root of the top tree and the public seed. -/
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

/-- Serialize a bit vector into a fixed number of bytes, most significant byte first.

This is FIPS 205's `toByte`, for the address words and the counters. -/
def bytesBE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * (byteCount - 1 - index.val)) 8)

/-! ### Reading the digest, as Algorithm 19 of FIPS 205 does -/

/-- The bytes of the digest calls, call 0 first, each in the output order of the hash. -/
def digestOutputBytes (outputs : DigestCall → HashOutput) : List UInt8 :=
  (List.ofFn fun call => bytesLE 32 (outputs call)).flatten

/-- Bit `p` of a byte string read most significant bit first, as `base_2b` reads it. -/
def msbBit (bytes : List UInt8) (p : Nat) : Nat :=
  (bytes.getD (p / 8) 0).toNat / 2 ^ (7 - p % 8) % 2

/-- The `width` bits from bit `offset`, most significant first: one value of `base_2b`. -/
def msbField (bytes : List UInt8) (offset width : Nat) : Nat :=
  (List.range width).foldl (fun value j => 2 * value + msbBit bytes (offset + j)) 0

/-- The big-endian integer of a byte string, FIPS 205's `toInt`. -/
def beInt (bytes : List UInt8) : Nat :=
  bytes.foldl (fun value byte => 256 * value + byte.toNat) 0

/-- The index of a digest: the tree index from its middle bytes, then the bottom leaf.

The bottom leaf comes from its last bytes, and each field is cut to its number of bits. -/
def digestIndexValue (bytes : List UInt8) : Nat :=
  beInt ((bytes.drop mdBytes).take treeIndexBytes) % 2 ^ (totalHeight - bottomHeight) *
      2 ^ bottomHeight +
    beInt ((bytes.drop (mdBytes + treeIndexBytes)).take leafIndexBytes) % 2 ^ bottomHeight

/-- The fields of a digest, packed as the message digest lays them out.

The index comes first, then the leaf of each tree, `base_2b(md, a, k)`. -/
def digestFieldsValue (bytes : List UInt8) : Nat :=
  digestIndexValue bytes +
    ∑ κ : FTree,
      msbField bytes (forsHeight * κ.val) forsHeight * 2 ^ (totalHeight + forsHeight * κ.val)

/-- The message digest of the digest calls: their fields. -/
def truncateMessageDigest (outputs : DigestCall → HashOutput) : MessageDigest :=
  BitVec.ofNat messageDigestBits (digestFieldsValue (digestOutputBytes outputs))

/-- FIPS 205's address `ADRS`: the layer, counted from the bottom, the tree and the type.

Then come the key pair, the chain or the height, and the hash address or the tree index. -/
structure TweakFields where
  layer : BitVec 32
  tree : BitVec 96
  tag : BitVec 32
  keyPair : BitVec 32
  height : BitVec 32
  index : BitVec 32
deriving DecidableEq

/-- The 32 address bytes: eight big-endian words, of which the tree takes three. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  bytesBE 4 fields.layer ++ bytesBE 12 fields.tree ++ bytesBE 4 fields.tag ++
    bytesBE 4 fields.keyPair ++
    bytesBE 4 fields.height ++ bytesBE 4 fields.index

/-- An address from its integer fields. -/
def tweakFields (tag layer tree keyPair height index : Nat) : TweakFields :=
  ⟨BitVec.ofNat 32 layer, BitVec.ofNat 96 tree, BitVec.ofNat 32 tag, BitVec.ofNat 32 keyPair,
    BitVec.ofNat 32 height, BitVec.ofNat 32 index⟩

/-- The layer word of a layer, which counts the layers from the bottom. -/
def layerByte (lay : Layer) : Nat := numLayers - 1 - lay.val

/-- The address of a call in a tree of a layer. -/
def treeFields (tag : Nat) (lay : Layer) (tree : TreeIndex) (keyPair height index : Nat) :
    TweakFields :=
  tweakFields tag (layerByte lay) tree.val keyPair height index

/-! ### FORS addresses -/

/-- The address of a FORS call of an instance, with the given type.

It holds the bottom layer, the tree of the bottom key and, as the key pair, its leaf. -/
def forsFields (tag : Nat) (index : Index) (height treeIdx : Nat) : TweakFields :=
  tweakFields tag 0 (index.val / 2 ^ bottomHeight) (index.val % 2 ^ bottomHeight) height treeIdx

/-- The tree index of a node of FORS tree `κ`: `κ 2^(a - z) + j` for node `j` at height `z`.

This is FIPS 205's index, which counts across the trees.

No algorithm computes a node index past the width of its tree.

Such an index is placed above `2^31`, so that every position has an address of its own. -/
def forsTreeIndex (κ : FTree) (height node : Nat) : Nat :=
  if node < 2 ^ (forsHeight - height) then κ.val * 2 ^ (forsHeight - height) + node
  else 2 ^ 31 + κ.val * 2 ^ 12 + node

/-- The domains of the hashes that verification computes.

Seed derivations have domains of their own.

A FORS node domain at `level` names a node at tree level `level + 1`.

At the last level, that node is the root of the tree. -/
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
      (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | forsLeaf (index : Index) (κ : FTree) (leaf : FLeaf)
  | forsNode (index : Index) (κ : FTree) (level : FLevel) (node : FLeaf)
  | forsRoots (index : Index)
deriving DecidableEq

/-- The address of a hash domain, with the types of FIPS 205.

- `WOTS_HASH = 0` holds the chain and the position that a step leaves.
- `WOTS_PK = 1` is the one-time leaf.
- `TREE = 2` holds the height and the node index.
- `FORS_TREE = 3` holds the height and the tree index.
- `FORS_ROOTS = 4` is the FORS public key.
- Type 7 is the encoding of WOTS+C. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay tree leaf chainIdx step => treeFields 0 lay tree leaf chainIdx step
  | .leaf lay tree leaf => treeFields 1 lay tree leaf 0 0
  | .node lay tree level nodeIdx => treeFields 2 lay tree 0 level nodeIdx
  | .encoding lay tree leaf => treeFields 7 lay tree leaf 0 0
  | .forsLeaf index κ leaf => forsFields 3 index 0 (forsTreeIndex κ 0 leaf.val)
  | .forsNode index κ level node =>
      forsFields 3 index (level.val + 1) (forsTreeIndex κ (level.val + 1) node.val)
  | .forsRoots index => forsFields 4 index 0 0

/-- The 32 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The input `PK.seed || ADRS || payload` of every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ message

/-- The seed derivations, one `PRF` call each.

- A one-time derivation gives the start of one chain of the key at a leaf, with type 5.
- A FORS derivation gives the secret of one leaf of a tree of an instance, with type 6.
- A surrogate is a sibling above the kept subtree, with a type of its own.

No key of the parameters computes a surrogate. -/
inductive KeygenDomain where
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
  | fors (index : Index) (κ : FTree) (leaf : FLeaf)
  | surrogate (level : Fin maxLayerHeight)
deriving DecidableEq

def keygenDomainFields : KeygenDomain → TweakFields
  | .ots lay tree leaf chain => treeFields 5 lay tree leaf chain 0
  | .fors index κ leaf => forsFields 6 index 0 (forsTreeIndex κ 0 leaf.val)
  | .surrogate level => tweakFields 8 0 0 0 level 0

/-- The 11 ASCII bytes of `leanSPHINCS`, the tag of the key-seed hashes and the message context. -/
def seedTag : HashInput := [0x6c, 0x65, 0x61, 0x6e, 0x53, 0x50, 0x48, 0x49, 0x4e, 0x43, 0x53]

/-- The 44-byte input `leanSPHINCS || SK.seed || d` of a key-seed hash.

Domain `d = 0` gives `PK.seed`, the first 16 bytes of the hash.

Domain `d = 1` gives `SK.prf`, all 32 bytes of the hash.

This input has no public seed and no address. -/
def keySeedInput (seed : MasterSeed) (domain : Nat) : HashInput :=
  seedTag ++ bytesLE 32 seed ++ [UInt8.ofNat domain]

/-- The input `PK.seed || ADRS || SK.seed` of the seed derivation `PRF(PK.seed, SK.seed, ADRS)`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (keygenDomainFields domain) ++ bytesLE 32 seed

/-- The 45-byte framed message `M' = 0x00 || 11 || leanSPHINCS || M`.

This is how pure SLH-DSA frames a message under the context `leanSPHINCS`.

FIPS 205 gives this framing in Algorithms 22 and 24. -/
def framedMessage (message : Message) : HashInput :=
  [0x00, 0x0b] ++ seedTag ++ bytesLE 32 message

/-- The 93-byte input `SK.prf || PK.seed || M'` of `PRF_msg(SK.prf, PK.seed, M')`.

Its hash gives the randomizer of a message. -/
def randomizerHashInput (prf : HashOutput) (parameter : PublicParameter) (message : Message) :
    HashInput :=
  bytesLE 32 prf ++ bytesLE 16 parameter ++ framedMessage message

/-- The 84-byte input `R || PK.seed || PK.root || M || BE_32(i)` of call `i` of `H_msg`.

The 32-byte message is not framed here. -/
def messageDigestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) : HashInput :=
  bytesLE 16 randomness ++ bytesLE 16 parameter ++ bytesLE 16 root ++ bytesLE 32 message ++
    bytesBE 4 (BitVec.ofNat 32 call.val)

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

/-- The bit offset of a two-bit digit.

`base_2b` reads the most significant bits of each byte first.

So digit `i` starts at bit `6 - 2 (i mod 4)` of byte `i / 4`. -/
def digitOffset (i : ChainIndex) : Nat := 8 * (i.val / 4) + 6 - winternitzBits * (i.val % 4)

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

/-- The FORS key as the bytes `root_0 || ... || root_{k-1}`, which `T_k` compresses. -/
def rootsPayload (roots : ForsKey) : HashInput :=
  (List.ofFn roots).flatMap (bytesLE 16)

/-- The 16-byte message of a WOTS+C key.

It is the FORS public key at the bottom layer, and the root of the tree below above it. -/
def rootPayload (root : Digest) : HashInput := bytesLE 16 root

/-- The encoding of `M` with counter `c`: hash `M || BE_32(c)` under the encoding address.

Then decode the digest.

The input `PK.seed || ADRS || M || BE_32(c)` has 68 bytes. -/
def encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (message ++ bytesBE 4 counter)
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

/-- The root of a FORS tree that an opening reaches: the leaf, folded over `a` levels. -/
def treeRecover (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (opening : TreeOpening) : m Digest := do
  let value ← forsLeafHash parameter index κ leaf opening.secret
  forsFold parameter index κ leaf opening.path forsHeight value

/-- The roots of the FORS trees that an opening reaches. -/
def forsRecover (parameter : PublicParameter) (index : Index) (leaves : FTree → FLeaf)
    (opening : FTree → TreeOpening) : m ForsKey :=
  sequenceFin fun κ => treeRecover parameter index κ (leaves κ) (opening κ)

/-- The FORS public key `T_k` of the roots, which the bottom WOTS+C key signs. -/
def forsPublicKey (parameter : PublicParameter) (index : Index) (roots : ForsKey) : m Digest :=
  tweakableHash parameter (.forsRoots index) (rootsPayload roots)

/-! ### The message digest -/

/-- One untruncated digest call. -/
def messageDigestCall (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) : m HashOutput :=
  oracleHash (messageDigestInput parameter root message randomness call)

/-- The index: the low `h` bits of the digest. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin

/-- The low `h` bits of the first digest call, which the randomizer search tests for landing.

In the digest layout of FIPS 205, these are bits of the FORS leaves, not the index.

A full key lands every index, so the test always passes and the signer signs at `R`. -/
def blockIndex (first : HashOutput) : Index :=
  (first.extractLsb' 0 totalHeight).toFin

/-- The message digest `H_msg(R, PK.seed, PK.root, M)`.

It reads the calls as Algorithm 19 of FIPS 205 reads them. -/
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

The WOTS+C key of each layer signs the message: the FORS public key at the bottom, a root above it.

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

/-- Verification `Ver(pk, m, sigma)`: recompute the digest and recover the FORS public key.

Then walk the layers, recovering each one-time leaf and folding its path, and compare the root. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let roots ← forsRecover publicKey.parameter index (digestLeaves digest) signature.fors
  let forsKey ← forsPublicKey publicKey.parameter index roots
  let some root ← verifyLayers publicKey.parameter index signature numLayers (rootPayload forsKey)
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

/-- Run the `n` computations from the last index down, and stop on the first failure.

Each computation starts from the state that the one before it returned. -/
def sequenceThread {σ : Type} : {n : Nat} → {α : Fin n → Type} →
    ((i : Fin n) → σ → m (Option (α i × σ))) → σ → m (Option ((i : Fin n) → α i))
  | 0, _, _, _ => pure (some fun i => Fin.elim0 i)
  | _ + 1, α, computation, state => do
      let some (last, next) ← computation (Fin.last _) state | return none
      let some init ← sequenceThread (α := fun i => α i.castSucc) (fun i => computation i.castSucc)
        next | return none
      return some (Fin.lastCases last init)

/-- The path of a layer signature as the tree fold reads it, zero outside the layer's height. -/
def partPath {lay : Layer} (part : LayerSignature lay) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then part.path ⟨level, hlevel⟩ else 0

/-- The root of its tree that a layer signature of a message reaches, as the verifier computes it.

It is the one-time leaf, folded up the path. -/
def layerRecover (parameter : PublicParameter) (index : Index) (lay : Layer) (message : HashInput)
    (part : LayerSignature lay) : m (Option Digest) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let some value ← otsLeaf parameter lay tree leaf message part.counter part.chainValues
    | return none
  let root ← treeFold parameter lay tree leaf (partPath part) (layerHeight lay) value
  return some root

attribute [irreducible] verify

end Concrete

/-! ### Pruning -/

section Pruning

/-- The position `s` of the kept subtree: `PK.seed` modulo `2^(h - b)`.

It is 0, since `b = h` for every key. -/
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

/-- One seed derivation `PRF(PK.seed, SK.seed, ADRS)`, the first 16 bytes of its hash. -/
def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

/-- The step of a randomizer walk, with its lowest bit set.

So the walk `R0 + i * step` does not return to `R0` in fewer than `2^128` steps. -/
def walkStep (half : Randomness) : Randomness := half ||| 1#digestBits

/-- The randomizer hash `PRF_msg(SK.prf, PK.seed, M')`, one hash per message.

Its first half is the randomizer `R`.

Its second half gives the step of a walk, which a full key never takes. -/
def deriveRandomizer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (prf : HashOutput) (parameter : PublicParameter)
    (message : Message) : m (Randomness × Randomness) := do
  let output ← Concrete.oracleHash (randomizerHashInput prf parameter message)
  return (truncateHash output, walkStep (upperHash output))

/-- The public seed `PK.seed`, the first 16 bytes of the hash of `leanSPHINCS || SK.seed || 0`. -/
def derivePublicSeed {m : Type → Type} [Monad m] [HasQuery HashSpec m] (seed : MasterSeed) :
    m PublicParameter := do
  return truncateHash (← Concrete.oracleHash (keySeedInput seed 0))

/-- The secret PRF key `SK.prf`, the whole hash of `leanSPHINCS || SK.seed || 1`. -/
def derivePrf {m : Type → Type} [Monad m] [HasQuery HashSpec m] (seed : MasterSeed) :
    m HashOutput :=
  Concrete.oracleHash (keySeedInput seed 1)

/-- A uniform 32-byte seed. -/
noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

open Concrete

/-- The secret key, what the signer reads: `SK.seed`, `SK.prf`, `PK.seed` and `PK.root`. -/
structure SecretKey where
  seed : MasterSeed
  prf : HashOutput
  parameter : PublicParameter
  root : Digest

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The starts of the 64 chains of the one-time key at a leaf, one `PRF` call each. -/
def otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) :=
  sequenceFin fun chainIdx => deriveKey parameter (.ots lay tree leaf chainIdx) seed

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

/-- The surrogate sibling at a level `level >= b`, derived from the seed with address type 8.

Honest calls have `level < h`. -/
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

/-- The secret of one FORS leaf, one `PRF` call. -/
def forsSecret (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (seed : MasterSeed) : m Digest :=
  deriveKey parameter (.fors index κ leaf) seed

/-- A node of a FORS tree at tree level `level`, the root at level `a`. -/
def forsNode (parameter : PublicParameter) (index : Index) (κ : FTree) (seed : MasterSeed) :
    Nat → Nat → m Digest
  | 0, node => do
      let leaf : FLeaf := ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let secret ← forsSecret parameter index κ leaf seed
      forsLeafHash parameter index κ leaf secret
  | level + 1, node => do
      let left ← forsNode parameter index κ seed level (2 * node)
      let right ← forsNode parameter index κ seed level (2 * node + 1)
      if hlevel : level < forsHeight then
        tweakableHash parameter (.forsNode index κ ⟨level, hlevel⟩
          ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) (nodePayload left right)
      else
        pure 0

/-- The FORS public key of an instance: `T_k` of the roots of its trees. -/
def forsKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) : m Digest := do
  let roots ← sequenceFin fun κ => forsNode parameter index κ seed forsHeight 0
  forsPublicKey parameter index roots

/-- The opening of one FORS tree at a leaf: its secret and its path, the sibling at every level. -/
def treeOpen (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (seed : MasterSeed) : m TreeOpening := do
  let secret ← forsSecret parameter index κ leaf seed
  let path ← sequenceFin fun level : Fin forsHeight =>
    forsNode parameter index κ seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return ⟨secret, path⟩

/-- The FORS opening: the opening of every tree. -/
def forsOpen (parameter : PublicParameter) (index : Index) (leaves : FTree → FLeaf)
    (seed : MasterSeed) : m (FTree → TreeOpening) :=
  sequenceFin fun κ => treeOpen parameter index κ (leaves κ) seed

/-- Key generation from `SK.seed`: derive `PK.seed` and `SK.prf`, then build the top root. -/
def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← derivePublicSeed seed
  let prf ← derivePrf seed
  let root ← treeRoot parameter topLayer rootTree seed
  return (⟨root, parameter⟩, ⟨seed, prf, parameter, root⟩)

/-- Key generation: the seed of the key is `SK.seed`. -/
def keygen (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) :=
  keygenFromSeed seed

/-- One attempt of the randomizer search: whether the low `h` bits of the first digest call land.

These bits belong to the FORS leaves, not to the index, and a full key lands every value. -/
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option Index) := do
  let first ← messageDigestCall secretKey.parameter secretKey.root message randomness firstCall
  if Landed secretKey.parameter (blockIndex first) then
    return some (blockIndex first)
  else
    return none

/-- The message of the WOTS+C key at a leaf: the root of the tree below it.

At the bottom layer, it is the FORS public key of the instance below it. -/
def keyMessage (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) : m HashInput :=
  if hbelow : lay.val + 1 < numLayers then do
    let root ← treeRoot parameter ⟨lay.val + 1, hbelow⟩ (childTree lay tree leaf) seed
    return rootPayload root
  else do
    let key ← forsKey parameter (childTree lay tree leaf) seed
    return rootPayload key

/-- The message of the WOTS+C key of a layer on the path of an index. -/
def layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) : m HashInput :=
  keyMessage secretKey.parameter secretKey.seed lay (treeIndexAt index lay) (leafIndexAt index lay)

/-- Sign a message with the WOTS+C key of a layer on the path of an index, and attach its path. -/
def signLayerWith (secretKey : SecretKey) (index : Index) (lay : Layer) (message : HashInput) :
    m (Option (LayerSignature lay)) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let some (counter, values) ← otsSign secretKey.parameter lay tree leaf secretKey.seed message
    | return none
  let path ← treePath secretKey.parameter lay tree secretKey.seed leaf
  return some ⟨counter, values, path⟩

/-- The signature of one layer for its own message, with the message computed from scratch.

The proof reasons about this signature.

The signer computes the same signature without computing the message again. -/
def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    m (Option (LayerSignature lay)) := do
  let message ← layerMessage secretKey index lay
  signLayerWith secretKey index lay message

/-- One layer of the signer, given the value that the layer below computed.

That value is the FORS public key at the bottom layer, and the root of the tree below above it.

The step signs the layer, and below the top layer it recovers the root that the signature reaches.

The layer above signs that root. -/
def layerStep (secretKey : SecretKey) (index : Index) (lay : Layer) (below : Digest) :
    m (Option (LayerSignature lay × Digest)) := do
  let some part ← signLayerWith secretKey index lay (rootPayload below) | return none
  if lay.val = 0 then
    return some (part, below)
  else
    let some root ← layerRecover secretKey.parameter index lay (rootPayload below) part
      | return none
    return some (part, root)

/-- Try the randomizers `R, R + step, R + 2 step` and onwards, and stop at the first that lands. -/
def signDigestLoop (secretKey : SecretKey) (message : Message) (step : Randomness) :
    Nat → Randomness → m (Option (Randomness × Index))
  | 0, _ => pure none
  | attempts + 1, randomness => do
      match ← signAttempt secretKey message randomness with
      | some index => return some (randomness, index)
      | none => signDigestLoop secretKey message step attempts (randomness + step)

/-- Signing, which is deterministic.

1. Derive the randomizer `R` of the message with one hash; a full key lands at the first `R`.
2. Compute the digest, open FORS, and recover the FORS public key from the opening.
3. From the bottom layer up, sign the message of the layer below with WOTS+C and attach the path.
4. Below the top layer, recover the root that the layer above signs.

It returns the signature of the Rust signer.

On every run it makes no more hash calls than the Rust signer, though the calls differ.

Carrying the bound over to the Rust signer needs exactly this. -/
def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let walk ← deriveRandomizer secretKey.prf secretKey.parameter message
  let some (randomness, _) ← signDigestLoop secretKey message walk.2 digestAttemptLimit walk.1
    | return none
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  let index := digestIndex digest
  let opening ← forsOpen secretKey.parameter index (digestLeaves digest) secretKey.seed
  let roots ← forsRecover secretKey.parameter index (digestLeaves digest) opening
  let forsKey ← forsPublicKey secretKey.parameter index roots
  let some layers ← sequenceThread (fun lay below => layerStep secretKey index lay below) forsKey
    | return none
  return some ⟨randomness, opening, layers⟩

end Seeded

end SphincsSecurity
