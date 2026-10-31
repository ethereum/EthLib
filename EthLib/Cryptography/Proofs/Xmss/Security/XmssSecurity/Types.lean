import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# The leanXMSS model: parameters, types and hash inputs

The model of `Scheme.lean` writes values as bit vectors and hash inputs as byte lists.

Every hash input is byte for byte the one of EthLib's algorithms (`Unforgeability/Translate.lean`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def randomnessBits : Nat := 128
/-- Encoding attempts per signature, `A_max`. -/
def signingAttemptLimit : Nat := 2 ^ 32
/-- The height `h` of each layer's trees. -/
def treeHeight : Nat := 16
/-- Leaf indices `idx < 2^32`, the bottom one-time keys. -/
def lifetime : Nat := 2 ^ (2 * treeHeight)
/-- The top one-time keys, one per bottom tree. -/
def topLifetime : Nat := 2 ^ treeHeight
/-- Bit 23 of `hi`, set on the top layer. -/
def topFlag : Nat := 2 ^ 23
def winternitzBits : Nat := 2
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 58
def targetSum : Nat := 106

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := BitVec randomnessBits
/-- `idx < 2^32`, a bottom one-time key. -/
abbrev LeafIndex := Fin lifetime
/-- `b < 2^16`, a top one-time key and the bottom tree it signs. -/
abbrev TopIndex := Fin topLifetime
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
/-- A chain step; the tweak carries the step, and the chain index follows the value. -/
abbrev ChainStep := Fin (chainLength - 1)
/-- A level of the stored tree, `0` the leaves and `h` the root. -/
abbrev MerkleHeight := Fin (treeHeight + 1)
/-- A level of the authentication path, below the root; the tweak carries `level + 1`. -/
abbrev MerkleLevel := Fin treeHeight
/-- A bottom node within a level, numbered globally across the forest.

Level `l` only uses the values below `2^(2h - l)`. -/
abbrev MerkleNode := Fin lifetime
/-- A top node within a level.

Level `l` only uses the values below `2^(h - l)`. -/
abbrev TopNode := Fin topLifetime
/-- A pair of chains `(2t, 2t + 1)`, `t < 29`: one seed derivation. -/
abbrev ChainPair := Fin (numChains / 2)
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The second 16 bytes of a hash output.

Only the seed derivations of chain starts use them. -/
def upperHash (output : HashOutput) : Digest :=
  output.extractLsb' digestBits digestBits

/-- The half of a derivation that starts chain `n`.

It is the first for even `n` and the second for odd `n`. -/
def hashHalf (n : Nat) (output : HashOutput) : Digest :=
  if n % 2 = 0 then truncateHash output else upperHash output

/-- The pair of chains a chain belongs to. -/
def chainPair (chain : ChainIndex) : ChainPair :=
  ⟨chain.val / 2, by have h : chain.val < 58 := chain.isLt; show chain.val / 2 < 29; omega⟩

/-- The top key of a leaf index, `idx / 2^16`. -/
def topKeyOf (leafIndex : LeafIndex) : TopIndex :=
  ⟨leafIndex.val / 2 ^ treeHeight, by
    have h := leafIndex.isLt
    simp only [lifetime, topLifetime, treeHeight] at h ⊢
    omega⟩

/-- `pk = (root, P)`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- One layer's signature: the randomizer, the `v` chain values and the authentication path. -/
structure LayerSignature where
  randomness : Randomness
  chainValue : ChainIndex → Digest
  authPath : Fin treeHeight → Digest
deriving DecidableEq

/-- Cached chain starts, chain values and Merkle nodes of both layers, and the public parameter.

It also holds the top signature of every bottom tree: its randomizer and codeword.

The top signature is `none` if its grinding failed. -/
structure SecretKey where
  parameter : PublicParameter
  chainStart : LeafIndex → ChainIndex → Digest
  chainValue : LeafIndex → ChainIndex → Digit → Digest
  treeValue : MerkleHeight → MerkleNode → Digest
  topChainStart : TopIndex → ChainIndex → Digest
  topChainValue : TopIndex → ChainIndex → Digit → Digest
  topTreeValue : MerkleHeight → TopNode → Digest
  topSigned : TopIndex → Option (Randomness × Encoding)

/-- The bottom layer's randomizer, chain values and path, then the top layer's signature.

The leaf index travels with the request and the forgery. -/
structure Signature where
  randomness : Randomness
  chainValue : ChainIndex → Digest
  authPath : Fin treeHeight → Digest
  top : LayerSignature
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The address of a hash call: its type `tag < 32` and a chain step `step < 8`.

It also has two fields `hi < 2^24` and `lo < 2^32`. -/
structure TweakFields where
  tag : BitVec 5
  step : BitVec 3
  hi : BitVec 24
  lo : BitVec 32
deriving DecidableEq

/-- The 16 address bytes `lo || hi || (tag + 32 * step) || 0^8`.

`lo` is on 4 bytes and `hi` on 3 bytes, each least significant byte first.

Then come the type byte and 8 zero bytes. -/
def fieldBytes (fields : TweakFields) : List UInt8 :=
  bytesLE 4 fields.lo ++ bytesLE 3 fields.hi ++ bytesLE 1 (fields.step ++ fields.tag) ++ bytesLE 8 0

/-- Convert the four integer fields to their fixed widths. -/
def tweakFields (tag step hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-- The verification hash domains of both layers.

They are `TWEAK_CHAIN = 1`, `TWEAK_LEAF = 2`, `TWEAK_NODE = 3` and `TWEAK_MSG = 12`.

The top layer's `hi` carries `topFlag`. -/
inductive HashDomain where
  | chain (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
  | leaf (leafIndex : LeafIndex)
  | merkle (level : MerkleLevel) (node : MerkleNode)
  | encoding (leafIndex : LeafIndex)
  | topChain (key : TopIndex) (chain : ChainIndex) (step : ChainStep)
  | topLeaf (key : TopIndex)
  | topMerkle (level : MerkleLevel) (node : TopNode)
  | topEncoding (key : TopIndex)
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of a tweak. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain leafIndex _ step => tweakFields 1 step 0 leafIndex
  | .leaf leafIndex => tweakFields 2 0 0 leafIndex
  | .merkle level node => tweakFields 3 0 (level.val + 1) node
  | .encoding leafIndex => tweakFields 12 0 0 leafIndex
  | .topChain key _ step => tweakFields 1 step topFlag key
  | .topLeaf key => tweakFields 2 0 topFlag key
  | .topMerkle level node => tweakFields 3 0 (topFlag + level.val + 1) node
  | .topEncoding key => tweakFields 12 0 topFlag key

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : List UInt8 :=
  fieldBytes (hashDomainFields domain)

/-- What a domain appends after the payload: a chain step's `LE_128(i)`, nothing otherwise.

The chain index is not in the address, so a key's chains share their step addresses. -/
def domainSuffix : HashDomain → HashInput
  | .chain _ chain _ => bytesLE 16 (BitVec.ofNat 128 chain.val)
  | .topChain _ chain _ => bytesLE 16 (BitVec.ofNat 128 chain.val)
  | _ => []

/-- The random-oracle input of every tweakable hash call: `P || A || payload`.

A chain step's payload is its value followed by `domainSuffix`. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ message ++ domainSuffix domain

/-- `P || A(7, 0, 0, leafIndex) || S || m`, the randomizer base `R0` of a message. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex : LeafIndex) (message : Message) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (tweakFields 7 0 0 leafIndex.val) ++
    bytesLE 32 seed ++ bytesLE 32 message

/-- `P || A_rnd(1, b) || S || r_b`, the randomizer base of the top signature of bottom tree `b`. -/
def topRandomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (key : TopIndex) (root : Digest) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (tweakFields 7 0 topFlag key.val) ++
    bytesLE 32 seed ++ bytesLE 16 root

/-- The seed derivations: the parameter (under `P = 0`), and pairs of chain starts.

A pair is the starts of chains `2t` and `2t + 1` of a one-time key of either layer.

They are the two halves of one hash. -/
inductive KeygenDomain where
  | parameter
  | chain (leafIndex : LeafIndex) (pair : ChainPair)
  | topChain (key : TopIndex) (pair : ChainPair)
deriving DecidableEq

/-- `TWEAK_PARAMETER = 5`, `TWEAK_PRF = 0`.

`hi` is the pair, flagged on the top layer, and `lo` is the key. -/
def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0 0
  | .chain leafIndex pair => tweakFields 0 0 pair leafIndex
  | .topChain key pair => tweakFields 0 0 (topFlag + pair) key

/-- `"leanXMSS" || S_0`, the input of the scheme's seed `S`. -/
def seedHashInput (keySeed : MasterSeed) : HashInput :=
  [0x6c, 0x65, 0x61, 0x6e, 0x58, 0x4d, 0x53, 0x53] ++ bytesLE 32 keySeed

/-- `P || A || S`; parameter derivation uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (keygenDomainFields domain) ++ bytesLE 32 seed

/-! ### The target-sum code

`v = 58` digits of `w = 2` bits, the low `2v = 116` bits of the digest.

The code is the words of digit sum `T = 106` whose top `12` bits are zero.

Those bits are the last `6` base-4 digits. -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- The bits above the `v` digits: `128 - 2v = 12`, which a codeword holds at zero. -/
def zeroBits : Nat := digestBits - winternitzBits * numChains

/-- Offset of a two-bit digit. -/
def digitOffset (i : ChainIndex) : Nat := winternitzBits * i.val

/-- `x_i`, the two bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- The top `128 - 2v` bits of a digest. -/
def digestTop (digest : Digest) : BitVec zeroBits :=
  digest.extractLsb' (winternitzBits * numChains) zeroBits

/-- A digest is a codeword when two conditions hold.

Its last `64 - v` base-4 digits, its top 12 bits, are zero.

Its first `v` digits sum to `T`. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if digestTop digest = 0 ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

`Concrete` contains the hash and verification routines.

`Seeded` contains key generation and signing.

Hashing routines work in any monad with access to `HashSpec`.

The experiment samples the master seed and charges every hash call, including repeated calls.

Out-of-range branches only make the definitions total; honest algorithms never reach them. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- Private uniform sampling and the shared hash oracle.

Only hash calls count toward the query budget. -/
abbrev OracleWorld := unifSpec + HashSpec

namespace Concrete

/-- One query to the random oracle `H`. -/
def oracleHash {m : Type → Type} [Monad m] [HasQuery HashSpec m] (input : HashInput) :
    m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

end Concrete

end XmssSecurity
