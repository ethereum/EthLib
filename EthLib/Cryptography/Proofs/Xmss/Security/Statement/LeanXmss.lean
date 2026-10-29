module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# leanXMSS

The leanXMSS scheme (key generation, signing, verification over a hash oracle `H`), with its
signing requests, forgeries and transcripts.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

/-!
## leanXMSS

The scheme of `crates/signatures/src/lean_xmss`, specified in `doc/lean_xmss`: two layers of XMSS of height 16 over
WOTS+C one-time keys. Key `b` of the top tree signs the root of bottom tree `b`; a leaf index
`idx < 2^32` signs with bottom key `idx`, in bottom tree `idx / 2^16`.

* WOTS+C: 58 chains of 4 positions. A 16-byte digest is read as 64 base-4 digits, little endian; it
  is a codeword when the last 6 digits are zero and the other 58 sum to 106.
* Every hash input is `P || A || payload`: the 16-byte public parameter, the 16-byte address
  `lo (4 bytes) || hi (3 bytes) || (type + 32 step) || 0^8`, then the payload. The top layer sets
  bit 23 of `hi`. A chain step's address carries the step but not the chain, whose index follows the
  value in the payload.
* `H` is the leanVM hash, Keccak-256 on the bytes of its input, a query (`HashSpec`) the model
  answers: in the end statement (the last section) Keccak-256 over the random permutation.
* The secret key is a 32-byte seed `S_0`. Every secret derives from `S = H("leanXMSS" || S_0)`, all
  32 bytes, and the signer keeps `S`.
* Signing a message `M` with key `e` of layer `l`: `R0 = Th(P, A_rnd(l, e), S || M)`, then the least
  `c < 2^32` such that `Th(P, A_msg(l, e), M || (R0 + c))` is a codeword.
-/

namespace LeanXmss

/-! ### What leanXMSS and leanSPHINCS share

The tweakable hash `Th(P, A, M) = Truncate_n(H(P ‖ A ‖ M))`, its 16-byte address and the types
around it, which `crates/signatures/src/tweak.rs` gives both schemes (`Statement/LeanSphincs.lean`
exports them into `Sphincs`). -/

def digestBits : Nat := 128
def winternitzBits : Nat := 2
def chainLength : Nat := 2 ^ winternitzBits
abbrev MasterSeed := BitVec 256
abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec 256
abbrev Message := BitVec 256
abbrev PublicParameter := BitVec 128
abbrev Randomness := Digest
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
abbrev HashInput := List UInt8

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The second 16 bytes of a hash output. Only the seed derivations of chain starts use them. -/
def upperHash (output : HashOutput) : Digest :=
  output.extractLsb' digestBits digestBits

/-- The half of a hash output that starts chain `n`: the first for even `n`, the second for odd `n`. -/
def hashHalf (n : Nat) (output : HashOutput) : Digest :=
  if n % 2 = 0 then truncateHash output else upperHash output

/-- `pk = (root, P)`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The address of a hash call (`Tweak`, `crates/signatures/src/tweak.rs`): its type `tag < 32`, a
chain step `step < 8`, and two fields `hi < 2^24` and `lo < 2^32`. -/
structure TweakFields where
  tag : BitVec 5
  step : BitVec 3
  hi : BitVec 24
  lo : BitVec 32
deriving DecidableEq

/-- The 16 address bytes `lo || hi || (tag + 32 * step) || 0^8`. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  bytesLE 4 fields.lo ++ bytesLE 3 fields.hi ++ bytesLE 1 (fields.step ++ fields.tag) ++ bytesLE 8 0

/-- Convert the four integer fields to their fixed widths. -/
def tweakFields (tag step hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-- `P || A || payload`, the input of every tweakable hash call at the address `fields`
(`hasher`, `tweak.rs`). -/
def thInput (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    HashInput :=
  bytesLE 16 parameter ++ fieldBytes fields ++ payload

/-! ### leanXMSS's parameters, types and hash-input layout -/

/-- `v`, the chains of a one-time key. -/
def numChains : Nat := 58
/-- `T`, the sum of a codeword's `v` digits. -/
def targetSum : Nat := 106
def numLayers : Nat := 2
/-- `h`, the height of each layer's trees. -/
def layerHeight : Nat := 16
/-- Leaf indices `idx < 2^32`. -/
def lifetime : Nat := 2 ^ (numLayers * layerHeight)
/-- Randomizer trials per one-time signature, `A_max`. -/
def randomizerAttemptLimit : Nat := 2 ^ 32

/-- `l`: `0` the bottom layer, `1` the top. -/
abbrev Layer := Fin numLayers
/-- `idx`, a leaf index. -/
abbrev LeafIndex := Fin lifetime
/-- `e`, a one-time key of a layer: below `2^32` on the bottom layer, below `2^16` on the top. -/
abbrev KeyIndex := Fin lifetime
abbrev ChainIndex := Fin numChains
/-- A pair of chains `(2t, 2t + 1)`, `t < 29`: one seed derivation. -/
abbrev ChainPair := Fin (numChains / 2)
abbrev Encoding := ChainIndex → Digit

def bottomLayer : Layer := ⟨0, by decide⟩
def topLayer : Layer := ⟨1, by decide⟩

/-- The key of layer `l` a leaf index signs with: `idx` at the bottom, `idx / 2^16` at the top. -/
def keyAt (index : LeafIndex) (lay : Layer) : KeyIndex :=
  ⟨index.val / 2 ^ (layerHeight * lay.val),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

/-- One layer's signature: the randomizer, the `v` revealed chain values and the authentication path. -/
structure LayerSignature where
  randomness : Randomness
  chainValues : ChainIndex → Digest
  path : Fin layerHeight → Digest
deriving DecidableEq

/-- The leaf index, then the bottom layer's signature and the top layer's: 2404 bytes. -/
structure Signature where
  leafIndex : LeafIndex
  layers : Layer → LayerSignature
deriving DecidableEq

/-- `hi` on layer `l`: the top layer sets bit 23 (`layer_hi`). -/
def layerHi (lay : Layer) (field : Nat) : Nat := field + 2 ^ 23 * lay.val

/-- The verification hash domains. A node at `level` is the node of tree level `level`, its index
global on the bottom layer (`idx / 2^level`). -/
inductive HashDomain where
  | chain (lay : Layer) (key : KeyIndex) (step : ChainStep)
  | leaf (lay : Layer) (key : KeyIndex)
  | node (lay : Layer) (level : Nat) (nodeIdx : Nat)
  | message (lay : Layer) (key : KeyIndex)
deriving DecidableEq

/-- Types `TWEAK_CHAIN = 1`, `TWEAK_LEAF = 2`, `TWEAK_NODE = 3`, `TWEAK_MSG = 12`. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay key step => tweakFields 1 step (layerHi lay 0) key
  | .leaf lay key => tweakFields 2 0 (layerHi lay 0) key
  | .node lay level nodeIdx => tweakFields 3 0 (layerHi lay level) nodeIdx
  | .message lay key => tweakFields 12 0 (layerHi lay 0) key

/-- `leanXMSS`, the 8 ASCII bytes hashed before the key's seed (`SEED_TAG`). -/
def seedTag : HashInput := [0x6c, 0x65, 0x61, 0x6e, 0x58, 0x4d, 0x53, 0x53]

/-- The seed derivations: the parameter (under `P = 0`), and the starts of chains `2t` and `2t + 1`
of a one-time key, the two halves of one hash. -/
inductive KeygenDomain where
  | parameter
  | ots (lay : Layer) (key : KeyIndex) (pair : ChainPair)
deriving DecidableEq

/-- `TWEAK_PARAMETER = 5`, `TWEAK_PRF = 0` (`hi` the pair of chains, `lo` the key). -/
def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0 0
  | .ots lay key pair => tweakFields 0 0 (layerHi lay pair) key

/-- The pair of chains a chain belongs to. -/
def chainPair (chain : ChainIndex) : ChainPair :=
  ⟨chain.val / 2, by have h : chain.val < 58 := chain.isLt; show chain.val / 2 < 29; omega⟩

/-! #### The codeword -/

namespace Codeword

/-- `x_i`, digit `i < 64` of a digest read as a little-endian integer. -/
def digit (digest : Digest) (i : Nat) : Digit :=
  (digest.extractLsb' (winternitzBits * i) winternitzBits).toFin

/-- The first `v` digits. -/
def encoding (digest : Digest) : Encoding := fun i => digit digest i.val

/-- The sum of a word's digits. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- A codeword: the last `64 - v` digits are zero and the first `v` sum to `T`. -/
def Valid (digest : Digest) : Prop :=
  digest.toNat / 2 ^ (winternitzBits * numChains) = 0 ∧ sum (encoding digest) = targetSum

instance : DecidablePred Valid :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The word a digest encodes, if it is a codeword. -/
def decode (digest : Digest) : Option Encoding :=
  if Valid digest then some (encoding digest) else none

end Codeword

/-! ### The algorithms

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and
signing. Hashing routines work in any monad with access to `HashSpec`. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes (the SUF-CMA game's
`Common.SufCma.HSpec`). -/
abbrev HashSpec := HashInput →ₒ HashOutput

namespace Concrete

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

/-! #### Hash chains and Merkle trees, for both schemes -/

/-- `steps` steps of a hash chain from position `start`: the step leaving position `t < top` is
`step t`, and a walk past position `top` gives `0`. -/
def walkChain {m : Type → Type} [Monad m] {top : Nat} (step : Fin top → Digest → m Digest) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← walkChain step start steps value
      if h : start + steps < top then step ⟨start + steps, h⟩ previous else pure 0

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

/-- Fold the leaf at index `idx` and its path, the sibling at level `l` being `path l`, up `levels`
levels: the node at level `l + 1` is `node l (idx / 2^(l + 1))` of its children in index order. -/
def foldPath {m : Type → Type} [Monad m] (node : Nat → Nat → HashInput → m Digest) (idx : Nat)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | l + 1, value => do
      let current ← foldPath node idx path l value
      node l (idx / 2 ^ (l + 1))
        (if idx.testBit l then nodePayload (path l) current else nodePayload current (path l))

/-- Node `index` at level `level` of the Merkle tree over the leaves `leaf i`: the node at level
`l + 1` is `node l index` of its two children. -/
def buildTree {m : Type → Type} [Monad m] (leaf : Nat → m Digest)
    (node : Nat → Nat → HashInput → m Digest) : Nat → Nat → m Digest
  | 0, index => leaf index
  | l + 1, index => do
      let left ← buildTree leaf node l (2 * index)
      let right ← buildTree leaf node l (2 * index + 1)
      node l index (nodePayload left right)

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One query to the hash `H` (`HashSpec`), which the model answers. -/
def oracleHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-- `Th(P, A, M) = Truncate_n(H(P || A || M))` (`th`, `tweak.rs`). -/
def th (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) : m Digest := do
  return truncateHash (← oracleHash (thInput parameter fields payload))

/-- `H(P || A || M)`, untruncated: two secrets for one hash (`th_pair`). -/
def thPair (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    m HashOutput :=
  oracleHash (thInput parameter fields payload)

/-- `H(tag || S_0)`, all 32 bytes (`tagged_seed`): the seed `S` a scheme derives from. -/
def taggedSeed (tag : HashInput) (seed : MasterSeed) : m MasterSeed :=
  oracleHash (tag ++ bytesLE 32 seed)

/-- The tweakable hash at a hash domain's address. -/
abbrev tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest :=
  th parameter (hashDomainFields domain) payload

/-! #### The one-time signature -/

/-- `value || LE_16(i)`, the payload of a chain step of chain `i`. -/
def chainPayload (chainIdx : ChainIndex) (value : Digest) : HashInput :=
  bytesLE 16 value ++ bytesLE 16 (BitVec.ofNat 128 chainIdx.val)

/-- Chain `i` of a one-time key; the step leaving position `s` carries step `s`. -/
def chainWalk (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest :=
  walkChain fun step value ↦ tweakableHash parameter (.chain lay key step) (chainPayload chainIdx value)

/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay key chainIdx digit.val (chainLength - 1 - digit.val) value

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- The one-time leaf: the hash of the `v` chain ends (`wots_leaf_hash`). -/
def leafHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay key) (leafPayload endpoints)

/-- `D = Th(P, A_msg(l, e), M || rho)` (`message_digest`). -/
def messageDigest (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (randomness : Randomness) : m Digest :=
  tweakableHash parameter (.message lay key) (message ++ bytesLE 16 randomness)

/-- `Ots.leaf` (`wots_leaf`): the leaf a claimed one-time signature recovers, or nothing if its
digest is not a codeword. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (randomness : Randomness) (values : ChainIndex → Digest) : m (Option Digest) := do
  let digest ← messageDigest parameter lay key message randomness
  let some encoding := Codeword.decode digest | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay key chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay key endpoints
  return some value

/-! #### The trees -/

/-- `Tree.fold`: fold a key's leaf and path into its tree's root. -/
def treeFold (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) : Nat → Digest → m Digest :=
  foldPath (fun level nodeIdx ↦ tweakableHash parameter (.node lay (level + 1) nodeIdx)) key.val
    fun level ↦ if h : level < layerHeight then path ⟨level, h⟩ else 0

/-- The root a layer's signature by key `e` reaches from `message`, or nothing (`layer_root`). -/
def layerRoot (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (part : LayerSignature) : m (Option Digest) := do
  let some leaf ← otsLeaf parameter lay key message part.randomness part.chainValues | return none
  let root ← treeFold parameter lay key part.path layerHeight leaf
  return some root

/-! #### Verification -/

/-- `Ver(pk, m, sigma)`: recover the bottom root from the message, then the top root from the bottom
root, and compare it with the public key. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let index := signature.leafIndex
  let some bottomRoot ← layerRoot publicKey.parameter bottomLayer (keyAt index bottomLayer)
      (bytesLE 32 message) (signature.layers bottomLayer) | return false
  let some root ← layerRoot publicKey.parameter topLayer (keyAt index topLayer)
      (bytesLE 16 bottomRoot) (signature.layers topLayer) | return false
  return decide (root = publicKey.root)

end Concrete

/-- The key's seed `S_0`, uniform. -/
noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

open Concrete

/-- The signer's key: the scheme's seed `S` and the parameter. -/
structure SecretKey where
  seed : MasterSeed
  parameter : PublicParameter

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `wots_secrets`: the starts of the `v` chains of a one-time key, from 29 seed derivations.
Chains `2t` and `2t + 1` start at the two halves of derivation `t`. -/
def otsSecrets (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (seed : MasterSeed) :
    m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun pair : ChainPair =>
    thPair parameter (keygenDomainFields (.ots lay key pair)) (bytesLE 32 seed)
  return fun chainIdx => hashHalf chainIdx.val (outputs (chainPair chainIdx))

/-- The chain ends of a one-time key. -/
def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let secrets ← otsSecrets parameter lay key seed
  sequenceFin fun chainIdx => chainWalk parameter lay key chainIdx 0 (chainLength - 1) (secrets chainIdx)

/-- The randomizer trials `R0 + c, R0 + c + 1, ...`, stopping at the first codeword. -/
def otsSignFrom (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (seed : MasterSeed)
    (message : HashInput) (base : Randomness) :
    Nat → Nat → m (Option (Randomness × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := base + BitVec.ofNat digestBits trial
      let digest ← messageDigest parameter lay key message randomness
      match Codeword.decode digest with
      | some encoding => do
          let secrets ← otsSecrets parameter lay key seed
          let values ← sequenceFin fun chainIdx =>
            chainWalk parameter lay key chainIdx 0 (encoding chainIdx).val (secrets chainIdx)
          return some (randomness, values)
      | none => otsSignFrom parameter lay key seed message base attempts (trial + 1)

/-- `wots_sign`: derive `R0`, take the least admissible trial, then open the chains. -/
def otsSign (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (seed : MasterSeed)
    (message : HashInput) : m (Option (Randomness × (ChainIndex → Digest))) := do
  -- `R0`, the randomizer base (`TWEAK_RANDOMIZER = 7`)
  let base ← th parameter (tweakFields 7 0 (layerHi lay 0) key) (bytesLE 32 seed ++ message)
  otsSignFrom parameter lay key seed message base randomizerAttemptLimit 0

/-- Node `nodeIdx` at tree level `level` of layer `l`, from the one-time keys below it. On the bottom
layer node indices are global: node `j` at level `level` is in bottom tree `j / 2^(16 - level)`. -/
def treeNode (parameter : PublicParameter) (lay : Layer) (seed : MasterSeed) : Nat → Nat → m Digest :=
  buildTree (fun nodeIdx ↦ do
      let key : KeyIndex := ⟨nodeIdx % lifetime, Nat.mod_lt _ (by decide)⟩
      leafHash parameter lay key (← oneTimePublicKey parameter lay key seed))
    fun level nodeIdx ↦ tweakableHash parameter (.node lay (level + 1) nodeIdx)

/-- The authentication path of key `e`: at level `level`, the sibling of `e / 2^level`. -/
def treePath (parameter : PublicParameter) (lay : Layer) (seed : MasterSeed) (key : KeyIndex) :
    m (Fin layerHeight → Digest) :=
  sequenceFin fun level => treeNode parameter lay seed level.val (Nat.xor (key.val / 2 ^ level.val) 1)

/-- `Gen` (`key_gen`): hash the key's seed `S_0` into `S`, derive the public parameter and build the
top tree. -/
def keygenFromSeed (keySeed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let seed ← taggedSeed seedTag keySeed
  let parameter ← th 0 (keygenDomainFields .parameter) (bytesLE 32 seed)
  let root ← treeNode parameter topLayer seed layerHeight 0
  return (⟨root, parameter⟩, ⟨seed, parameter⟩)

/-- One layer's signature by key `e` of `message`: the one-time signature and the path. -/
def signLayer (secretKey : SecretKey) (lay : Layer) (key : KeyIndex) (message : HashInput) :
    m (Option LayerSignature) := do
  let some (randomness, values) ← otsSign secretKey.parameter lay key secretKey.seed message
    | return none
  let path ← treePath secretKey.parameter lay secretKey.seed key
  return some ⟨randomness, values, path⟩

/-- `Sign` at leaf index `idx`: the bottom key `idx` signs `m`, and the top key `idx / 2^16` signs the
root of bottom tree `idx / 2^16`. -/
def sign (secretKey : SecretKey) (index : LeafIndex) (message : Message) : m (Option Signature) := do
  let bottomKey := keyAt index bottomLayer
  let topKey := keyAt index topLayer
  let some bottom ← signLayer secretKey bottomLayer bottomKey (bytesLE 32 message) | return none
  let bottomRoot ← treeNode secretKey.parameter bottomLayer secretKey.seed layerHeight topKey.val
  let some top ← signLayer secretKey topLayer topKey (bytesLE 16 bottomRoot) | return none
  return some ⟨index, fun lay => if lay = bottomLayer then bottom else top⟩

end Seeded

/-! ## Signing requests, forgeries and transcripts -/

/-- A signing request: a leaf index and a 32-byte message. -/
structure SignRequest where
  leafIndex : LeafIndex
  message : Message
deriving DecidableEq

/-- A claimed forgery: a message and a signature, which carries its leaf index. -/
structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

/-- The signing oracle answers a request with a signature, or `none` if the signer fails. -/
abbrev SigningSpec := SignRequest →ₒ Option Signature

namespace SigningTranscript

/-- A transcript is valid when no leaf index occurs twice. -/
abbrev Valid (log : QueryLog SigningSpec) : Prop :=
  (log.map fun entry => entry.1.leafIndex).Nodup

end SigningTranscript

end LeanXmss

end
