import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Types
import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Convert

/-!
# The leanXMSS model

leanXMSS (`doc/lean_xmss`) with precomputed keys, a device of the proof.

It has two layers of XMSS of height 16.

The bottom layer is a forest of `2^16` trees over the `2^32` bottom one-time keys.

Its node indices are global.

Top key `b` signs the root of bottom tree `b` once, at key generation.

Its hashes and its verifier are EthLib's, read through the byte conversions.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- Enter a query log into a cache, in order. -/
def extendHashCacheWithLog (initialCache : QueryCache HashSpec) :
    QueryLog HashSpec → QueryCache HashSpec
  | [] => initialCache
  | ⟨input, output⟩ :: tail =>
      extendHashCacheWithLog (initialCache.cacheQuery input output) tail

/-- The cache a query log records. -/
def hashCacheOfLog (log : QueryLog HashSpec) : QueryCache HashSpec :=
  extendHashCacheWithLog ∅ log

namespace Concrete

/-- `m || rho`: with `P || A`, 80 bytes, one block of the leanVM hash.

So a trial is one Keccak-f permutation. -/
def encodingPayload (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 32 message ++ bytesLE 16 randomness

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- `r_b || rho`: the top layer signs a 16-byte bottom root. -/
def topEncodingPayload (root : Digest) (randomness : Randomness) : HashInput :=
  bytesLE 16 root ++ bytesLE 16 randomness

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]


/-- `Th(P, tw, M) = Truncate_n(H(tw || P || M))`. -/
def tweakableHash
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) : m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-! ### The hashes

Each hash is EthLib's, run with `queryH` on the bytes of the model's values.

`tweakableHash` names the oracle input each one makes.

`Unforgeability/Translate.lean` proves it, as `encodingHash_eq` and the others. -/

section

open EthLib.Cryptography.Xmss.Unforgeability (queryH ofParam ofLeafIndex ofTopIndex ofDigest
  toDigest ofMessage ofRandomizer ofChains)

/-- The digest `D` of `IncEnc(P, m, rho, idx)`: EthLib's bottom `messageDigest`. -/
def encodingHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) : m Digest :=
  toDigest <$> EthLib.Cryptography.Xmss.messageDigest queryH (ofParam parameter) .bottom
    (ofLeafIndex leafIndex) (EthLib.Cryptography.Xmss.packBytes (ofMessage message))
    (ofRandomizer randomness)

/-- One chain step, under `tweak_chain(idx, i, step + 1)`: EthLib's bottom `chainStep`. -/
def chainHash (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : m Digest :=
  toDigest <$> EthLib.Cryptography.Xmss.chainStep queryH (ofParam parameter) .bottom
    (ofLeafIndex leafIndex) ⟨chain.val, chain.isLt⟩ step (ofDigest value)

/-- `X_{0,idx}`, the hash of the `v` public values: EthLib's bottom `otsLeafHash`. -/
def leafHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  toDigest <$> EthLib.Cryptography.Xmss.otsLeafHash queryH (ofParam parameter) .bottom
    (ofLeafIndex leafIndex) (ofChains endpoints)

/-- `X_{level+1,node}` from its two children: EthLib's bottom `nodeHash`. -/
def nodeHash (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) : m Digest :=
  toDigest <$> EthLib.Cryptography.Xmss.nodeHash queryH (ofParam parameter) .bottom
    ⟨level.val + 1, Nat.succ_lt_succ level.isLt⟩ node.val (ofDigest left) (ofDigest right)

/-- The top layer's message digest of a bottom root: EthLib's top `messageDigest`. -/
def topEncodingHash (parameter : PublicParameter) (key : TopIndex)
    (root : Digest) (randomness : Randomness) : m Digest :=
  toDigest <$> EthLib.Cryptography.Xmss.messageDigest queryH (ofParam parameter) .top
    (ofTopIndex key) (EthLib.Cryptography.Xmss.packBytes (ofDigest root)) (ofRandomizer randomness)

/-- One top chain step: EthLib's top `chainStep`. -/
def topChainHash (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : m Digest :=
  toDigest <$> EthLib.Cryptography.Xmss.chainStep queryH (ofParam parameter) .top
    (ofTopIndex key) ⟨chain.val, chain.isLt⟩ step (ofDigest value)

/-- A top leaf: EthLib's top `otsLeafHash`. -/
def topLeafHash (parameter : PublicParameter) (key : TopIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  toDigest <$> EthLib.Cryptography.Xmss.otsLeafHash queryH (ofParam parameter) .top
    (ofTopIndex key) (ofChains endpoints)

/-- A top node from its two children: EthLib's top `nodeHash`. -/
def topNodeHash (parameter : PublicParameter) (level : MerkleLevel) (node : TopNode)
    (left right : Digest) : m Digest :=
  toDigest <$> EthLib.Cryptography.Xmss.nodeHash queryH (ofParam parameter) .top
    ⟨level.val + 1, Nat.succ_lt_succ level.isLt⟩ node.val (ofDigest left) (ofDigest right)

end

/-! ### Verification -/

/-- `A_level`, or `0` above the tree. -/
def signaturePath (signature : Signature) (level : Nat) : Digest :=
  if hlevel : level < treeHeight then signature.authPath ⟨level, hlevel⟩ else 0

/-- `Chain_{i,idx}(P, start, steps, value)`.

The step onto position `start + steps + 1` carries step `start + steps` in its address.

It carries `i` after its value. -/
def chainWalk (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | position, steps + 1, value => do
      let previous ← chainWalk parameter leafIndex chain position steps value
      if hposition : position + steps < chainLength - 1 then
        chainHash parameter leafIndex chain ⟨position + steps, hposition⟩ previous
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `2^w - 1 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter leafIndex chain digit.val (chainLength - 1 - digit.val) value

/-- `pk'_{idx,i}` for every chain. -/
def recoverEndpoints (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Signature) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    recoverChain parameter leafIndex chain (encoding chain) (signature.chainValue chain)

/-- The index of the Merkle node on the path of `leafIndex` one level above `level`. -/
def nodeIndex (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  ⟨leafIndex.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self leafIndex.val (2 ^ (level + 1))
    exact hle.trans_lt leafIndex.isLt⟩

/-- `Z_{level+1}` from `Z_level` and `A_level`.

Bit `level` of the leaf index dictates their order. -/
def authenticationNodeHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (level : Nat) (current sibling : Digest) : m Digest :=
  if hlevel : level < treeHeight then
    if leafIndex.val.testBit level then
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) sibling current
    else
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) current sibling
  else
    pure 0

/-- `Z_levels`, folded up from the leaf `Z_0`. -/
def authenticationRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) : Nat → Digest → m Digest
  | 0, leaf => pure leaf
  | levels + 1, leaf => do
      let current ← authenticationRoot parameter leafIndex signature levels leaf
      authenticationNodeHash parameter leafIndex levels current (signaturePath signature levels)

/-- A top chain walk, as `chainWalk`. -/
def topChainWalk (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | position, steps + 1, value => do
      let previous ← topChainWalk parameter key chain position steps value
      if hposition : position + steps < chainLength - 1 then
        topChainHash parameter key chain ⟨position + steps, hposition⟩ previous
      else
        pure 0

/-- The top node on the path of key `b` one level above `level`. -/
def topNodeIndex (key : TopIndex) (level : Nat) : TopNode :=
  ⟨key.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self key.val (2 ^ (level + 1))
    exact hle.trans_lt key.isLt⟩

/-- `Z_levels` of the top tree, folded up from the top leaf. -/
def topAuthenticationRoot (parameter : PublicParameter) (key : TopIndex)
    (path : Fin treeHeight → Digest) : Nat → Digest → m Digest
  | 0, leaf => pure leaf
  | levels + 1, leaf => do
      let current ← topAuthenticationRoot parameter key path levels leaf
      if hlevel : levels < treeHeight then
        let sibling := path ⟨levels, hlevel⟩
        if key.val.testBit levels then
          topNodeHash parameter ⟨levels, hlevel⟩ (topNodeIndex key levels) sibling current
        else
          topNodeHash parameter ⟨levels, hlevel⟩ (topNodeIndex key levels) current sibling
      else
        pure 0

/-- The top layer's check: its signature of bottom root `root` by key `b` reaches the public root.

It is EthLib's top layer (`layerRoot`), on the bytes of the model's values. -/
def verifyTop (publicKey : PublicKey) (key : TopIndex) (root : Digest) (part : LayerSignature) :
    m Bool := do
  let some topRoot ← EthLib.Cryptography.Xmss.layerRoot
      EthLib.Cryptography.Xmss.Unforgeability.queryH
      (EthLib.Cryptography.Xmss.Unforgeability.ofParam publicKey.parameter) .top key.val
      (EthLib.Cryptography.Xmss.packBytes (EthLib.Cryptography.Xmss.Unforgeability.ofDigest root))
      (EthLib.Cryptography.Xmss.Unforgeability.ofLayerSig part)
    | return false
  return decide (topRoot = EthLib.Cryptography.Xmss.Unforgeability.ofDigest publicKey.root)

/-- Fold the bottom leaf to its tree's root, then check the top layer's signature of that root.

The fold is EthLib's (`fold`), on the bytes of the model's values. -/
def verifyAfterLeaf
    (publicKey : PublicKey) (leafIndex : LeafIndex) (signature : Signature) (leaf : Digest) :
    m Bool := do
  let root ← EthLib.Cryptography.Xmss.fold EthLib.Cryptography.Xmss.Unforgeability.queryH
    (EthLib.Cryptography.Xmss.Unforgeability.ofParam publicKey.parameter) .bottom leafIndex.val
    (EthLib.Cryptography.Xmss.Unforgeability.ofDigest leaf)
    (EthLib.Cryptography.Xmss.Unforgeability.ofPath signature.authPath)
  verifyTop publicKey (topKeyOf leafIndex) (EthLib.Cryptography.Xmss.Unforgeability.toDigest root)
    signature.top

/-- `Ver(pk, idx, m, sigma)`: EthLib's verifier, on the bytes of the model's values.

`Unforgeability/Translate.lean` unfolds it into the routines above (`Concrete.verify_eq`). -/
def verify (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) : m Bool :=
  EthLib.Cryptography.Xmss.verifyWith EthLib.Cryptography.Xmss.Unforgeability.queryH
    (EthLib.Cryptography.Xmss.Unforgeability.ofPublicKey publicKey)
    (EthLib.Cryptography.Xmss.Unforgeability.ofMessage message)
    (EthLib.Cryptography.Xmss.Unforgeability.ofSignature leafIndex signature)

/-! ### Precomputed chains and tree -/

/-- `pk_{idx,i} = Chain(P, 0, 2^w - 1, sk_{idx,i})` for every chain. -/
def oneTimePublicKey (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) : m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk parameter leafIndex chain 0 (chainLength - 1) (secret leafIndex chain)

/-- `X_{0,idx}` from the secrets. -/
def leafAt (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) : m Digest := do
  let endpoints ← oneTimePublicKey parameter secret leafIndex
  leafHash parameter leafIndex endpoints

/-- A natural read as a node index. -/
def merkleNodeOfNat (value : Nat) : MerkleNode :=
  ⟨value % lifetime,
    Nat.mod_lt _ (by simp [lifetime])⟩

/-- `2j` or `2j + 1`. -/
def childNode (node : MerkleNode) (right : Bool) : MerkleNode :=
  merkleNodeOfNat (2 * node.val + if right then 1 else 0)

/-- `X_{levels,node}`, the Merkle tree over the one-time leaves. -/
def treeNode (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    Nat → MerkleNode → m Digest
  | 0, node => leafAt parameter secret node
  | levels + 1, node => do
      let left ← treeNode parameter secret levels (childNode node false)
      let right ← treeNode parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0

/-- The root of bottom tree `b`: node `b` of level `h`. -/
def bottomRootNode (key : TopIndex) : MerkleNode :=
  ⟨key.val, key.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by simp [treeHeight]))⟩

/-- The top chain ends of key `b`. -/
def topOneTimePublicKey (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key : TopIndex) : m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    topChainWalk parameter key chain 0 (chainLength - 1) (topSecret key chain)

/-- The top leaf of key `b`. -/
def topLeafAt (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key : TopIndex) : m Digest := do
  let endpoints ← topOneTimePublicKey parameter topSecret key
  topLeafHash parameter key endpoints

def topNodeOfNat (value : Nat) : TopNode :=
  ⟨value % topLifetime, Nat.mod_lt _ (by simp [topLifetime])⟩

def topChildNode (node : TopNode) (right : Bool) : TopNode :=
  topNodeOfNat (2 * node.val + if right then 1 else 0)

/-- `X_{levels,node}` of the top tree. -/
def topTreeNode (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest) :
    Nat → TopNode → m Digest
  | 0, node => topLeafAt parameter topSecret node
  | levels + 1, node => do
      let left ← topTreeNode parameter topSecret levels (topChildNode node false)
      let right ← topTreeNode parameter topSecret levels (topChildNode node true)
      if hlevel : levels < treeHeight then
        topNodeHash parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0

/-- The public root is node `0` of the top tree's level `h`. -/
def rootNode : TopNode :=
  ⟨0, by simp [topLifetime]⟩

/-- The top grinding of bottom root `root` by key `b` from the base `R0`.

It returns the least trial whose digest is a codeword, with that codeword. -/
def topSignFrom (parameter : PublicParameter) (key : TopIndex) (root : Digest) (base : Randomness) :
    Nat → Nat → m (Option (Randomness × Encoding))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := base + BitVec.ofNat randomnessBits trial
      let digest ← topEncodingHash parameter key root randomness
      match TargetSum.decodeDigest digest with
      | some encoding => return some (randomness, encoding)
      | none => topSignFrom parameter key root base attempts (trial + 1)

/-- The honest computation of key generation.

It computes every bottom root and its top signature, from the base `topBase b r_b`.

Then it computes the top tree's root. -/
def honestKeygen (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Digest → m Randomness) :
    m (Digest × (TopIndex → Option (Randomness × Encoding))) := do
  let topSigned ← sequenceFin fun key => do
    let bottomRoot ← treeNode parameter secret treeHeight (bottomRootNode key)
    let base ← topBase key bottomRoot
    topSignFrom parameter key bottomRoot base signingAttemptLimit 0
  let root ← topTreeNode parameter topSecret treeHeight rootNode
  return (root, topSigned)

/-- Answer a hash query from a recorded query cache, and by 0 for an unrecorded input. -/
def replayHash (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

/-- Compute the stored chain values and nodes of both layers.

This replays the key-generation query log. -/
def precomputedSecretKey (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (topSecret : TopIndex → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) (cache : QueryCache HashSpec) :
    SecretKey where
  parameter := parameter
  chainStart := secret
  chainValue := fun leafIndex chain digit =>
    evalWithAnswerFn (replayHash cache)
      (chainWalk parameter leafIndex chain 0 digit.val (secret leafIndex chain) :
        OracleComp HashSpec Digest)
  treeValue := fun height node =>
    evalWithAnswerFn (replayHash cache)
      (treeNode parameter secret height.val node : OracleComp HashSpec Digest)
  topChainStart := topSecret
  topChainValue := fun key chain digit =>
    evalWithAnswerFn (replayHash cache)
      (topChainWalk parameter key chain 0 digit.val (topSecret key chain) :
        OracleComp HashSpec Digest)
  topTreeValue := fun height node =>
    evalWithAnswerFn (replayHash cache)
      (topTreeNode parameter topSecret height.val node : OracleComp HashSpec Digest)
  topSigned := topSigned

/-! ### Signing -/

/-- `floor(idx / 2^level) xor 1`, the sibling on the path. -/
def authenticationPathNode (leafIndex : LeafIndex) (level : MerkleLevel) : MerkleNode :=
  merkleNodeOfNat (Nat.xor (leafIndex.val / 2 ^ level.val) 1)

/-- The sibling on the top path of key `b`. -/
def topPathNode (key : TopIndex) (level : MerkleLevel) : TopNode :=
  topNodeOfNat (Nat.xor (key.val / 2 ^ level.val) 1)

/-- The top layer's signature of bottom tree `b`, read from the key.

It is zeros if its grinding failed. -/
def topPart (secretKey : SecretKey) (key : TopIndex) : LayerSignature :=
  match secretKey.topSigned key with
  | some (randomness, encoding) =>
      { randomness := randomness
        chainValue := fun chain => secretKey.topChainValue key chain (encoding chain)
        authPath := fun level => secretKey.topTreeValue level.castSucc (topPathNode key level) }
  | none => ⟨0, fun _ => 0, fun _ => 0⟩

/-- The signature once the encoding is found. -/
def precomputedSignWithEncoding (secretKey : SecretKey) (leafIndex : LeafIndex)
    (randomness : Randomness) (encoding : Encoding) : Signature :=
  { randomness := randomness
    chainValue := fun chain => secretKey.chainValue leafIndex chain (encoding chain)
    authPath := fun level => secretKey.treeValue level.castSucc (authenticationPathNode leafIndex level)
    top := topPart secretKey (topKeyOf leafIndex) }

/-- One attempt: hash once, and sign if the digest encodes. -/
def precomputedSignAttempt (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter leafIndex message randomness
  let some encoding := TargetSum.decodeDigest digest | return none
  return some (precomputedSignWithEncoding secretKey leafIndex randomness encoding)

/-- Signing fails at every leaf index of a bottom tree whose top grinding failed. -/
def topSignedAt (secretKey : SecretKey) (leafIndex : LeafIndex) : Bool :=
  (secretKey.topSigned (topKeyOf leafIndex)).isSome

attribute [irreducible] verifyAfterLeaf treeNode

end Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

/-- One seed derivation, all 32 bytes: the starts of two chains are its halves. -/
def deriveOutput (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    m HashOutput :=
  Concrete.oracleHash (keygenHashInput parameter domain seed)

/-- `R0 = Th(P, A_rnd(idx), S || m)`. -/
def deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) : m Randomness := do
  return (← Concrete.oracleHash (randomizerHashInput parameter seed leafIndex message)).extractLsb' 0 randomnessBits

/-- `R0` of the top signature of bottom tree `b`. -/
def deriveTopRandomizer (parameter : PublicParameter) (seed : MasterSeed) (key : TopIndex)
    (root : Digest) : m Randomness := do
  return truncateHash (← Concrete.oracleHash (topRandomizerHashInput parameter seed key root))

/-- The chain starts of every bottom key, from 29 derivations each. -/
def deriveSecrets (parameter : PublicParameter) (seed : MasterSeed) :
    m (LeafIndex → ChainIndex → Digest) := do
  let outputs ← Concrete.sequenceFin fun leafIndex => Concrete.sequenceFin fun pair =>
    deriveOutput parameter (.chain leafIndex pair) seed
  return fun leafIndex chain => hashHalf chain.val (outputs leafIndex (chainPair chain))

/-- The chain starts of every top key. -/
def deriveTopSecrets (parameter : PublicParameter) (seed : MasterSeed) :
    m (TopIndex → ChainIndex → Digest) := do
  let outputs ← Concrete.sequenceFin fun key => Concrete.sequenceFin fun pair =>
    deriveOutput parameter (.topChain key pair) seed
  return fun key chain => hashHalf chain.val (outputs key (chainPair chain))

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

/-- The scheme's seed `S`, and what key generation computes.

That is the chain and tree values and the top signatures. -/
structure SecretKey where
  seed : MasterSeed
  precomputed : XmssSecurity.SecretKey

/-- Hash the key's seed `S_0` into `S = H("leanXMSS" || S_0)`.

Derive the parameter and the secrets, then compute and store both layers. -/
def keygenFromSeed (keySeed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let seed ← Concrete.oracleHash (seedHashInput keySeed)
  let parameter ← deriveKey 0 .parameter seed
  let secret ← deriveSecrets parameter seed
  let topSecret ← deriveTopSecrets parameter seed
  let result ← (Concrete.honestKeygen parameter secret topSecret
    (deriveTopRandomizer parameter seed) : OracleComp HashSpec _).withQueryLog
  let precomputed := Concrete.precomputedSecretKey parameter secret topSecret result.1.2
    (hashCacheOfLog result.2)
  return (⟨result.1.1, parameter⟩, ⟨seed, precomputed⟩)

/-- Try the randomizers `base + trial, base + trial + 1, ...`.

Stop at the first admissible encoding. -/
def signFrom (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) (base : Randomness) :
    Nat → Nat → m (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := base + BitVec.ofNat randomnessBits trial
      match ← Concrete.precomputedSignAttempt secretKey.precomputed leafIndex message randomness with
      | some signature => return some signature
      | none => signFrom secretKey leafIndex message base attempts (trial + 1)

/-- Derive `R0` and take the least admissible trial `R0 + c`, `c < A_max`.

Then attach the top signature.

Fail if the bottom tree has none. -/
def sign (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) : m (Option Signature) := do
  let base ← deriveRandomizer secretKey.precomputed.parameter secretKey.seed leafIndex message
  let result ← signFrom secretKey leafIndex message base signingAttemptLimit 0
  return if Concrete.topSignedAt secretKey.precomputed leafIndex then result else none

end Seeded

end XmssSecurity
