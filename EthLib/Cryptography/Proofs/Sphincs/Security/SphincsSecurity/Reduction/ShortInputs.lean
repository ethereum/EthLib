module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Classification.Verifier
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Domains
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Honest hash inputs are short

Every hash input of key generation, signing and verification has at most 2084 bytes.

The longest ones have 1072 bytes: 16 parameter bytes, 32 address bytes and 64 values of 16 bytes.

The input that compresses the 64 chain ends of a one-time key always has this length.

The input that compresses the roots of a FORS key of `k <= 64` trees has `48 + 16 k` bytes.
-/

@[expose] public section

-- The byte-length lemmas must see the parameter and digest widths as `8 * 16` to match.
set_option backward.isDefEq.respectTransparency false

open OracleComp OracleSpec

namespace SphincsSecurity.Security.Short

variable [Params]

open Concrete

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

/--
A bound on the length of an honest hash input, in bytes.

It allows 16 parameter bytes, 32 address bytes and a payload of at most 2036 bytes.
-/
def bound : Nat := 2084

def IsShort (input : HashInput) : Prop := input.length ≤ bound

instance : DecidablePred IsShort := fun input => inferInstanceAs (Decidable (input.length ≤ bound))

/-- Every hash query of the computation is short. -/
def Only {α : Type} (oa : OracleComp HashSpec α) : Prop :=
  oa.IsQueryBoundP (fun input => ¬IsShort input) 0

omit [Params] in
theorem Only.pure' {α : Type} (value : α) : Only (pure value : OracleComp HashSpec α) := trivial

omit [Params] in
theorem Only.bind {α β : Type} {oa : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    (h : Only oa) (hnext : ∀ value, Only (next value)) : Only (oa >>= next) := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa [Only] using this

omit [Params] in
theorem Only.ite {α : Type} (condition : Prop) [Decidable condition]
    {left right : OracleComp HashSpec α} (hleft : Only left) (hright : Only right) :
    Only (if condition then left else right) := by
  split
  · exact hleft
  · exact hright

omit [Params] in
theorem Only.query {input : HashInput} (h : IsShort input) :
    Only (oracleHash input : OracleComp HashSpec HashOutput) := by
  simp only [Only, oracleHash, HasQuery.query]
  rw [isQueryBoundP_query_iff]
  intro hlong
  exact absurd h hlong

theorem Only.tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) (h : payload.length ≤ 2036) :
    Only (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) := by
  unfold Concrete.tweakableHash
  refine Only.bind (Only.query ?_) (fun _ => Only.pure' _)
  simp only [IsShort, bound, tweakableHashInput_length]
  omega

omit [Params] in
theorem Only.derivePublicSeed (seed : MasterSeed) :
    Only (SphincsSecurity.derivePublicSeed seed : OracleComp HashSpec PublicParameter) := by
  unfold SphincsSecurity.derivePublicSeed
  refine Only.bind (Only.query ?_) (fun _ => Only.pure' _)
  simp [IsShort, bound, keySeedInput_length]

omit [Params] in
theorem Only.derivePrf (seed : MasterSeed) :
    Only (SphincsSecurity.derivePrf seed : OracleComp HashSpec HashOutput) := by
  refine Only.query ?_
  simp [IsShort, bound, keySeedInput_length]

theorem Only.deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    Only (SphincsSecurity.deriveKey parameter domain seed : OracleComp HashSpec Digest) := by
  unfold SphincsSecurity.deriveKey
  refine Only.bind (Only.query ?_) (fun _ => Only.pure' _)
  simp [IsShort, bound, keygenHashInput_length]

omit [Params] in
theorem Only.sequenceFin {α : Type} {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (h : ∀ i, Only (computation i)) : Only (Concrete.sequenceFin computation) := by
  induction n with
  | zero => exact Only.pure' _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      exact Only.bind (h 0) (fun _ => Only.bind (ih _ (fun i => h i.succ)) (fun _ => Only.pure' _))

theorem Only.chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start : Nat) :
    ∀ steps value, Only (Concrete.chainWalk parameter lay tree leaf chainIdx start steps value :
      OracleComp HashSpec Digest)
  | 0, value => Only.pure' _
  | steps + 1, value => by
      rw [Concrete.chainWalk]
      refine Only.bind (Only.chainWalk parameter lay tree leaf chainIdx start steps value) ?_
      intro previous
      split
      · exact Only.tweakableHash _ _ _ (by rw [bytesLE_length]; omega)
      · exact Only.pure' _

omit [Params] in
theorem Only.sequenceDep : ∀ {n : Nat} {α : Fin n → Type}
    {computation : (i : Fin n) → OracleComp HashSpec (Option (α i))}, (∀ i, Only (computation i)) →
      Only (sequenceDep computation)
  | 0, _, _, _ => Only.pure' _
  | _ + 1, α, computation, h => by
      unfold SphincsSecurity.Concrete.sequenceDep
      refine Only.bind (h (Fin.last _)) (fun head => ?_)
      rcases head with _ | head
      · exact Only.pure' _
      · refine Only.bind (Only.sequenceDep (α := fun i => α i.castSucc) fun i => h
          i.castSucc) (fun tail => ?_)
        rcases tail with _ | tail <;> exact Only.pure' _

theorem Only.leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (endpoints : ChainIndex → Digest) :
    Only (Concrete.leafHash parameter lay tree leaf endpoints : OracleComp HashSpec Digest) :=
  Only.tweakableHash _ _ _ (by rw [leafPayload_length]; omega)

/-- A layer's message is at most 1024 bytes (it is a 16-byte root). -/
def ShortMessage (message : HashInput) : Prop := message.length ≤ 1024

omit [Params] in
theorem shortMessage_root (root : Digest) : ShortMessage (rootPayload root) := by
  unfold ShortMessage rootPayload; rw [bytesLE_length]; omega

theorem Only.encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : HashInput) (hmsg : ShortMessage message) (counter : Counter) :
    Only (Concrete.encode parameter lay tree leaf message counter :
      OracleComp HashSpec (Option Encoding)) := by
  unfold Concrete.encode
  unfold ShortMessage at hmsg
  exact Only.bind (Only.tweakableHash _ _ _ (by simp [bytesBE_length]; omega))
    (fun _ => Only.pure' _)

theorem Only.otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : HashInput) (hmsg : ShortMessage message) (counter : Counter)
    (values : ChainIndex → Digest) :
    Only (Concrete.otsLeaf parameter lay tree leaf message counter values :
      OracleComp HashSpec (Option Digest)) := by
  unfold Concrete.otsLeaf
  refine Only.bind (Only.encode _ _ _ _ _ hmsg _) ?_
  intro encoding
  cases encoding with
  | none => exact Only.pure' _
  | some encoding =>
      exact Only.bind (Only.sequenceFin _ fun chainIdx => Only.chainWalk _ _ _ _ _ _ _ _)
        (fun _ => Only.bind (Only.leafHash _ _ _ _ _) (fun _ => Only.pure' _))

theorem Only.treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) :
    ∀ levels value, Only (Concrete.treeFold parameter lay tree leaf path levels value :
      OracleComp HashSpec Digest)
  | 0, value => Only.pure' _
  | levels + 1, value => by
      rw [Concrete.treeFold]
      refine Only.bind (Only.treeFold parameter lay tree leaf path levels value) ?_
      intro current
      split <;> exact Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)

theorem Only.forsLeafHash (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (secret : Digest) :
    Only (Concrete.forsLeafHash parameter index κ leaf secret : OracleComp HashSpec Digest) :=
  Only.tweakableHash _ _ _ (by rw [bytesLE_length]; omega)

theorem Only.forsFold (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (path : Fin forsHeight → Digest) :
    ∀ levels value, Only (Concrete.forsFold parameter index κ leaf path levels value :
      OracleComp HashSpec Digest)
  | 0, value => Only.pure' _
  | levels + 1, value => by
      rw [Concrete.forsFold]
      refine Only.bind (Only.forsFold parameter index κ leaf path levels value) ?_
      intro current
      dsimp only
      split_ifs
      · exact Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)
      · exact Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)
      · exact Only.pure' _

theorem Only.forsRecover (parameter : PublicParameter) (index : Index)
    (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) :
    Only (Concrete.forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey) := by
  unfold Concrete.forsRecover Concrete.treeRecover
  exact Only.sequenceFin _ fun κ => Only.bind (Only.forsLeafHash _ _ _ _ _) (fun _ =>
    Only.forsFold _ _ _ _ _ _ _)

theorem Only.forsPublicKey (parameter : PublicParameter) (index : Index) (roots : ForsKey) :
    Only (Concrete.forsPublicKey parameter index roots : OracleComp HashSpec Digest) :=
  Only.tweakableHash _ _ _ (by rw [rootsPayload_length]; have := Params.forsTrees_le; omega)

theorem Only.messageDigestCall (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) :
    Only (Concrete.messageDigestCall parameter root message randomness call :
      OracleComp HashSpec HashOutput) := by
  unfold Concrete.messageDigestCall
  apply Only.query
  simp only [IsShort, bound, messageDigestInput_length]
  omega

theorem Only.messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    Only (Concrete.messageDigest parameter root message randomness :
      OracleComp HashSpec MessageDigest) := by
  unfold Concrete.messageDigest
  exact Only.bind (Only.sequenceFin _ fun _ => Only.messageDigestCall _ _ _ _ _)
      (fun _ => Only.pure' _)

attribute [local irreducible] Concrete.treeFold Concrete.chainWalk
  Concrete.otsLeaf Concrete.forsRecover Concrete.messageDigest

theorem Only.verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    ∀ (n : Nat) (message : HashInput), ShortMessage message →
      Only (Concrete.verifyLayers parameter index signature n message :
        OracleComp HashSpec (Option Digest))
  | 0, _, _ => Only.pure' _
  | n + 1, message, hmsg => by
      rw [Concrete.verifyLayers]
      split
      · refine Only.bind (Only.otsLeaf _ _ _ _ _ hmsg _ _) ?_
        intro value
        cases value with
        | none => exact Only.pure' _
        | some value =>
            refine Only.bind (Only.treeFold _ _ _ _ _ _ value) (fun root => ?_)
            split
            · exact Only.pure' _
            · exact Only.verifyLayers parameter index signature n _ (shortMessage_root root)
      · exact Only.pure' _

theorem Only.verify (publicKey : PublicKey) (message : Message) (signature : Signature) :
    Only (Concrete.verify publicKey message signature : OracleComp HashSpec Bool) := by
  rw [verify_eq_layers]
  refine Only.bind (Only.messageDigest _ _ _ _) ?_
  intro digest
  refine Only.bind (Only.forsRecover _ _ _ _) ?_
  intro roots
  refine Only.bind (Only.forsPublicKey _ _ _) ?_
  intro key
  refine Only.bind (Only.verifyLayers _ _ _ _ _ (shortMessage_root key)) ?_
  intro value
  cases value <;> exact Only.pure' _

namespace Seeded
open SphincsSecurity.Seeded

theorem Only.otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    Only (otsSecrets parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) :=
  Short.Only.sequenceFin _ fun _ => Short.Only.deriveKey _ _ _

theorem Only.oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) :
    Only (oneTimePublicKey parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) :=
  Short.Only.bind (Only.otsSecrets _ _ _ _ _) (fun _ =>
    Short.Only.sequenceFin _ fun _ => Short.Only.chainWalk _ _ _ _ _ _ _ _)

theorem Only.otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput) (hmsg : ShortMessage message) :
    ∀ attempts counter, Short.Only (otsSignFrom parameter lay tree leaf seed
        message attempts counter :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))
  | 0, _ => Short.Only.pure' _
  | attempts + 1, counter => by
      rw [SphincsSecurity.Seeded.otsSignFrom]
      refine Short.Only.bind (Short.Only.encode _ _ _ _ _ hmsg _) ?_
      intro encoding
      cases encoding with
      | none =>
          exact Only.otsSignFrom parameter lay tree leaf seed message hmsg attempts (counter + 1)
      | some encoding =>
          exact Short.Only.bind (Only.otsSecrets _ _ _ _ _) (fun _ =>
            Short.Only.bind (Short.Only.sequenceFin _ fun _ => Short.Only.chainWalk _ _ _ _ _ _ _ _)
              (fun _ => Short.Only.pure' _))

theorem Only.treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : ∀ level nodeIdx, Short.Only
        (treeNode parameter lay tree seed level nodeIdx :
      OracleComp HashSpec Digest)
  | 0, nodeIdx => by
      rw [SphincsSecurity.Seeded.treeNode]
      exact Short.Only.bind (Only.oneTimePublicKey _ _ _ _ _)
          (fun _ => Short.Only.leafHash _ _ _ _ _)
  | level + 1, nodeIdx => by
      rw [SphincsSecurity.Seeded.treeNode]
      exact Short.Only.bind (Only.treeNode parameter lay tree seed level _) (fun _ =>
        Short.Only.bind (Only.treeNode parameter lay tree seed level _) (fun _ =>
          Short.Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)))

theorem Only.forsSecret (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (seed : MasterSeed) :
    Short.Only (forsSecret parameter index κ leaf seed : OracleComp HashSpec Digest) :=
  Short.Only.deriveKey _ _ _

theorem Only.forsNode (parameter : PublicParameter) (index : Index) (κ : FTree)
    (seed : MasterSeed) :
    ∀ level node, Short.Only (forsNode parameter index κ seed level node :
        OracleComp HashSpec Digest)
  | 0, node => by
      rw [SphincsSecurity.Seeded.forsNode]
      exact Short.Only.bind (Only.forsSecret _ _ _ _ _) (fun _ => Short.Only.forsLeafHash _ _ _ _ _)
  | level + 1, node => by
      rw [SphincsSecurity.Seeded.forsNode]
      refine Short.Only.bind (Only.forsNode parameter index κ seed level _) (fun _ =>
        Short.Only.bind (Only.forsNode parameter index κ seed level _) (fun _ => ?_))
      split
      · exact Short.Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)
      · exact Short.Only.pure' _

theorem Only.forsKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) :
    Short.Only (forsKey parameter index seed : OracleComp HashSpec Digest) := by
  unfold SphincsSecurity.Seeded.forsKey
  exact Short.Only.bind
    (Short.Only.sequenceFin _ fun κ => Only.forsNode parameter index κ seed _ _) (fun _ =>
      Short.Only.forsPublicKey _ _ _)

theorem Only.forsOpen (parameter : PublicParameter) (index : Index) (leaves : FTree → FLeaf)
    (seed : MasterSeed) :
    Short.Only (forsOpen parameter index leaves seed : OracleComp HashSpec
        (FTree → TreeOpening)) := by
  unfold SphincsSecurity.Seeded.forsOpen SphincsSecurity.Seeded.treeOpen
  exact Short.Only.sequenceFin _ fun _ =>
    Short.Only.bind (Only.forsSecret _ _ _ _ _) (fun _ =>
      Short.Only.bind (Short.Only.sequenceFin _ fun _ => Only.forsNode _ _ _ _ _ _)
        (fun _ => Short.Only.pure' _))

theorem Only.surrogate (parameter : PublicParameter) (seed : MasterSeed) (level : Nat) :
    Short.Only (surrogate parameter seed level : OracleComp HashSpec Digest) := by
  unfold SphincsSecurity.Seeded.surrogate
  split
  · exact Short.Only.deriveKey _ _ _
  · exact Short.Only.pure' _

theorem Only.spineNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : ∀ steps, Short.Only (spineNode parameter lay tree seed steps :
      OracleComp HashSpec Digest)
  | 0 => by
      rw [SphincsSecurity.Seeded.spineNode]
      exact Only.treeNode _ _ _ _ _ _
  | steps + 1 => by
      rw [SphincsSecurity.Seeded.spineNode]
      refine Short.Only.bind (Only.spineNode parameter lay tree seed steps) (fun _ =>
        Short.Only.bind (Only.surrogate _ _ _) (fun _ => ?_))
      dsimp only
      exact Short.Only.ite _ (Short.Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega))
        (Short.Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega))

theorem Only.treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : Short.Only (treeRoot parameter lay tree seed : OracleComp
        HashSpec Digest) :=
  Only.spineNode _ _ _ _ _

theorem Only.treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) :
    Short.Only (treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest)) :=
  Short.Only.sequenceFin _ fun level => by
    split
    · exact Only.treeNode _ _ _ _ _ _
    · exact Only.surrogate _ _ _

theorem Only.keygenFromSeed (seed : MasterSeed) :
    Short.Only (keygenFromSeed seed : OracleComp HashSpec (PublicKey × SecretKey)) := by
  unfold SphincsSecurity.Seeded.keygenFromSeed
  exact Short.Only.bind (Short.Only.derivePublicSeed _) (fun _ =>
    Short.Only.bind (Short.Only.derivePrf _) (fun _ =>
      Short.Only.bind (Only.treeRoot _ _ _ _) (fun _ => Short.Only.pure' _)))

theorem Only.keygen (seed : MasterSeed) :
    Short.Only (keygen seed : OracleComp HashSpec (PublicKey × SecretKey)) := by
  unfold SphincsSecurity.Seeded.keygen
  exact Only.keygenFromSeed _

theorem Only.signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    Short.Only (signAttempt secretKey message randomness : OracleComp HashSpec (Option Index)) := by
  unfold SphincsSecurity.Seeded.signAttempt
  exact Short.Only.bind (Short.Only.messageDigestCall _ _ _ _ _) (fun _ =>
    Short.Only.ite _ (Short.Only.pure' _) (Short.Only.pure' _))

attribute [local irreducible] SphincsSecurity.Seeded.treeNode SphincsSecurity.Seeded.forsNode
  SphincsSecurity.Seeded.otsSignFrom SphincsSecurity.Seeded.forsKey
  SphincsSecurity.Seeded.treePath

theorem Only.signLayerWith (secretKey : SecretKey) (index : Index) (lay : Layer)
    (message : HashInput) (hmsg : ShortMessage message) :
    Short.Only (signLayerWith secretKey index lay message :
      OracleComp HashSpec (Option (LayerSignature lay))) := by
  unfold SphincsSecurity.Seeded.signLayerWith SphincsSecurity.Seeded.otsSign
  refine Short.Only.bind (Only.otsSignFrom _ _ _ _ _ _ hmsg _ _) (fun result => ?_)
  rcases result with _ | ⟨counter, values⟩
  · exact Short.Only.pure' _
  · exact Short.Only.bind (Only.treePath _ _ _ _ _) (fun _ => Short.Only.pure' _)

theorem Only.signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    Short.Only (signLayer secretKey index lay : OracleComp HashSpec
        (Option (LayerSignature lay))) := by
  unfold SphincsSecurity.Seeded.signLayer SphincsSecurity.Seeded.layerMessage
    SphincsSecurity.Seeded.keyMessage
  split
  · simp only [bind_assoc, pure_bind]
    exact Short.Only.bind (Only.treeRoot _ _ _ _) (fun root =>
      Only.signLayerWith _ _ _ _ (shortMessage_root root))
  · simp only [bind_assoc, pure_bind]
    exact Short.Only.bind (Only.forsKey _ _ _) (fun key =>
      Only.signLayerWith _ _ _ _ (shortMessage_root key))

theorem Only.layerRecover (parameter : PublicParameter) (index : Index) (lay : Layer)
    (message : HashInput) (hmsg : ShortMessage message) (part : LayerSignature lay) :
    Short.Only (layerRecover parameter index lay message part :
      OracleComp HashSpec (Option Digest)) := by
  unfold Concrete.layerRecover
  refine Short.Only.bind (Short.Only.otsLeaf _ _ _ _ _ hmsg _ _) (fun value => ?_)
  rcases value with _ | value
  · exact Short.Only.pure' _
  · exact Short.Only.bind (Short.Only.treeFold _ _ _ _ _ _ _) (fun _ => Short.Only.pure' _)

theorem Only.layerStep (secretKey : SecretKey) (index : Index) (lay : Layer) (below : Digest) :
    Short.Only (layerStep secretKey index lay below :
      OracleComp HashSpec (Option (LayerSignature lay × Digest))) := by
  unfold SphincsSecurity.Seeded.layerStep
  refine Short.Only.bind (Only.signLayerWith _ _ _ _ (shortMessage_root below)) (fun part => ?_)
  rcases part with _ | part
  · exact Short.Only.pure' _
  · refine Short.Only.ite _ (Short.Only.pure' _) ?_
    refine Short.Only.bind (Only.layerRecover _ _ _ _ (shortMessage_root below) _) (fun root => ?_)
    rcases root with _ | root <;> exact Short.Only.pure' _

end Seeded

attribute [local irreducible] SphincsSecurity.Seeded.signLayer SphincsSecurity.Seeded.layerStep
  SphincsSecurity.Seeded.forsOpen

omit [Params] in
theorem Only.sequenceThread {σ : Type} : ∀ {n : Nat} {α : Fin n → Type}
    {computation : (i : Fin n) → σ → OracleComp HashSpec (Option (α i × σ))},
    (∀ i state, Only (computation i state)) → ∀ state, Only (sequenceThread computation state)
  | 0, _, _, _, _ => Only.pure' _
  | _ + 1, α, computation, h, state => by
      unfold SphincsSecurity.Concrete.sequenceThread
      refine Only.bind (h (Fin.last _) state) (fun last => ?_)
      rcases last with _ | ⟨last, next⟩
      · exact Only.pure' _
      · refine Only.bind (Only.sequenceThread (α := fun i => α i.castSucc)
          (fun i => h i.castSucc) next) (fun init => ?_)
        rcases init with _ | init <;> exact Only.pure' _

theorem Only.finishSign (secretKey : SphincsSecurity.Seeded.SecretKey) (message : Message)
    (randomness : Randomness) :
    Only (Seeded.finishSign secretKey message randomness :
      OracleComp HashSpec (Option Signature)) := by
  unfold Seeded.finishSign
  refine Only.bind (Only.messageDigest _ _ _ _) (fun digest => ?_)
  dsimp only
  generalize digestIndex digest = index
  generalize digestLeaves digest = leaves
  refine Only.bind (Seeded.Only.forsOpen _ _ _ _) (fun opening => ?_)
  refine Only.bind (Only.forsRecover _ _ _ _) (fun roots => ?_)
  refine Only.bind (Only.forsPublicKey _ _ _) (fun forsKey => ?_)
  refine Only.bind (Only.sequenceThread
    (fun lay below => Seeded.Only.layerStep secretKey index lay below) forsKey) (fun layers => ?_)
  rcases layers with _ | layers <;> exact Only.pure' _

end SphincsSecurity.Security.Short
