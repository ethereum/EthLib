module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.IdealStatement
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.StatementLemmas
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.ForgeryCases

@[expose] public section

open EthLib.Cryptography

open OracleSpec

namespace XmssSecurity.Concrete

theorem strong_components {signedMessage forgedMessage : Message}
    {signedSignature forgedSignature : Signature}
    (hstrong : signedMessage ≠ forgedMessage ∨ signedSignature ≠ forgedSignature)
    (htop : signedSignature.top = forgedSignature.top) :
    (signedMessage, signedSignature.randomness) ≠
        (forgedMessage, forgedSignature.randomness) ∨
      signedSignature.chainValue ≠ forgedSignature.chainValue ∨
      signedSignature.authPath ≠ forgedSignature.authPath := by
  by_cases hinput :
      (signedMessage, signedSignature.randomness) =
        (forgedMessage, forgedSignature.randomness)
  · by_cases hvalues : signedSignature.chainValue = forgedSignature.chainValue
    · right
      right
      intro hpath
      apply hstrong.elim
      · intro hmessage
        exact hmessage (congrArg Prod.fst hinput)
      · intro hsignature
        apply hsignature
        cases signedSignature
        cases forgedSignature
        simp_all
    · exact Or.inr (Or.inl hvalues)
  · exact Or.inl hinput

noncomputable def SameLeafIndexBadEventOccurs
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signedMessage forgedMessage : Message)
    (signedEncoding forgedEncoding : Encoding)
    (signedSignature forgedSignature : Signature)
    (hsignedValid : TargetSum.Valid signedEncoding) : BadEvent → Prop :=
  XmssSecurity.SameLeafIndexBadEventOccurs
    (CacheView.encodingHash cache parameter leafIndex)
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeAt cache parameter .bottom) leafIndex.val
    (signedMessage, signedSignature.randomness)
    (forgedMessage, forgedSignature.randomness)
    signedEncoding forgedEncoding
    signedSignature.chainValue forgedSignature.chainValue
    signedSignature.authPath forgedSignature.authPath
    hsignedValid

/-- Concrete same-leaf-index strong forgeries select one of the 175 cache-level bad events. -/
theorem sameLeafIndex_forgery_has_badEvent
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signedMessage forgedMessage : Message)
    (signedEncoding forgedEncoding : Encoding)
    (signedSignature forgedSignature : Signature)
    (hsignedEncoding : TargetSum.decodeDigest
      (CacheView.encodingHash cache parameter leafIndex
        (signedMessage, signedSignature.randomness)) = some signedEncoding)
    (hforgedEncoding : TargetSum.decodeDigest
      (CacheView.encodingHash cache parameter leafIndex
        (forgedMessage, forgedSignature.randomness)) = some forgedEncoding)
    (hroot : (Merkle.climb (CacheView.nodeAt cache parameter .bottom) 0 leafIndex.val
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            forgedEncoding forgedSignature.chainValue))
        (List.ofFn forgedSignature.authPath)).run =
      (Merkle.climb (CacheView.nodeAt cache parameter .bottom) 0 leafIndex.val
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            signedEncoding signedSignature.chainValue))
        (List.ofFn signedSignature.authPath)).run)
    (hstrong : signedMessage ≠ forgedMessage ∨ signedSignature ≠ forgedSignature)
    (htop : signedSignature.top = forgedSignature.top) :
    ∃ event, SameLeafIndexBadEventOccurs cache parameter leafIndex
      signedMessage forgedMessage signedEncoding forgedEncoding
      signedSignature forgedSignature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2 event := by
  exact XmssSecurity.sameLeafIndex_forgery_has_badEvent
    (CacheView.encodingHash cache parameter leafIndex)
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeAt cache parameter .bottom) leafIndex.val
    (signedMessage, signedSignature.randomness)
    (forgedMessage, forgedSignature.randomness)
    signedEncoding forgedEncoding
    signedSignature.chainValue forgedSignature.chainValue
    signedSignature.authPath forgedSignature.authPath
    hsignedEncoding hforgedEncoding hroot (strong_components hstrong htop)

noncomputable def FreshLeafIndexBadEventOccurs
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (forgedEncoding : Encoding) (forgedSignature : Signature)
    (secret : ChainIndex → Digest) (honestPath : Fin treeHeight → Digest)
    (hforgedValid : TargetSum.Valid forgedEncoding) : BadEvent → Prop :=
  XmssSecurity.FreshLeafIndexBadEventOccurs
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeAt cache parameter .bottom) leafIndex.val
    forgedEncoding forgedSignature.chainValue secret
    forgedSignature.authPath honestPath hforgedValid

/-- Concrete fresh-leaf-index forgeries select one of the same 175 cache-level bad events. -/
theorem freshLeafIndex_forgery_has_badEvent
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (forgedEncoding : Encoding) (forgedSignature : Signature)
    (secret : ChainIndex → Digest) (honestPath : Fin treeHeight → Digest)
    (hforgedValid : TargetSum.Valid forgedEncoding)
    (hroot : (Merkle.climb (CacheView.nodeAt cache parameter .bottom) 0 leafIndex.val
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            forgedEncoding forgedSignature.chainValue))
        (List.ofFn forgedSignature.authPath)).run =
      (Merkle.climb (CacheView.nodeAt cache parameter .bottom) 0 leafIndex.val
        (CacheView.leafHash cache parameter leafIndex
          (fun chain => Wots.publicChain
            (CacheView.chainStep cache parameter leafIndex chain) (secret chain)))
        (List.ofFn honestPath)).run) :
    ∃ event, FreshLeafIndexBadEventOccurs cache parameter leafIndex forgedEncoding
      forgedSignature secret honestPath hforgedValid event := by
  exact XmssSecurity.freshLeafIndex_forgery_has_badEvent
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeAt cache parameter .bottom) leafIndex.val
    forgedEncoding forgedSignature.chainValue secret
    forgedSignature.authPath honestPath hforgedValid hroot

/-! ### The top layer -/

/-- The honest bottom root of tree `b`, replayed from the cache. -/
def bottomRoot (cache : QueryCache HashSpec) (secretKey : SecretKey) (key : TopIndex) : Digest :=
  CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart treeHeight (bottomRootNode key)

/-- The honest top path of key `b`, replayed from the cache. -/
def honestTopPath (cache : QueryCache HashSpec) (secretKey : SecretKey) (key : TopIndex)
    (level : Fin treeHeight) : Digest :=
  CacheReplay.topTreeNode cache secretKey.parameter secretKey.topChainStart level
    (topPathNode key level)

/-- The honest top chain values of key `b` at a codeword, replayed from the cache. -/
def honestTopValues (cache : QueryCache HashSpec) (secretKey : SecretKey) (key : TopIndex)
    (encoding : Encoding) : ChainIndex → Digest :=
  fun chain => Wots.signChain (CacheView.topChainStep cache secretKey.parameter key chain)
    (encoding chain) (secretKey.topChainStart key chain)

/-- A top-layer bad event for a forged top signature `forged` of bottom root `root` by key `b`.

Its digest decodes to the forged encoding.

The event is against the honest top signature of tree `b` if its grinding succeeded.

Otherwise it is against the top key's secrets. -/
noncomputable def TopBadEventOccurs (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (key : TopIndex) (root : Digest) (forged : LayerSignature) (forgedEncoding : Encoding)
    (event : BadEvent) : Prop :=
  match secretKey.topSigned key with
  | some (randomness, encoding) =>
      ∃ hvalid : TargetSum.Valid encoding,
        XmssSecurity.SameLeafIndexBadEventOccurs
          (CacheView.topEncodingHash cache secretKey.parameter key)
          (fun chain => CacheView.topChainStep cache secretKey.parameter key chain)
          (CacheView.topLeafHash cache secretKey.parameter key)
          (CacheView.nodeAt cache secretKey.parameter .top) key.val
          (bottomRoot cache secretKey key, randomness) (root, forged.randomness)
          encoding forgedEncoding
          (honestTopValues cache secretKey key encoding) forged.chainValue
          (honestTopPath cache secretKey key) forged.authPath hvalid event
  | none =>
      ∃ hvalid : TargetSum.Valid forgedEncoding,
        XmssSecurity.FreshLeafIndexBadEventOccurs
          (fun chain => CacheView.topChainStep cache secretKey.parameter key chain)
          (CacheView.topLeafHash cache secretKey.parameter key)
          (CacheView.nodeAt cache secretKey.parameter .top) key.val
          forgedEncoding forged.chainValue (secretKey.topChainStart key)
          forged.authPath (honestTopPath cache secretKey key) hvalid event

end XmssSecurity.Concrete
