module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Address
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme

/-!
# Proofs: EthLib's hash calls are the model's

EthLib's algorithms take the hash `H` as an argument.

Passed a query to the model's oracle, each hash call of EthLib is the model's call.

It hashes the same bytes, and its answer is the model's answer as bytes.

The equalities hold in every lawful monad with a query to the oracle.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open SphincsSecurity (tweakBytes fieldBytes)
open SphincsSecurity.Concrete (tweakableHash)

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSig.HashSpec m]

/-! ## The tweakable hash -/

/-- The bytes of a digest's encoding, as a payload. -/
theorem toList_data_packBytes_ofDigest (v : SphincsSecurity.Digest) :
    (packBytes (ofDigest v)).data.toList = SphincsSecurity.bytesLE 16 v := by
  simp

omit [LawfulMonad m] in
/-- EthLib's whole-output hash with the query is the model's oracle call, on the same bytes. -/
theorem thFull_queryH (P : SphincsSecurity.PublicParameter) (A : Address) (payload : ByteArray)
    (fields : SphincsSecurity.TweakFields) (msg : HashSig.HashInput)
    (hA : A.toList = fieldBytes fields) (hpayload : payload.data.toList = msg) :
    thFull (queryH (m := m)) (ofParam P) A payload
      = ofOutput <$> HashSig.oracleHash (m := m)
          (SphincsSecurity.bytesLE 16 P ++ fieldBytes fields ++ msg) := by
  simp only [thFull, queryH, thInput, toList_data_append, toList_data_packBytes, hA, hpayload]
  rfl

/-- The first half of an answer, read as bytes, is the bytes of the model's truncation. -/
theorem halfOf_zero_oracleHash {α : Type} (input : HashSig.HashInput) (f : Digest → α) :
    (do let x ← ofOutput <$> HashSig.oracleHash (m := m) input; pure (f (halfOf 0 x)))
      = (do let a ← HashSig.oracleHash (m := m) input
            pure (f (ofDigest (HashSig.truncateHash a)))) := by
  simp only [bind_map_left, halfOf_zero_ofOutput]

/-- EthLib's `Th` with the query is the model's, at the same address and payload bytes. -/
theorem th_queryH (P : SphincsSecurity.PublicParameter) (A : Address) (payload : ByteArray)
    (domain : SphincsSecurity.HashDomain) (msg : HashSig.HashInput)
    (hA : A.toList = tweakBytes domain) (hpayload : payload.data.toList = msg) :
    th (queryH (m := m)) (ofParam P) A payload
      = ofDigest <$> tweakableHash (m := m) P domain msg := by
  rw [th, thFull_queryH P A payload _ msg hA hpayload, tweakableHash, map_bind]
  simp only [map_pure]
  exact halfOf_zero_oracleHash (m := m) _ id

/-! ## Derivations from the seed -/

omit [LawfulMonad m] in
/-- A derivation from the scheme seed is the model's derivation, all 32 bytes. -/
theorem seedPrf_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (A : Address) (domain : SphincsSecurity.KeygenDomain)
    (hA : A.toList = fieldBytes (SphincsSecurity.keygenDomainFields domain)) :
    seedPrf (queryH (m := m)) (ofSeed S) (ofParam P) A .empty
      = ofOutput <$> SphincsSecurity.deriveOutput (m := m) P domain S := by
  rw [seedPrf, thFull_queryH P A _ _ (SphincsSecurity.bytesLE 32 S) hA (by simp)]
  rfl

/-- The derivation of the public parameter, from the all-zero parameter. -/
theorem publicParamOf_queryH (S : SphincsSecurity.MasterSeed) :
    publicParamOf (seedPrf (queryH (m := m)) (ofSeed S))
      = ofParam <$> SphincsSecurity.deriveKey (m := m) 0 .parameter S := by
  -- The all-zero parameter is the bytes of the zero bit vector.
  have hzero : Vector.replicate PUBLIC_PARAM_LEN (0 : UInt8)
      = ofParam (0 : SphincsSecurity.PublicParameter) := by
    rw [ofParam, ofBV_eq_uintToBytes]
    apply Vector.ext
    intro i hi
    simp [uintToBytes]
  unfold publicParamOf
  rw [hzero, seedPrf_queryH S 0 addrParam .parameter toList_addrParam]
  simp only [SphincsSecurity.deriveKey, SphincsSecurity.deriveOutput, map_bind, map_pure]
  exact halfOf_zero_oracleHash (m := m) _ id

/-- The randomizer is the first half of the model's randomizer hash. -/
theorem randomizer_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (msg : SphincsSecurity.Message) :
    randomizer (ofParam P) (seedPrf (queryH (m := m)) (ofSeed S)) (ofMessage msg)
      = (fun walk => ofRandomizer walk.1) <$>
          SphincsSecurity.deriveRandomizer (m := m) P S msg := by
  unfold randomizer seedPrf
  rw [thFull_queryH P addrRnd _ _ (SphincsSecurity.bytesLE 32 S ++ SphincsSecurity.bytesLE 32 msg)
    toList_addrRnd (by simp)]
  simp only [SphincsSecurity.deriveRandomizer, SphincsSecurity.randomizerHashInput, map_bind,
    map_pure, List.append_assoc]
  exact halfOf_zero_oracleHash (m := m) _ id

omit [LawfulMonad m] in
/-- The scheme seed is the model's, the whole hash of the tag and `S_0`. -/
theorem schemeSeed_queryH (S0 : SphincsSecurity.MasterSeed) :
    schemeSeed (queryH (m := m)) (ofSeed S0)
      = ofSeed <$> SphincsSecurity.schemeSeed (m := m) S0 := by
  have hinput : (ByteArray.mk SEED_TAG.toArray ++ packBytes (ofSeed S0)).data.toList
      = SphincsSecurity.schemeSeedInput S0 := by
    simp only [toList_data_append, toList_data_packBytes, toList_ofSeed]
    rfl
  unfold schemeSeed queryH
  rw [hinput]
  rfl

/-! ## Chains, leaves and nodes -/

/-- One step of a chain. -/
theorem chainStep_queryH (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (leaf : SphincsSecurity.LeafIndex) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (v : SphincsSecurity.Digest) :
    chainStep (queryH (m := m)) (ofParam P) (keyOf lay tree leaf) i mu (ofDigest v)
      = ofDigest <$> tweakableHash (m := m) P (.chain lay tree leaf ⟨i.val, i.isLt⟩
          ⟨mu.val, mu.isLt⟩) (SphincsSecurity.bytesLE 16 v) :=
  th_queryH P _ _ _ _ (toList_addrChain lay tree leaf i mu) (toList_data_packBytes_ofDigest v)

/-- A walk along a chain. -/
theorem chain_queryH (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (leaf : SphincsSecurity.LeafIndex) (i : Fin V)
    (start : Nat) : ∀ (steps : Nat) (h : start + steps < CHAIN_LENGTH) (v : SphincsSecurity.Digest),
    chain (queryH (m := m)) (ofParam P) (keyOf lay tree leaf) i start steps h (ofDigest v)
      = ofDigest <$> SphincsSecurity.Concrete.chainWalk (m := m) P lay tree leaf
          ⟨i.val, i.isLt⟩ start steps v
  | 0, _, v => by simp [chain, Wots.chain, SphincsSecurity.Concrete.chainWalk, map_pure]
  | s + 1, h, v => by
    have ih := chain_queryH P lay tree leaf i start s (by omega) v
    unfold chain at ih
    rw [chain, Wots.chain, ih, bind_map_left]
    clear ih
    simp only [SphincsSecurity.Concrete.chainWalk, map_bind]
    refine bind_congr fun prev => ?_
    -- The step stays on the chain, so the model takes the step too.
    have hs : start + s < SphincsSecurity.chainLength - 1 := by
      simp only [SphincsSecurity.chainLength, SphincsSecurity.winternitzBits, CHAIN_LENGTH] at *
      omega
    simp only [hs, ↓reduceDIte]
    exact chainStep_queryH P lay tree leaf i _ prev

/-- The bytes of the digests of a function on chains, in order, as the model's leaf payload. -/
theorem toList_packDigests (f : SphincsSecurity.ChainIndex → SphincsSecurity.Digest) :
    (packDigests (Vector.ofFn fun i : Fin V => ofDigest (f ⟨i.val, i.isLt⟩))).data.toList
      = SphincsSecurity.Concrete.leafPayload f := by
  have hflat : ∀ {n} (ds : Vector Digest n),
      (packDigests ds).data.toList = (ds.toList.map Vector.toList).flatten := by
    intro n ds
    simp [packDigests, packBytes, Vector.flatten, Array.toList_flatten, Vector.toList]
    rfl
  rw [hflat, Vector.toList_ofFn, List.map_ofFn, SphincsSecurity.Concrete.leafPayload]
  simp [List.flatMap, Function.comp_def]
  rfl

/-- A key's leaf, from its chain ends. -/
theorem otsLeafHash_queryH (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (leaf : SphincsSecurity.LeafIndex)
    (ends : SphincsSecurity.ChainIndex → SphincsSecurity.Digest) :
    otsLeafHash (queryH (m := m)) (ofParam P) (keyOf lay tree leaf)
        (Vector.ofFn fun i : Fin V => ofDigest (ends ⟨i.val, i.isLt⟩))
      = ofDigest <$> SphincsSecurity.Concrete.leafHash (m := m) P lay tree leaf ends :=
  th_queryH P _ _ _ _ (toList_addrLeaf lay tree leaf) (toList_packDigests ends)

/-- A tree node at level `level`, `1 <= level <= 10`, from its two children. -/
theorem nodeHash_queryH (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (level j : Nat) (hlevel : level ≤ TOP_HEIGHT)
    (left right : SphincsSecurity.Digest) :
    nodeHash (queryH (m := m)) (ofParam P) (layerOf lay) tree.val level j (ofDigest left)
        (ofDigest right)
      = ofDigest <$> tweakableHash (m := m) P (.node lay tree level j)
          (SphincsSecurity.Concrete.nodePayload left right) :=
  th_queryH P _ _ _ _ (toList_addrNode lay tree level j hlevel) (by
    simp [SphincsSecurity.Concrete.nodePayload])

/-! ## FORS -/

/-- A FORS leaf, from its secret. -/
theorem forsLeafHash_queryH (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (κ : SphincsSecurity.FTree) (leaf : SphincsSecurity.FLeaf) (secret : SphincsSecurity.Digest) :
    forsLeafHash (queryH (m := m)) (ofParam P) index.val (treeOf κ) leaf (ofDigest secret)
      = ofDigest <$> SphincsSecurity.Concrete.forsLeafHash (m := m) P index κ leaf secret :=
  th_queryH P _ _ _ _ (toList_addrForsLeaf index κ leaf) (toList_data_packBytes_ofDigest secret)

/-- A FORS node at tree level `level + 1`, from its two children. -/
theorem forsNodeHash_queryH (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (κ : SphincsSecurity.FTree) (level : SphincsSecurity.FLevel) (node : SphincsSecurity.FLeaf)
    (left right : SphincsSecurity.Digest) :
    forsNodeHash (queryH (m := m)) (ofParam P) index.val (treeOf κ) (level.val + 1) node.val
        (ofDigest left) (ofDigest right)
      = ofDigest <$> tweakableHash (m := m) P (.forsNode index κ level node)
          (SphincsSecurity.Concrete.nodePayload left right) :=
  th_queryH P _ _ _ _ (toList_addrForsNode index κ level node) (by
    simp [SphincsSecurity.Concrete.nodePayload])

omit [LawfulMonad m] in
/-- A derivation of the secrets of a pair of FORS leaves. -/
theorem forsPrf_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) (pair : SphincsSecurity.FPair) :
    seedPrf (queryH (m := m)) (ofSeed S) (ofParam P) (addrForsPrf index.val (treeOf κ)
        ⟨pair.val, pair.isLt⟩) .empty
      = ofOutput <$> SphincsSecurity.deriveOutput (m := m) P (.fors index κ pair) S :=
  seedPrf_queryH S P _ _ (toList_addrForsPrf index κ pair)

omit [LawfulMonad m] in
/-- A derivation of the starts of a pair of chains. -/
theorem otsPrf_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) (pair : SphincsSecurity.ChainPair) :
    seedPrf (queryH (m := m)) (ofSeed S) (ofParam P) (addrPrf (keyOf lay tree leaf)
        ⟨pair.val, pair.isLt⟩) .empty
      = ofOutput <$> SphincsSecurity.deriveOutput (m := m) P (.ots lay tree leaf pair) S :=
  seedPrf_queryH S P _ _ (toList_addrPrf lay tree leaf pair)

/-! ## The message digest -/

omit [LawfulMonad m] in
/-- A digest call: the message, then the randomizer, under the call's address. -/
theorem digestCall_queryH (P : SphincsSecurity.PublicParameter) (root : SphincsSecurity.Digest)
    (msg : SphincsSecurity.Message) (rho : SphincsSecurity.Randomness)
    (call : SphincsSecurity.DigestCall) :
    thFull (queryH (m := m)) (ofParam P) (addrMsg ⟨call.val, call.isLt⟩)
        (packBytes (ofMessage msg) ++ packBytes (ofRandomizer rho))
      = ofOutput <$> SphincsSecurity.Concrete.messageDigestCall (m := m) P root msg rho call := by
  rw [thFull_queryH P _ _ _ (SphincsSecurity.Concrete.messageDigestPayload root msg rho)
    (toList_addrMsg call) (by simp [SphincsSecurity.Concrete.messageDigestPayload])]
  rfl

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
