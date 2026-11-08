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
open EthLib.Cryptography.HashSig (toList_data_append toList_data_packBytes)

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSig.HashSpec m]

/-! ## The tweakable hash -/

/-- The bytes of a digest's encoding, as a payload. -/
theorem toList_data_packBytes_ofDigest (v : SphincsSecurity.Digest) :
    (packBytes (ofDigest v)).data.toList = SphincsSecurity.bytesLE 16 v := by
  simp

/-- The first 16 bytes of an answer, read as bytes, are the bytes of the model's truncation. -/
theorem trunc_oracleHash (input : HashSig.HashInput) :
    (do let x ← ofOutput <$> HashSig.oracleHash (m := m) input; pure (trunc N x))
      = ofDigest <$>
          (do let a ← HashSig.oracleHash (m := m) input; pure (HashSig.truncateHash a)) := by
  simp only [bind_map_left, trunc_ofOutput_truncateHash, map_bind, map_pure]

/-- EthLib's `Th` with the query hashes `PK.seed`, the address and the payload, in that order. -/
theorem th_queryH_input (P : SphincsSecurity.PublicParameter) (A : Adrs) (payload : ByteArray)
    (input : HashSig.HashInput)
    (hinput : SphincsSecurity.bytesLE 16 P ++ A.toList ++ payload.data.toList = input) :
    th (queryH (m := m)) (ofParam P) A payload
      = ofDigest <$>
          (do let a ← HashSig.oracleHash (m := m) input; pure (HashSig.truncateHash a)) := by
  rw [th, ← trunc_oracleHash]
  simp only [queryH, thInput, toList_data_append, toList_data_packBytes, toList_ofParam, hinput]

/-- EthLib's `Th` with the query is the model's, at the same address and payload bytes. -/
theorem th_queryH (P : SphincsSecurity.PublicParameter) (A : Adrs) (payload : ByteArray)
    (domain : SphincsSecurity.HashDomain) (msg : HashSig.HashInput)
    (hA : A.toList = tweakBytes domain) (hpayload : payload.data.toList = msg) :
    th (queryH (m := m)) (ofParam P) A payload
      = ofDigest <$> tweakableHash (m := m) P domain msg := by
  rw [th_queryH_input P A payload _ (by rw [hA, hpayload])]
  rfl

/-! ## Derivations from the seed -/

/-- `PRF(PK.seed, SK.seed, ADRS)` is the model's derivation of the same domain. -/
theorem prf_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (A : Adrs) (domain : SphincsSecurity.KeygenDomain)
    (hA : A.toList = fieldBytes (SphincsSecurity.keygenDomainFields domain)) :
    prf (queryH (m := m)) (ofParam P) (ofSeed S) A
      = ofDigest <$> SphincsSecurity.deriveKey (m := m) P domain S := by
  rw [prf, th_queryH_input P A _ (SphincsSecurity.keygenHashInput P domain S)
    (by simp only [hA, toList_data_packBytes, toList_ofSeed]; rfl)]
  rfl

/-- The 44 bytes of a key expansion are the model's key-seed input of the same domain. -/
theorem toList_expandInput (S : SphincsSecurity.MasterSeed) (domain : UInt8) :
    (expandInput (ofSeed S) domain).data.toList
      = SphincsSecurity.keySeedInput S domain.toNat := by
  simp only [expandInput, toList_data_append, toList_data_packBytes, toList_ofSeed,
    SphincsSecurity.keySeedInput, UInt8.ofNat_toNat]
  rfl

/-- The model's `PK.seed` and `SK.prf` as EthLib's expanded key. -/
def ofExpanded (P : SphincsSecurity.PublicParameter) (prf : HashSig.HashOutput) :
    ExpandedKey :=
  { pkSeed := ofParam P, skPrf := ofOutput prf }

/-- A computation that reads the model's `PK.seed` reads the truncation of its key-seed hash. -/
theorem derivePublicSeed_bind {γ : Type} (S : SphincsSecurity.MasterSeed)
    (g : SphincsSecurity.PublicParameter → m γ) :
    SphincsSecurity.derivePublicSeed (m := m) S >>= g
      = HashSig.oracleHash (m := m) (SphincsSecurity.keySeedInput S 0) >>= fun a =>
          g (HashSig.truncateHash a) :=
  (bind_assoc _ _ _).trans (bind_congr fun _ => pure_bind _ _)

/-- The key expansion is the model's two key-seed hashes, `PK.seed` first. -/
theorem expandKey_queryH (S : SphincsSecurity.MasterSeed) :
    expandKey (queryH (m := m)) (ofSeed S)
      = (do
          let P ← SphincsSecurity.derivePublicSeed (m := m) S
          let prf ← SphincsSecurity.derivePrf (m := m) S
          pure (ofExpanded P prf)) := by
  rw [derivePublicSeed_bind, SphincsSecurity.derivePrf]
  simp only [expandKey, queryH, toList_expandInput, bind_map_left,
    trunc_ofOutput_truncateHash, UInt8.reduceToNat]
  exact bind_congr fun _ => bind_congr fun _ => rfl

/-- The 93 bytes that `PRF_msg` hashes are the model's randomizer input. -/
theorem toList_prfMsgInput (prf : HashSig.HashOutput) (P : SphincsSecurity.PublicParameter)
    (msg : SphincsSecurity.Message) :
    (packBytes (n := HASH_LEN) (ofOutput prf) ++ packBytes (ofParam P)
        ++ framedMessage (ofMessage msg)).data.toList
      = SphincsSecurity.randomizerHashInput prf P msg := by
  simp only [framedMessage, toList_data_append, toList_data_packBytes_ofOutput,
    toList_data_packBytes, toList_ofParam, toList_ofMessage, SphincsSecurity.randomizerHashInput,
    SphincsSecurity.framedMessage, List.append_assoc, seedTag_eq, ofNat_length_seedTag]

/-- The randomizer is the first half of the model's randomizer hash. -/
theorem prfMsg_queryH (prf : HashSig.HashOutput) (P : SphincsSecurity.PublicParameter)
    (msg : SphincsSecurity.Message) :
    prfMsg (queryH (m := m)) (ofOutput prf : HashOutput) (ofParam P) (ofMessage msg)
      = (fun walk => ofRandomizer walk.1) <$>
          SphincsSecurity.deriveRandomizer (m := m) prf P msg := by
  conv_rhs => simp only [SphincsSecurity.deriveRandomizer, map_bind, map_pure]
  simp only [prfMsg, queryH, toList_prfMsgInput, bind_map_left, trunc_ofOutput_truncateHash]
  exact bind_congr fun _ => rfl

/-! ## Chains, leaves and nodes -/

/-- One step of a chain. -/
theorem chainStep_queryH (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (leaf : SphincsSecurity.LeafIndex) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (v : SphincsSecurity.Digest) :
    chainStep (queryH (m := m)) (ofParam P) (keyOf lay tree leaf) i mu (ofDigest v)
      = ofDigest <$> tweakableHash (m := m) P (.chain lay tree leaf ⟨i.val, i.isLt⟩
          ⟨mu.val, mu.isLt⟩) (SphincsSecurity.bytesLE 16 v) :=
  th_queryH P _ _ _ _ (toList_adrsChain lay tree leaf i mu) (toList_data_packBytes_ofDigest v)

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

/-- The bytes of the digests of a function on `n` values, in order, as the model's payload. -/
theorem toList_packDigests {n : Nat} (f : Fin n → SphincsSecurity.Digest) :
    (packDigests (Vector.ofFn fun i => ofDigest (f i))).data.toList
      = (List.ofFn f).flatMap (SphincsSecurity.bytesLE 16) := by
  have hflat : ∀ {n} (ds : Vector Digest n),
      (packDigests ds).data.toList = (ds.toList.map Vector.toList).flatten := by
    intro n ds
    simp [packDigests, packBytes, Vector.flatten, Array.toList_flatten, Vector.toList]
    rfl
  rw [hflat, Vector.toList_ofFn, List.map_ofFn]
  simp only [Function.comp_def, toList_ofDigest]
  exact congrArg List.flatten (List.map_ofFn (f := f) (g := SphincsSecurity.bytesLE 16)).symm

/-- The bytes of the chain ends, in order, as the model's leaf payload. -/
theorem toList_packDigests_chains (f : SphincsSecurity.ChainIndex → SphincsSecurity.Digest) :
    (packDigests (Vector.ofFn fun i : Fin V => ofDigest (f ⟨i.val, i.isLt⟩))).data.toList
      = SphincsSecurity.Concrete.leafPayload f :=
  toList_packDigests (n := V) fun i => f ⟨i.val, i.isLt⟩

/-- A key's leaf, from its chain ends. -/
theorem otsLeafHash_queryH (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (leaf : SphincsSecurity.LeafIndex)
    (ends : SphincsSecurity.ChainIndex → SphincsSecurity.Digest) :
    otsLeafHash (queryH (m := m)) (ofParam P) (keyOf lay tree leaf)
        (Vector.ofFn fun i : Fin V => ofDigest (ends ⟨i.val, i.isLt⟩))
      = ofDigest <$> SphincsSecurity.Concrete.leafHash (m := m) P lay tree leaf ends :=
  th_queryH P _ _ _ _ (toList_adrsPk lay tree leaf) (toList_packDigests_chains ends)

/-- A tree node at height `z` and index `j`, from its two children. -/
theorem nodeHash_queryH (P : SphincsSecurity.PublicParameter) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (z j : Nat) (left right : SphincsSecurity.Digest) :
    nodeHash (queryH (m := m)) (ofParam P) (layerOf lay) tree.val z j (ofDigest left)
        (ofDigest right)
      = ofDigest <$> tweakableHash (m := m) P (.node lay tree z j)
          (SphincsSecurity.Concrete.nodePayload left right) :=
  th_queryH P _ _ _ _ (toList_adrsNode lay tree z j) (by
    simp [SphincsSecurity.Concrete.nodePayload])

/-! ## FORS -/

/-- The secret of a FORS leaf is the model's derivation. -/
theorem forsSecret_queryH (S : SphincsSecurity.MasterSeed) (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) (leaf : SphincsSecurity.FLeaf) :
    forsSecret (prf (queryH (m := m)) (ofParam P) (ofSeed S)) index.val (treeOf κ) leaf.val
      = ofDigest <$> SphincsSecurity.Seeded.forsSecret (m := m) P index κ leaf S :=
  prf_queryH S P _ _ (toList_adrsFprf index κ leaf)

/-- A FORS leaf, from its secret. -/
theorem forsLeafHash_queryH (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (κ : SphincsSecurity.FTree) (leaf : SphincsSecurity.FLeaf) (secret : SphincsSecurity.Digest) :
    forsLeafHash (queryH (m := m)) (ofParam P) index.val (treeOf κ) leaf.val (ofDigest secret)
      = ofDigest <$> SphincsSecurity.Concrete.forsLeafHash (m := m) P index κ leaf secret :=
  th_queryH P _ _ _ _ (toList_adrsFors_leaf index κ leaf) (toList_data_packBytes_ofDigest secret)

/-- A FORS node at height `level + 1`, from its two children, below the width of its height. -/
theorem forsNodeHash_queryH (P : SphincsSecurity.PublicParameter) (index : SphincsSecurity.Index)
    (κ : SphincsSecurity.FTree) (level : SphincsSecurity.FLevel) (node : SphincsSecurity.FLeaf)
    (hnode : node.val < 2 ^ (FORS_HEIGHT - (level.val + 1))) (left right : SphincsSecurity.Digest) :
    forsNodeHash (queryH (m := m)) (ofParam P) index.val (treeOf κ) (level.val + 1) node.val
        (ofDigest left) (ofDigest right)
      = ofDigest <$> tweakableHash (m := m) P (.forsNode index κ level node)
          (SphincsSecurity.Concrete.nodePayload left right) :=
  th_queryH P _ _ _ _ (toList_adrsFors_node index κ level node hnode) (by
    simp [SphincsSecurity.Concrete.nodePayload])

/-- A FORS node at height `level + 1` and index `j`, below the width of its height.

The model stores its index as a FORS leaf, modulo `2^10`. -/
theorem forsNodeHash_queryH_mod (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree) (level : SphincsSecurity.FLevel)
    (j : Nat) (hj : j < 2 ^ (FORS_HEIGHT - (level.val + 1))) (left right : SphincsSecurity.Digest) :
    forsNodeHash (queryH (m := m)) (ofParam P) index.val (treeOf κ) (level.val + 1) j
        (ofDigest left) (ofDigest right)
      = ofDigest <$> tweakableHash (m := m) P (.forsNode index κ level
          ⟨j % 2 ^ SphincsSecurity.forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
          (SphincsSecurity.Concrete.nodePayload left right) := by
  -- The index is below `2^10`, so the model's reduction keeps it.
  have hmod : j % 2 ^ SphincsSecurity.forsHeight = j :=
    Nat.mod_eq_of_lt (hj.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)))
  have h := forsNodeHash_queryH (m := m) P index κ level
    ⟨j % 2 ^ SphincsSecurity.forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    (by simp only [hmod]; exact hj) left right
  rwa [show (⟨j % 2 ^ SphincsSecurity.forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :
    SphincsSecurity.FLeaf).val = j from hmod] at h

/-- The bytes of the FORS roots, in order, as the model's payload of `T_k`. -/
theorem toList_packDigests_roots (roots : SphincsSecurity.ForsKey) :
    (packDigests (Vector.ofFn fun κ : Fin FORS_TREES =>
        ofDigest (roots ⟨κ.val, κ.isLt⟩))).data.toList
      = SphincsSecurity.Concrete.rootsPayload roots :=
  toList_packDigests (n := FORS_TREES) fun κ => roots ⟨κ.val, κ.isLt⟩

/-- The FORS public key `T_k` of the roots. -/
theorem forsPkFromRoots_queryH (P : SphincsSecurity.PublicParameter)
    (index : SphincsSecurity.Index) (roots : SphincsSecurity.ForsKey) :
    forsPkFromRoots (queryH (m := m)) (ofParam P) index.val
        (Vector.ofFn fun κ : Fin FORS_TREES => ofDigest (roots ⟨κ.val, κ.isLt⟩))
      = ofDigest <$> SphincsSecurity.Concrete.forsPublicKey (m := m) P index roots :=
  th_queryH P _ _ _ _ (toList_adrsRoots index) (toList_packDigests_roots roots)

/-! ## The message digest -/

/-- The 84 bytes of digest call `i`: `R`, `PK.seed`, `PK.root`, the message, then `BE_32(i)`. -/
theorem toList_digestInput (P : SphincsSecurity.PublicParameter) (root : SphincsSecurity.Digest)
    (msg : SphincsSecurity.Message) (rho : SphincsSecurity.Randomness)
    (call : SphincsSecurity.DigestCall) :
    (packBytes (ofRandomizer rho) ++ packBytes (ofParam P) ++ packBytes (ofDigest root)
        ++ packBytes (ofMessage msg) ++ packBytes (toByte 4 call.val)).data.toList
      = SphincsSecurity.messageDigestInput P root msg rho call := by
  simp only [toList_data_append, toList_data_packBytes, toList_ofRandomizer, toList_ofParam,
    toList_ofDigest, toList_ofMessage, toList_toByte_bytesBE, SphincsSecurity.messageDigestInput]

omit [LawfulMonad m] in
/-- A digest call of `H_msg` is the model's digest call. -/
theorem digestCall_queryH (P : SphincsSecurity.PublicParameter) (root : SphincsSecurity.Digest)
    (msg : SphincsSecurity.Message) (rho : SphincsSecurity.Randomness)
    (call : SphincsSecurity.DigestCall) :
    queryH (m := m) (packBytes (ofRandomizer rho) ++ packBytes (ofParam P)
        ++ packBytes (ofDigest root) ++ packBytes (ofMessage msg) ++ packBytes (toByte 4 call.val))
      = ofOutput <$> SphincsSecurity.Concrete.messageDigestCall (m := m) P root msg rho call := by
  rw [queryH, toList_digestInput]
  rfl

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
