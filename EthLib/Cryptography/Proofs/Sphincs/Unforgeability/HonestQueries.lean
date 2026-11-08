module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Cryptography.Proofs.QueryAvoidance
public import EthLib.Cryptography.Proofs.Sphincs.Address
public import EthLib.Cryptography.Proofs.Sphincs.Serialization
public import EthLib.Cryptography.Proofs.Sphincs.TweakableHash
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.VerifyQueries

/-!
# Proofs: the hash calls of leanSPHINCS key generation and signing

Key generation and signing under a map of monads, and the inputs they never hash.

A map of monads that keeps `pure` and `bind` sends key generation and signing to themselves.

The mapped algorithms take the mapped hash and the mapped secrets.

The random-oracle proof uses this to move the algorithms between oracle worlds.

The honest algorithms make five kinds of call.

- The key expansion, of `"leanSPHINCS" | SK.seed | domain`, 44 bytes.
- `PRF_msg`, of 93 bytes, and `H_msg`, of 84 bytes, neither at an address.
- A `PRF` call, at a derivation address: a chain start or a FORS secret.
- An encoding of a one-time key, at the key's encoding address, with a 20-byte payload.
- A hash at an address of another type, with a payload of at least 16 bytes.

So a query that no call of the other four kinds makes is made only through a `PRF` call.

The encodings are a kind of their own because a key's counter search queries them.

A hypothesis on each key's encodings then shows which calls avoid another key's search inputs.

Every addressed input has the 48 bytes of `PK.seed | ADRS` before a payload of at least 16.

So in the game, the honest algorithms query a 44-byte input only to expand `SK.seed`.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open OracleSpec OracleComp

/-! ## Key generation and signing under a map of monads -/

section Map

variable {m n : Type → Type} [Monad m] [Monad n]
  (φ : ∀ {β : Type}, m β → n β)
  (map_pure : ∀ {β : Type} (b : β), φ (pure b) = pure b)
  (map_bind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ x >>= fun b => φ (f b))
  (H : ByteArray → m (Vector UInt8 32)) (prf : Prf m)

/-- The source of secrets mapped one call at a time. -/
abbrev mapPrf : Prf n := fun adrs => φ (prf adrs)

include map_pure map_bind

/-- The first test that passes, among `fuel` trials, commutes with the map. -/
theorem findFirst_map_monad {κ β : Type} (trial : Nat → κ) (test : κ → m (Option β)) :
    ∀ (c fuel : Nat), φ (Wots.findFirst trial test c fuel)
      = Wots.findFirst trial (fun k => φ (test k)) c fuel
  | _, 0 => map_pure _
  | c, fuel + 1 => by
    simp only [Wots.findFirst, map_bind]
    refine congrArg _ (funext fun r => ?_)
    cases r with
    | none => exact findFirst_map_monad trial test (c + 1) fuel
    | some x => exact map_pure _

/-- The chain starts commute with the map. -/
theorem chainStarts_map_monad (key : OtsKey) :
    φ (chainStarts prf key) = chainStarts (mapPrf φ prf) key :=
  HashSig.ofFnInOrder_map_monad φ map_pure map_bind _ _

/-- A one-time key's leaf, from its secrets, commutes with the map. -/
theorem otsPublicLeaf_map_monad (pkSeed : PkSeed) (key : OtsKey) :
    φ (otsPublicLeaf H pkSeed prf key)
      = otsPublicLeaf (fun x => φ (H x)) pkSeed (mapPrf φ prf) key := by
  rw [otsPublicLeaf, otsPublicLeaf, map_bind, chainStarts_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun starts => ?_)
  simp only [map_bind, HashSig.ofFnInOrder_map_monad φ map_pure map_bind, chain,
    Wots.chain_map_monad φ map_pure map_bind, chainStep_map_monad φ map_pure map_bind, otsLeafHash,
    th_map_monad φ map_pure map_bind]

/-- The counter search commutes with the map. -/
theorem findCounter_map_monad [LawfulMonad m] [LawfulMonad n] (pkSeed : PkSeed) (key : OtsKey)
    (msg : Digest) (c fuel : Nat) :
    φ (Internal.findCounter H pkSeed key msg c fuel)
      = Internal.findCounter (fun x => φ (H x)) pkSeed key msg c fuel := by
  rw [Internal.findCounter, Internal.findCounter, findFirst_map_monad φ map_pure map_bind]
  refine congrArg (fun test => Wots.findFirst UInt32.ofNat test c fuel) (funext fun k => ?_)
  rw [encode, encode, map_monad_map φ map_pure map_bind, th_map_monad φ map_pure map_bind]

/-- A one-time signature commutes with the map. -/
theorem otsSign_map_monad [LawfulMonad m] [LawfulMonad n] (pkSeed : PkSeed) (key : OtsKey)
    (msg : Digest) :
    φ (otsSign H pkSeed prf key msg)
      = otsSign (fun x => φ (H x)) pkSeed (mapPrf φ prf) key msg := by
  rw [otsSign, otsSign, map_bind, findCounter_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun found => ?_)
  cases found with
  | none => exact map_pure _
  | some found =>
    simp only [map_bind, map_pure, chainStarts_map_monad φ map_pure map_bind,
      HashSig.ofFnInOrder_map_monad φ map_pure map_bind, chain,
      Wots.chain_map_monad φ map_pure map_bind, chainStep_map_monad φ map_pure map_bind]

/-- A hypertree node commutes with the map. -/
theorem node_map_monad (pkSeed : PkSeed) (layer : Layer) (tree z j : Nat) :
    φ (node H pkSeed prf layer tree z j)
      = node (fun x => φ (H x)) pkSeed (mapPrf φ prf) layer tree z j := by
  rw [node, node, Merkle.node_map _ φ map_bind]
  simp only [nodeHash_map_monad φ map_pure map_bind, leaves,
    otsPublicLeaf_map_monad φ map_pure map_bind]
  rfl

/-- A tree's root commutes with the map. -/
theorem treeRoot_map_monad (pkSeed : PkSeed) (layer : Layer) (tree : Nat) :
    φ (treeRoot H pkSeed prf layer tree)
      = treeRoot (fun x => φ (H x)) pkSeed (mapPrf φ prf) layer tree :=
  node_map_monad φ map_pure map_bind H prf pkSeed layer tree _ 0

/-- A key's path commutes with the map. -/
theorem path_map_monad (pkSeed : PkSeed) (layer : Layer) (tree e : Nat) :
    φ (path H pkSeed prf layer tree e)
      = path (fun x => φ (H x)) pkSeed (mapPrf φ prf) layer tree e := by
  rw [path, path, Merkle.path_map _ φ map_pure map_bind]
  simp only [nodeHash_map_monad φ map_pure map_bind, leaves,
    otsPublicLeaf_map_monad φ map_pure map_bind]
  rfl

omit [Monad m] [Monad n] map_pure map_bind in
/-- A FORS secret commutes with the map: it is one call of the source. -/
theorem forsSecret_map_monad (idx : Nat) (kappa : Fin FORS_TREES) (s : Nat) :
    φ (forsSecret prf idx kappa s) = forsSecret (mapPrf φ prf) idx kappa s :=
  rfl

/-- A FORS leaf, from its secret, commutes with the map. -/
theorem forsLeaves_map_monad (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES) (s : Nat) :
    φ (forsLeaves H pkSeed prf idx kappa s)
      = forsLeaves (fun x => φ (H x)) pkSeed (mapPrf φ prf) idx kappa s := by
  rw [forsLeaves, forsLeaves, map_bind, forsSecret_map_monad φ]
  simp only [forsLeafHash, th_map_monad φ map_pure map_bind]

/-- A FORS node commutes with the map. -/
theorem forsNode_map_monad (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES) (z j : Nat) :
    φ (forsNode H pkSeed prf idx kappa z j)
      = forsNode (fun x => φ (H x)) pkSeed (mapPrf φ prf) idx kappa z j := by
  rw [forsNode, forsNode, Merkle.node_map _ φ map_bind]
  simp only [forsNodeHash_map_monad φ map_pure map_bind,
    forsLeaves_map_monad φ map_pure map_bind]

/-- A FORS tree's root commutes with the map. -/
theorem forsRoot_map_monad (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES) :
    φ (forsRoot H pkSeed prf idx kappa)
      = forsRoot (fun x => φ (H x)) pkSeed (mapPrf φ prf) idx kappa :=
  forsNode_map_monad φ map_pure map_bind H prf pkSeed idx kappa _ 0

/-- A FORS public key commutes with the map. -/
theorem forsKey_map_monad (pkSeed : PkSeed) (idx : Nat) :
    φ (forsKey H pkSeed prf idx) = forsKey (fun x => φ (H x)) pkSeed (mapPrf φ prf) idx := by
  rw [forsKey, forsKey, map_bind, HashSig.ofFnInOrder_map_monad φ map_pure map_bind]
  simp only [forsRoot_map_monad φ map_pure map_bind, forsPkFromRoots_map_monad φ map_pure map_bind]

/-- A FORS opening commutes with the map. -/
theorem treeOpen_map_monad (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) :
    φ (treeOpen H pkSeed prf idx kappa s)
      = treeOpen (fun x => φ (H x)) pkSeed (mapPrf φ prf) idx kappa s := by
  rw [treeOpen, treeOpen, map_bind, forsSecret_map_monad φ]
  simp only [map_bind, map_pure, Merkle.path_map _ φ map_pure map_bind,
    forsNodeHash_map_monad φ map_pure map_bind, forsLeaves_map_monad φ map_pure map_bind]

/-- The FORS openings commute with the map. -/
theorem forsSign_map_monad (pkSeed : PkSeed) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    φ (forsSign H pkSeed prf idx leaves)
      = forsSign (fun x => φ (H x)) pkSeed (mapPrf φ prf) idx leaves := by
  rw [forsSign, forsSign, HashSig.ofFnInOrder_map_monad φ map_pure map_bind]
  simp only [treeOpen_map_monad φ map_pure map_bind]

/-- The randomizer commutes with the map. -/
theorem prfMsg_map_monad (skPrf : HashOutput) (optRand : PkSeed) (msg : Message) :
    φ (prfMsg H skPrf optRand msg) = prfMsg (fun x => φ (H x)) skPrf optRand msg := by
  rw [prfMsg, prfMsg]
  erw [map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

/-- What a layer's key signs commutes with the map. -/
theorem layerMessage_map_monad (pkSeed : PkSeed) (layer : Layer) (idx : Nat) :
    φ (layerMessage H pkSeed prf layer idx)
      = layerMessage (fun x => φ (H x)) pkSeed (mapPrf φ prf) layer idx := by
  cases layer
  · exact forsKey_map_monad φ map_pure map_bind H prf pkSeed idx
  all_goals exact treeRoot_map_monad φ map_pure map_bind H prf pkSeed _ _

/-- A layer's signature commutes with the map. -/
theorem signLayer_map_monad [LawfulMonad m] [LawfulMonad n] (pkSeed : PkSeed) (layer : Layer)
    (idx : Nat) (msg : Digest) :
    φ (signLayer H pkSeed prf layer idx msg)
      = signLayer (fun x => φ (H x)) pkSeed (mapPrf φ prf) layer idx msg := by
  rw [signLayer, signLayer, map_bind, otsSign_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun found => ?_)
  cases found with
  | none => exact map_pure _
  | some found =>
    simp only [map_bind, map_pure, path_map_monad φ map_pure map_bind]

/-- The key expansion commutes with the map. -/
theorem expandKey_map_monad (seed : Seed) :
    φ (expandKey H seed) = expandKey (fun x => φ (H x)) seed := by
  rw [expandKey, expandKey, map_bind]
  refine congrArg _ (funext fun _ => ?_)
  rw [map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

/-- The public key commutes with the map. -/
theorem publicKeyOf_map_monad (pkSeed : PkSeed) :
    φ (publicKeyOf H pkSeed prf) = publicKeyOf (fun x => φ (H x)) pkSeed (mapPrf φ prf) := by
  rw [publicKeyOf, publicKeyOf, map_bind, treeRoot_map_monad φ map_pure map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

/-- Signing from the secrets, the public key and the randomizer commutes with the map. -/
theorem signDerived_map_monad [LawfulMonad m] [LawfulMonad n] (pk : PublicKey)
    (rho : Randomizer) (msg : Message) :
    φ (signDerived H prf pk rho msg)
      = signDerived (fun x => φ (H x)) (mapPrf φ prf) pk rho msg := by
  rw [signDerived, signDerived, map_bind, hMsg_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun d => ?_)
  rw [map_bind, forsSign_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun fors => ?_)
  simp only [map_bind, layerMessage_map_monad φ map_pure map_bind,
    signLayer_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun _ => congrArg _ (funext fun r₀ => ?_))
  cases r₀ with
  | error e => exact map_pure _
  | ok bottom =>
    simp only [map_bind, pure_bind, layerMessage_map_monad φ map_pure map_bind,
      signLayer_map_monad φ map_pure map_bind]
    refine congrArg _ (funext fun _ => congrArg _ (funext fun r₁ => ?_))
    cases r₁ with
    | error e => exact map_pure _
    | ok middle =>
      simp only [map_bind, layerMessage_map_monad φ map_pure map_bind,
        signLayer_map_monad φ map_pure map_bind]
      refine congrArg _ (funext fun _ => congrArg _ (funext fun r₂ => ?_))
      cases r₂ with
      | error e => exact map_pure _
      | ok top => simp only [map_pure]

/-- The secrets of `SK.seed`, mapped one call at a time, are the secrets under the mapped hash. -/
theorem mapPrf_prf (pkSeed : PkSeed) (seed : Seed) :
    mapPrf (m := m) (n := n) φ (Sphincs.prf H pkSeed seed)
      = Sphincs.prf (fun x => φ (H x)) pkSeed seed :=
  funext fun _ => th_map_monad φ map_pure map_bind H _ _ _

/-- Key generation commutes with the map. -/
theorem keyGenWith_map_monad (seed : Seed) :
    φ (keyGenWith H seed) = keyGenWith (fun x => φ (H x)) seed := by
  rw [keyGenWith, keyGenWith, map_bind, expandKey_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun key => ?_)
  rw [map_bind, publicKeyOf_map_monad φ map_pure map_bind, mapPrf_prf φ map_pure map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

/-- Signing commutes with the map. -/
theorem signWith_map_monad [LawfulMonad m] [LawfulMonad n] (sk : SecretKey) (msg : Message) :
    φ (signWith H sk msg) = signWith (fun x => φ (H x)) sk msg := by
  rw [signWith, signWith, map_bind, expandKey_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun key => ?_)
  rw [map_bind, publicKeyOf_map_monad φ map_pure map_bind, mapPrf_prf φ map_pure map_bind]
  refine congrArg _ (funext fun pk => ?_)
  rw [map_bind, prfMsg_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun rho => ?_)
  rw [signDerived_map_monad φ map_pure map_bind, mapPrf_prf φ map_pure map_bind]

end Map

/-! ## Derivation addresses -/

/-- The address types of the `PRF` calls: the chain starts and the FORS secrets. -/
def derivationTypes : List AdrsType :=
  [.wotsPrf, .forsPrf]

/-- An address of one of the derivation types. -/
def IsDerivationAddress (A : Adrs) : Prop :=
  ∃ type ∈ derivationTypes, ∃ layer tree keyPair word2 word3,
    A = adrs type layer tree keyPair word2 word3

/-- An address of another type is not a derivation address. -/
theorem not_isDerivationAddress {type : AdrsType} (htype : type ∉ derivationTypes)
    (layer : Layer) (tree keyPair word2 word3 : Nat) :
    ¬IsDerivationAddress (adrs type layer tree keyPair word2 word3) := by
  rintro ⟨type', htype', layer', tree', keyPair', word2', word3', h⟩
  obtain rfl := (adrs_inj h).1
  exact htype htype'

/-- An address of a derivation type is a derivation address. -/
theorem isDerivationAddress_of_mem {type : AdrsType} (htype : type ∈ derivationTypes)
    (layer : Layer) (tree keyPair word2 word3 : Nat) :
    IsDerivationAddress (adrs type layer tree keyPair word2 word3) :=
  ⟨type, htype, layer, tree, keyPair, word2, word3, rfl⟩

/-- A chain start is at a derivation address. -/
theorem isDerivationAddress_adrsPrf (key : OtsKey) (i : Fin V) :
    IsDerivationAddress (adrsPrf key i) :=
  isDerivationAddress_of_mem (type := .wotsPrf) (by decide) _ _ _ _ _

/-- A FORS secret is at a derivation address. -/
theorem isDerivationAddress_adrsFprf (idx j : Nat) : IsDerivationAddress (adrsFprf idx j) :=
  isDerivationAddress_of_mem (type := .forsPrf) (by decide) _ _ _ _ _

/-- A chain step is not at a derivation address. -/
theorem not_isDerivationAddress_adrsChain (key : OtsKey) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) : ¬IsDerivationAddress (adrsChain key i mu) :=
  not_isDerivationAddress (type := .wotsHash) (by decide) _ _ _ _ _

/-- A one-time leaf is not at a derivation address. -/
theorem not_isDerivationAddress_adrsPk (key : OtsKey) : ¬IsDerivationAddress (adrsPk key) :=
  not_isDerivationAddress (type := .wotsPk) (by decide) _ _ _ _ _

/-- An encoding is not at a derivation address. -/
theorem not_isDerivationAddress_adrsEnc (key : OtsKey) : ¬IsDerivationAddress (adrsEnc key) :=
  not_isDerivationAddress (type := .wotsEnc) (by decide) _ _ _ _ _

/-- A hypertree node is not at a derivation address. -/
theorem not_isDerivationAddress_adrsNode (layer : Layer) (tree z j : Nat) :
    ¬IsDerivationAddress (adrsNode layer tree z j) :=
  not_isDerivationAddress (type := .tree) (by decide) _ _ _ _ _

/-- A FORS leaf or node is not at a derivation address. -/
theorem not_isDerivationAddress_adrsFors (idx z j : Nat) :
    ¬IsDerivationAddress (adrsFors idx z j) :=
  not_isDerivationAddress (type := .forsTree) (by decide) _ _ _ _ _

/-- A FORS public key is not at a derivation address. -/
theorem not_isDerivationAddress_adrsRoots (idx : Nat) : ¬IsDerivationAddress (adrsRoots idx) :=
  not_isDerivationAddress (type := .forsRoots) (by decide) _ _ _ _ _

/-- The bytes of a digest are 16 bytes. -/
theorem size_packBytes_digest (d : Digest) : (packBytes d).size = 16 :=
  Base.size_packBytes d

/-- An address of another type than the encoding is not an encoding address. -/
theorem ne_adrsEnc {type : AdrsType} (htype : type ≠ .wotsEnc) (layer : Layer)
    (tree keyPair word2 word3 : Nat) (key : OtsKey) :
    adrs type layer tree keyPair word2 word3 ≠ adrsEnc key := by
  rw [adrsEnc, keyAdrs]
  exact adrs_ne_of_type_ne _ _ _ _ _ _ _ _ _ _ htype

/-! ## The inputs without an address -/

/-- The 93 bytes `PRF_msg` hashes: `SK.prf | opt_rand | M'`. -/
def randomizerInput (skPrf : HashOutput) (optRand : PkSeed) (msg : Message) : ByteArray :=
  packBytes skPrf ++ packBytes optRand ++ framedMessage msg

/-- The 84 bytes call `i` of `H_msg` hashes: `R | PK.seed | PK.root | M | BE_32(i)`. -/
def digestInput (rho : Randomizer) (pkSeed : PkSeed) (pkRoot : Digest) (msg : Message)
    (i : Nat) : ByteArray :=
  packBytes rho ++ packBytes pkSeed ++ packBytes pkRoot ++ packBytes msg ++ packBytes (toByte 4 i)

/-- The key expansion's input has 44 bytes: 11 for the name, 32 for `SK.seed`, 1 for the domain. -/
theorem size_expandInput (seed : Seed) (domain : UInt8) : (expandInput seed domain).size = 44 := by
  rw [expandInput, ByteArray.size_append, ByteArray.size_append, Base.size_packBytes, seed_tag_eq]
  rfl

/-- `PRF_msg`'s input has `32 + 16 + 45 = 93` bytes. -/
theorem size_randomizerInput (skPrf : HashOutput) (optRand : PkSeed) (msg : Message) :
    (randomizerInput skPrf optRand msg).size = 93 := by
  rw [randomizerInput, framedMessage, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_append, ByteArray.size_append, Base.size_packBytes, Base.size_packBytes,
    Base.size_packBytes, seed_tag_eq]
  rfl

/-- `H_msg`'s input has `16 + 16 + 16 + 32 + 4 = 84` bytes. -/
theorem size_digestInput (rho : Randomizer) (pkSeed : PkSeed) (pkRoot : Digest) (msg : Message)
    (i : Nat) : (digestInput rho pkSeed pkRoot msg i).size = 84 := by
  simp only [digestInput, ByteArray.size_append, Base.size_packBytes]
  rfl

/-! ## Inputs the honest algorithms never hash

A predicate `p` on queries that no allowed call satisfies is never queried.

An allowed call at an address is one of three kinds.

- A derivation, at a derivation address.
- An encoding of a key, with a payload of 20 bytes.
- A hash at an address of another type, with a payload of at least 16 bytes.

The encodings are asked of each key apart, since a key's counter search queries its own.

The calls without an address are asked of the lemmas that make them. -/

/-- A key's encodings query `p` nowhere.

This holds for every `PK.seed` and every payload of 20 bytes, a digest and a counter. -/
def EncodingAvoids {ι : Type} {spec : OracleSpec ι} (p : spec.Domain → Prop) [DecidablePred p]
    (H : ByteArray → OracleComp spec (Vector UInt8 32)) (key : OtsKey) : Prop :=
  ∀ pkSeed payload, payload.size = N + COUNTER_LEN →
    IsQueryBoundP (H (thInput pkSeed (adrsEnc key) payload)) p 0

section Avoid

variable {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Prop} [DecidablePred p]

variable (H : ByteArray → OracleComp spec (Vector UInt8 32)) (prf : Prf (OracleComp spec))
  (hH : ∀ pkSeed A payload, ¬IsDerivationAddress A → (∀ key, A ≠ adrsEnc key) →
    16 ≤ payload.size → IsQueryBoundP (H (thInput pkSeed A payload)) p 0)
  (hprf : ∀ A, IsDerivationAddress A → IsQueryBoundP (prf A) p 0)

/-- A tweakable hash call queries `p` nowhere when its hash does not. -/
theorem th_isQueryBoundP_zero_of_hash {pkSeed : PkSeed} {A : Adrs} {payload : ByteArray}
    (h : IsQueryBoundP (H (thInput pkSeed A payload)) p 0) :
    IsQueryBoundP (th H pkSeed A payload) p 0 :=
  isQueryBoundP_bind_zero _ _ h fun _ => isQueryBoundP_pure _ _ _

/-- The message digest queries `p` nowhere when its two calls do not. -/
theorem hMsg_isQueryBoundP_zero (rho : Randomizer) (pkSeed : PkSeed) (pkRoot : Digest)
    (msg : Message)
    (hD : ∀ i : Fin DIGEST_CALLS, IsQueryBoundP (H (digestInput rho pkSeed pkRoot msg i)) p 0) :
    IsQueryBoundP (hMsg H rho pkSeed pkRoot msg) p 0 :=
  isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ hD)
    fun _ => isQueryBoundP_pure _ _ _

/-- The randomizer queries `p` nowhere when its call does not. -/
theorem prfMsg_isQueryBoundP_zero (skPrf : HashOutput) (optRand : PkSeed) (msg : Message)
    (hR : IsQueryBoundP (H (randomizerInput skPrf optRand msg)) p 0) :
    IsQueryBoundP (prfMsg H skPrf optRand msg) p 0 :=
  isQueryBoundP_bind_zero _ _ hR fun _ => isQueryBoundP_pure _ _ _

/-- The key expansion queries `p` nowhere when its two calls do not. -/
theorem expandKey_isQueryBoundP_zero (seed : Seed)
    (hX : ∀ domain, IsQueryBoundP (H (expandInput seed domain)) p 0) :
    IsQueryBoundP (expandKey H seed) p 0 :=
  isQueryBoundP_bind_zero _ _ (hX 0) fun _ =>
    isQueryBoundP_bind_zero _ _ (hX 1) fun _ => isQueryBoundP_pure _ _ _

include hH

/-- A tweakable hash call outside the derivations and the encodings queries `p` nowhere. -/
theorem th_isQueryBoundP_zero {pkSeed : PkSeed} {A : Adrs} {payload : ByteArray}
    (hA : ¬IsDerivationAddress A) (hE : ∀ key, A ≠ adrsEnc key)
    (hsize : 16 ≤ payload.size) : IsQueryBoundP (th H pkSeed A payload) p 0 :=
  th_isQueryBoundP_zero_of_hash H (hH pkSeed A payload hA hE hsize)

/-- A chain step queries `p` nowhere. -/
theorem chainStep_isQueryBoundP_zero (pkSeed : PkSeed) (key : OtsKey) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) :
    IsQueryBoundP (chainStep H pkSeed key i mu value) p 0 :=
  th_isQueryBoundP_zero H hH (not_isDerivationAddress_adrsChain key i mu)
    (ne_adrsEnc (type := .wotsHash) (by decide) _ _ _ _ _) (by simp; decide)

/-- A walk along a chain queries `p` nowhere. -/
theorem chainWalk_isQueryBoundP_zero (pkSeed : PkSeed) (key : OtsKey) (i : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    IsQueryBoundP (chain H pkSeed key i start steps h value) p 0 :=
  chain_isQueryBoundP_zero _ (fun _ _ => chainStep_isQueryBoundP_zero H hH _ _ _ _ _) _ _ _ _

/-- A one-time leaf hash queries `p` nowhere. -/
theorem otsLeafHash_isQueryBoundP_zero (pkSeed : PkSeed) (key : OtsKey)
    (ends : Vector Digest V) : IsQueryBoundP (otsLeafHash H pkSeed key ends) p 0 :=
  th_isQueryBoundP_zero H hH (not_isDerivationAddress_adrsPk key)
    (ne_adrsEnc (type := .wotsPk) (by decide) _ _ _ _ _)
    (by rw [Sphincs.size_packDigests]; decide)

omit hH in
/-- An encoding queries `p` nowhere when the key's encodings do not. -/
theorem encode_isQueryBoundP_zero (pkSeed : PkSeed) {key : OtsKey} (hE : EncodingAvoids p H key)
    (msg : Digest) (counter : UInt32) :
    IsQueryBoundP (encode H pkSeed key msg counter) p 0 :=
  (isQueryBoundP_map_iff _ _ _).2 <| th_isQueryBoundP_zero_of_hash H
    (hE pkSeed (packBytes msg ++ packBytes (toByte COUNTER_LEN counter.toNat))
      (by simp only [ByteArray.size_append, Base.size_packBytes]))

/-- A one-time leaf, from a one-time signature, queries `p` nowhere.

The key's encodings must query `p` nowhere. -/
theorem otsLeaf_isQueryBoundP_zero (pkSeed : PkSeed) {key : OtsKey} (hE : EncodingAvoids p H key)
    (msg : Digest) (counter : UInt32) (y : Vector Digest V) :
    IsQueryBoundP (otsLeaf H pkSeed key msg counter y) p 0 := by
  rw [otsLeaf]
  refine isQueryBoundP_bind_zero _ _ (encode_isQueryBoundP_zero H pkSeed hE msg counter)
    fun x => ?_
  cases x with
  | none => exact isQueryBoundP_pure _ _ _
  | some x =>
    exact isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
      chainWalk_isQueryBoundP_zero H hH _ _ _ _ _ _ _) fun _ =>
        isQueryBoundP_bind_zero _ _ (otsLeafHash_isQueryBoundP_zero H hH _ _ _)
          fun _ => isQueryBoundP_pure _ _ _

/-- A hypertree node hash queries `p` nowhere. -/
theorem nodeHash_isQueryBoundP_zero (pkSeed : PkSeed) (layer : Layer) (tree z j : Nat)
    (left right : Digest) : IsQueryBoundP (nodeHash H pkSeed layer tree z j left right) p 0 :=
  th_isQueryBoundP_zero H hH (not_isDerivationAddress_adrsNode _ _ _ _)
    (ne_adrsEnc (type := .tree) (by decide) _ _ _ _ _) (by simp; decide)

/-- A FORS leaf hash queries `p` nowhere. -/
theorem forsLeafHash_isQueryBoundP_zero (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Nat) (secret : Digest) : IsQueryBoundP (forsLeafHash H pkSeed idx kappa s secret) p 0 :=
  th_isQueryBoundP_zero H hH (not_isDerivationAddress_adrsFors _ _ _)
    (ne_adrsEnc (type := .forsTree) (by decide) _ _ _ _ _) (by simp; decide)

/-- A FORS node hash queries `p` nowhere. -/
theorem forsNodeHash_isQueryBoundP_zero (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (z j : Nat) (left right : Digest) :
    IsQueryBoundP (forsNodeHash H pkSeed idx kappa z j left right) p 0 :=
  th_isQueryBoundP_zero H hH (not_isDerivationAddress_adrsFors _ _ _)
    (ne_adrsEnc (type := .forsTree) (by decide) _ _ _ _ _) (by simp; decide)

/-- The FORS public key from the roots queries `p` nowhere. -/
theorem forsPkFromRoots_isQueryBoundP_zero (pkSeed : PkSeed) (idx : Nat)
    (roots : Vector Digest FORS_TREES) :
    IsQueryBoundP (forsPkFromRoots H pkSeed idx roots) p 0 :=
  th_isQueryBoundP_zero H hH (not_isDerivationAddress_adrsRoots _)
    (ne_adrsEnc (type := .forsRoots) (by decide) _ _ _ _ _)
    (by rw [Sphincs.size_packDigests]; decide)

/-- Recovering one FORS tree's root queries `p` nowhere. -/
theorem treeRecover_isQueryBoundP_zero (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) (opening : TreeOpening) :
    IsQueryBoundP (treeRecover H pkSeed idx kappa s opening) p 0 := by
  rw [treeRecover]
  exact isQueryBoundP_bind_zero _ _ (forsLeafHash_isQueryBoundP_zero H hH _ _ _ _ _) fun _ =>
    climb_isQueryBoundP_zero _
      (fun _ _ _ _ => forsNodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _ _ _

/-- Recovering a FORS public key queries `p` nowhere. -/
theorem forsRecover_isQueryBoundP_zero (pkSeed : PkSeed) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) :
    IsQueryBoundP (forsRecover H pkSeed idx leaves openings) p 0 :=
  isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
    treeRecover_isQueryBoundP_zero H hH _ _ _ _ _) fun _ =>
      forsPkFromRoots_isQueryBoundP_zero H hH _ _ _

/-- A layer's root, from a layer's signature, queries `p` nowhere.

The encodings of the layer's key must query `p` nowhere. -/
theorem layerRoot_isQueryBoundP_zero (pkSeed : PkSeed) (layer : Layer) (idx : Nat)
    (hE : EncodingAvoids p H (OtsKey.ofIndex layer idx)) (msg : Digest)
    (sig : LayerSignature layer) : IsQueryBoundP (layerRoot H pkSeed layer idx msg sig) p 0 := by
  rw [layerRoot]
  refine isQueryBoundP_bind_zero _ _ (otsLeaf_isQueryBoundP_zero H hH _ hE _ _ _) fun leaf => ?_
  cases leaf with
  | none => exact isQueryBoundP_pure _ _ _
  | some leaf =>
    exact isQueryBoundP_bind_zero _ _ (climb_isQueryBoundP_zero _
      (fun _ _ _ _ => nodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _ _ _)
      fun _ => isQueryBoundP_pure _ _ _

include hprf

omit hH in
/-- The chain starts query `p` nowhere, outside the derivations. -/
theorem chainStarts_isQueryBoundP_zero (key : OtsKey) :
    IsQueryBoundP (chainStarts prf key) p 0 :=
  ofFnInOrder_isQueryBoundP_zero _ _ fun _ => hprf _ (isDerivationAddress_adrsPrf _ _)

/-- A one-time key's leaf, from its secrets, queries `p` nowhere. -/
theorem otsPublicLeaf_isQueryBoundP_zero (pkSeed : PkSeed) (key : OtsKey) :
    IsQueryBoundP (otsPublicLeaf H pkSeed prf key) p 0 :=
  isQueryBoundP_bind_zero _ _ (chainStarts_isQueryBoundP_zero prf hprf _) fun _ =>
    isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
      chainWalk_isQueryBoundP_zero H hH _ _ _ _ _ _ _) fun _ =>
        otsLeafHash_isQueryBoundP_zero H hH _ _ _

/-- A one-time signature queries `p` nowhere.

The key's encodings must query `p` nowhere. -/
theorem otsSign_isQueryBoundP_zero (pkSeed : PkSeed) {key : OtsKey} (hE : EncodingAvoids p H key)
    (msg : Digest) : IsQueryBoundP (otsSign H pkSeed prf key msg) p 0 := by
  rw [otsSign]
  refine isQueryBoundP_bind_zero _ _ (findFirst_isQueryBoundP_zero _ _
    (fun _ => encode_isQueryBoundP_zero H pkSeed hE msg _) _ _) fun found => ?_
  cases found with
  | none => exact isQueryBoundP_pure _ _ _
  | some found =>
    exact isQueryBoundP_bind_zero _ _ (chainStarts_isQueryBoundP_zero prf hprf _) fun _ =>
      isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
        chainWalk_isQueryBoundP_zero H hH _ _ _ _ _ _ _) fun _ => isQueryBoundP_pure _ _ _

/-- A hypertree node queries `p` nowhere. -/
theorem node_isQueryBoundP_zero (pkSeed : PkSeed) (layer : Layer) (tree z j : Nat) :
    IsQueryBoundP (node H pkSeed prf layer tree z j) p 0 :=
  merkleNode_isQueryBoundP_zero _ _ (fun _ => otsPublicLeaf_isQueryBoundP_zero H prf hH hprf _ _)
    (fun _ _ _ _ => nodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _

/-- A key's path queries `p` nowhere. -/
theorem path_isQueryBoundP_zero (pkSeed : PkSeed) (layer : Layer) (tree e : Nat) :
    IsQueryBoundP (path H pkSeed prf layer tree e) p 0 :=
  merkleSiblings_isQueryBoundP_zero _ _
    (fun _ => otsPublicLeaf_isQueryBoundP_zero H prf hH hprf _ _)
    (fun _ _ _ _ => nodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _ _

omit hH in
/-- A FORS secret queries `p` nowhere, outside the derivations. -/
theorem forsSecret_isQueryBoundP_zero (idx : Nat) (kappa : Fin FORS_TREES) (s : Nat) :
    IsQueryBoundP (forsSecret prf idx kappa s) p 0 :=
  hprf _ (isDerivationAddress_adrsFprf _ _)

/-- A FORS leaf, from its secret, queries `p` nowhere. -/
theorem forsLeaves_isQueryBoundP_zero (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Nat) : IsQueryBoundP (forsLeaves H pkSeed prf idx kappa s) p 0 :=
  isQueryBoundP_bind_zero _ _ (forsSecret_isQueryBoundP_zero prf hprf _ _ _) fun _ =>
    forsLeafHash_isQueryBoundP_zero H hH _ _ _ _ _

/-- A FORS node queries `p` nowhere. -/
theorem forsNode_isQueryBoundP_zero (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (z j : Nat) : IsQueryBoundP (forsNode H pkSeed prf idx kappa z j) p 0 :=
  merkleNode_isQueryBoundP_zero _ _ (fun _ => forsLeaves_isQueryBoundP_zero H prf hH hprf _ _ _ _)
    (fun _ _ _ _ => forsNodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _

/-- A FORS public key queries `p` nowhere. -/
theorem forsKey_isQueryBoundP_zero (pkSeed : PkSeed) (idx : Nat) :
    IsQueryBoundP (forsKey H pkSeed prf idx) p 0 :=
  isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
    forsNode_isQueryBoundP_zero H prf hH hprf _ _ _ _ _) fun _ =>
      forsPkFromRoots_isQueryBoundP_zero H hH _ _ _

/-- A FORS opening queries `p` nowhere. -/
theorem treeOpen_isQueryBoundP_zero (pkSeed : PkSeed) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) : IsQueryBoundP (treeOpen H pkSeed prf idx kappa s) p 0 :=
  isQueryBoundP_bind_zero _ _ (forsSecret_isQueryBoundP_zero prf hprf _ _ _) fun _ =>
    isQueryBoundP_bind_zero _ _ (merkleSiblings_isQueryBoundP_zero _ _
      (fun _ => forsLeaves_isQueryBoundP_zero H prf hH hprf _ _ _ _)
      (fun _ _ _ _ => forsNodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _ _)
      fun _ => isQueryBoundP_pure _ _ _

/-- The FORS openings query `p` nowhere. -/
theorem forsSign_isQueryBoundP_zero (pkSeed : PkSeed) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    IsQueryBoundP (forsSign H pkSeed prf idx leaves) p 0 :=
  ofFnInOrder_isQueryBoundP_zero _ _ fun _ => treeOpen_isQueryBoundP_zero H prf hH hprf _ _ _ _

/-- A tree's root queries `p` nowhere. -/
theorem treeRoot_isQueryBoundP_zero (pkSeed : PkSeed) (layer : Layer) (tree : Nat) :
    IsQueryBoundP (treeRoot H pkSeed prf layer tree) p 0 :=
  node_isQueryBoundP_zero H prf hH hprf pkSeed layer tree _ 0

/-- The public key queries `p` nowhere: it builds the top tree. -/
theorem publicKeyOf_isQueryBoundP_zero (pkSeed : PkSeed) :
    IsQueryBoundP (publicKeyOf H pkSeed prf) p 0 :=
  isQueryBoundP_bind_zero _ _ (treeRoot_isQueryBoundP_zero H prf hH hprf _ _ _)
    fun _ => isQueryBoundP_pure _ _ _

/-- What a layer's key signs queries `p` nowhere. -/
theorem layerMessage_isQueryBoundP_zero (pkSeed : PkSeed) (layer : Layer) (idx : Nat) :
    IsQueryBoundP (layerMessage H pkSeed prf layer idx) p 0 := by
  cases layer
  · exact forsKey_isQueryBoundP_zero H prf hH hprf _ _
  all_goals exact treeRoot_isQueryBoundP_zero H prf hH hprf _ _ _

/-- A layer's signature queries `p` nowhere.

The encodings of the layer's key must query `p` nowhere. -/
theorem signLayer_isQueryBoundP_zero (pkSeed : PkSeed) (layer : Layer) (idx : Nat)
    (hE : EncodingAvoids p H (OtsKey.ofIndex layer idx)) (msg : Digest) :
    IsQueryBoundP (signLayer H pkSeed prf layer idx msg) p 0 := by
  rw [signLayer]
  refine isQueryBoundP_bind_zero _ _ (otsSign_isQueryBoundP_zero H prf hH hprf _ hE msg)
    fun found => ?_
  cases found with
  | none => exact isQueryBoundP_pure _ _ _
  | some found =>
    exact isQueryBoundP_bind_zero _ _ (path_isQueryBoundP_zero H prf hH hprf _ _ _ _)
      fun _ => isQueryBoundP_pure _ _ _

/-- A layer signs what its layer message gives, and that queries `p` nowhere.

The encodings of the layer's key must query `p` nowhere. -/
theorem layerMessage_bind_signLayer_isQueryBoundP_zero {β : Type} (pkSeed : PkSeed)
    (layer : Layer) (idx : Nat) (hE : EncodingAvoids p H (OtsKey.ofIndex layer idx))
    (k : Except SphincsError (LayerSignature layer) → OracleComp spec β)
    (hk : ∀ r, IsQueryBoundP (k r) p 0) :
    IsQueryBoundP (layerMessage H pkSeed prf layer idx >>= fun msg =>
      signLayer H pkSeed prf layer idx msg >>= k) p 0 :=
  isQueryBoundP_bind_zero _ _ (layerMessage_isQueryBoundP_zero H prf hH hprf pkSeed layer idx)
    fun msg => isQueryBoundP_bind_zero _ _
      (signLayer_isQueryBoundP_zero H prf hH hprf pkSeed layer idx hE msg) hk

end Avoid

/-! ## One hypothesis for every call outside the derivations

Here every hash outside the derivations avoids `p`, encodings and digest calls included.

Every derivation avoids `p` too, at any address. -/

section AvoidAll

variable {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Prop} [DecidablePred p]
  (H : ByteArray → OracleComp spec (Vector UInt8 32)) (prf : Prf (OracleComp spec))
  (hH : ∀ pkSeed A payload, ¬IsDerivationAddress A → 16 ≤ payload.size →
    IsQueryBoundP (H (thInput pkSeed A payload)) p 0)
  (hD : ∀ rho pkSeed pkRoot msg i,
    IsQueryBoundP (H (digestInput rho pkSeed pkRoot msg i)) p 0)
  (hprf : ∀ A, IsQueryBoundP (prf A) p 0)

include hH in
/-- Every key's encodings avoid `p`: an encoding address is not a derivation address. -/
theorem encodingAvoids_of_forall (key : OtsKey) : EncodingAvoids p H key :=
  fun pkSeed payload hsize => hH pkSeed _ payload (not_isDerivationAddress_adrsEnc key)
    (by rw [hsize]; decide)

include hH hD in
/-- Verification queries `p` nowhere. -/
theorem verifyWith_isQueryBoundP_zero (pk : PublicKey) (msg : Message) (sig : Signature) :
    IsQueryBoundP (verifyWith H pk msg sig) p 0 := by
  have hH' : ∀ pkSeed A payload, ¬IsDerivationAddress A → (∀ key, A ≠ adrsEnc key) →
      16 ≤ payload.size → IsQueryBoundP (H (thInput pkSeed A payload)) p 0 :=
    fun pkSeed A payload hA _ hsize => hH pkSeed A payload hA hsize
  have hE : ∀ key, EncodingAvoids p H key := encodingAvoids_of_forall H hH
  rw [verifyWith]
  refine isQueryBoundP_bind_zero _ _ (hMsg_isQueryBoundP_zero H _ _ _ _ fun _ => hD _ _ _ _ _)
    fun d => isQueryBoundP_bind_zero _ _ (forsRecover_isQueryBoundP_zero H hH' _ _ _ _)
    fun key => isQueryBoundP_bind_zero _ _
      (layerRoot_isQueryBoundP_zero H hH' _ _ _ (hE _) _ _) fun r₀ => ?_
  cases r₀ with
  | none => exact isQueryBoundP_pure _ _ _
  | some r₀ =>
    refine isQueryBoundP_bind_zero _ _
      (layerRoot_isQueryBoundP_zero H hH' _ _ _ (hE _) _ _) fun r₁ => ?_
    cases r₁ with
    | none => exact isQueryBoundP_pure _ _ _
    | some r₁ =>
      refine isQueryBoundP_bind_zero _ _
        (layerRoot_isQueryBoundP_zero H hH' _ _ _ (hE _) _ _) fun r₂ => ?_
      cases r₂ with
      | none => exact isQueryBoundP_pure _ _ _
      | some r₂ => exact isQueryBoundP_pure _ _ _

include hH hD hprf in
/-- Signing from a source of secrets, a public key and a randomizer queries `p` nowhere. -/
theorem signDerived_isQueryBoundP_zero (pk : PublicKey) (rho : Randomizer) (msg : Message) :
    IsQueryBoundP (signDerived H prf pk rho msg) p 0 := by
  have hH' : ∀ pkSeed A payload, ¬IsDerivationAddress A → (∀ key, A ≠ adrsEnc key) →
      16 ≤ payload.size → IsQueryBoundP (H (thInput pkSeed A payload)) p 0 :=
    fun pkSeed A payload hA _ hsize => hH pkSeed A payload hA hsize
  have hprf' : ∀ A, IsDerivationAddress A → IsQueryBoundP (prf A) p 0 := fun A _ => hprf A
  have hE : ∀ key, EncodingAvoids p H key := encodingAvoids_of_forall H hH
  rw [signDerived]
  refine isQueryBoundP_bind_zero _ _ (hMsg_isQueryBoundP_zero H _ _ _ _ fun _ => hD _ _ _ _ _)
    fun d => isQueryBoundP_bind_zero _ _ (forsSign_isQueryBoundP_zero H prf hH' hprf' _ _ _)
    fun fors =>
      layerMessage_bind_signLayer_isQueryBoundP_zero H prf hH' hprf' _ _ _ (hE _) _ fun r₀ => ?_
  cases r₀ with
  | error e => exact isQueryBoundP_pure _ _ _
  | ok bottom =>
    refine isQueryBoundP_bind_zero _ _ (isQueryBoundP_pure _ _ _) fun _ =>
      layerMessage_bind_signLayer_isQueryBoundP_zero H prf hH' hprf' _ _ _ (hE _) _ fun r₁ => ?_
    cases r₁ with
    | error e => exact isQueryBoundP_pure _ _ _
    | ok middle =>
      refine isQueryBoundP_bind_zero _ _ (isQueryBoundP_pure _ _ _) fun _ =>
        layerMessage_bind_signLayer_isQueryBoundP_zero H prf hH' hprf' _ _ _ (hE _) _ fun r₂ => ?_
      cases r₂ with
      | error e => exact isQueryBoundP_pure _ _ _
      | ok top =>
        exact isQueryBoundP_bind_zero _ _ (isQueryBoundP_pure _ _ _)
          fun _ => isQueryBoundP_pure _ _ _

end AvoidAll

/-! ## Key generation and signing outside the key expansion

Whatever bound the key expansion has, key generation and signing have it too.

The other calls must avoid `p`.

- The addressed calls, outside the derivations.
- The calls of the message digest and of the randomizer.
- The derivations from `SK.seed`. -/

section Expansion

variable {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Prop} [DecidablePred p]
  (H : ByteArray → OracleComp spec (Vector UInt8 32))
  (hH : ∀ pkSeed A payload, ¬IsDerivationAddress A → 16 ≤ payload.size →
    IsQueryBoundP (H (thInput pkSeed A payload)) p 0)

include hH

/-- Key generation queries `p` at most as often as the key expansion. -/
theorem keyGenWith_isQueryBoundP {k : Nat} (seed : Seed)
    (hX : IsQueryBoundP (expandKey H seed) p k)
    (hprf : ∀ pkSeed A, IsQueryBoundP (Sphincs.prf H pkSeed seed A) p 0) :
    IsQueryBoundP (keyGenWith H seed) p k :=
  isQueryBoundP_bind (m := 0) hX fun key _ =>
    isQueryBoundP_bind_zero _ _ (publicKeyOf_isQueryBoundP_zero H _
      (fun pkSeed A payload hA _ hsize => hH pkSeed A payload hA hsize)
      (fun A _ => hprf key.pkSeed A) _)
      fun _ => isQueryBoundP_pure _ _ _

/-- Signing queries `p` at most as often as the key expansion. -/
theorem signWith_isQueryBoundP {k : Nat} (sk : SecretKey) (msg : Message)
    (hX : IsQueryBoundP (expandKey H sk.seed) p k)
    (hD : ∀ rho pkSeed pkRoot msg i,
      IsQueryBoundP (H (digestInput rho pkSeed pkRoot msg i)) p 0)
    (hR : ∀ skPrf optRand, IsQueryBoundP (H (randomizerInput skPrf optRand msg)) p 0)
    (hprf : ∀ pkSeed A, IsQueryBoundP (Sphincs.prf H pkSeed sk.seed A) p 0) :
    IsQueryBoundP (signWith H sk msg) p k :=
  isQueryBoundP_bind (m := 0) hX fun key _ =>
    isQueryBoundP_bind_zero _ _ (publicKeyOf_isQueryBoundP_zero H _
      (fun pkSeed A payload hA _ hsize => hH pkSeed A payload hA hsize)
      (fun A _ => hprf key.pkSeed A) _)
      fun pk => isQueryBoundP_bind_zero _ _ (prfMsg_isQueryBoundP_zero H _ _ _ (hR _ _))
        fun rho => signDerived_isQueryBoundP_zero H _ hH hD (hprf key.pkSeed) pk rho msg

end Expansion

/-! ## In the game -/

/-- A query of the game's oracle at an input of 44 bytes, the length of the key expansion's. -/
def IsSeedLengthQuery : HashSig.OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr x => x.length = 44

instance : DecidablePred IsSeedLengthQuery := by
  rintro (_ | _) <;> simp only [IsSeedLengthQuery] <;> infer_instance

/-- In the game, a hash of an input that is not 44 bytes long makes no seed-length query. -/
theorem H_isQueryBoundP_seedLength {x : ByteArray} (hx : x.size ≠ 44) :
    IsQueryBoundP (H x) IsSeedLengthQuery 0 := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
  exact absurd (by simpa [IsSeedLengthQuery] using h) hx

/-- In the game, no addressed call is a seed-length query: it has at least 48 bytes.

The two unused hypotheses give the lemma the shape that the query lemmas ask of the hash. -/
theorem H_thInput_isQueryBoundP_seedLength (pkSeed : PkSeed) (A : Adrs)
    (payload : ByteArray) (_ : ¬IsDerivationAddress A) (_ : 16 ≤ payload.size) :
    IsQueryBoundP (H (thInput pkSeed A payload)) IsSeedLengthQuery 0 :=
  H_isQueryBoundP_seedLength (by simp only [size_thInput, PREFIX_LEN, N, ADRS_LEN]; omega)

/-- In the game, no call of the message digest is a seed-length query: it has 84 bytes. -/
theorem H_digestInput_isQueryBoundP_seedLength (rho : Randomizer) (pkSeed : PkSeed)
    (pkRoot : Digest) (msg : Message) (i : Nat) :
    IsQueryBoundP (H (digestInput rho pkSeed pkRoot msg i)) IsSeedLengthQuery 0 :=
  H_isQueryBoundP_seedLength (by rw [size_digestInput]; decide)

/-- In the game, a derivation from any `SK.seed` is not a seed-length query.

It hashes `PK.seed`, the address and the 32-byte `SK.seed`, 80 bytes. -/
theorem prf_H_isQueryBoundP_seedLength (pkSeed : PkSeed) (seed : Seed) (A : Adrs) :
    IsQueryBoundP (prf H pkSeed seed A) IsSeedLengthQuery 0 :=
  th_isQueryBoundP_zero_of_hash H
    (H_isQueryBoundP_seedLength (by rw [size_thInput_seed]; decide))

/-- In the game, signing from the secrets of any `SK.seed` makes no seed-length query. -/
theorem signDerived_H_isQueryBoundP_seedLength (pkSeed : PkSeed) (seed : Seed) (pk : PublicKey)
    (rho : Randomizer) (msg : Message) :
    IsQueryBoundP (signDerived H (prf H pkSeed seed) pk rho msg) IsSeedLengthQuery 0 :=
  signDerived_isQueryBoundP_zero H _ H_thInput_isQueryBoundP_seedLength
    H_digestInput_isQueryBoundP_seedLength (prf_H_isQueryBoundP_seedLength pkSeed seed) pk rho msg

/-- In the game, the public key from the secrets of any `SK.seed` makes no seed-length query. -/
theorem publicKeyOf_H_isQueryBoundP_seedLength (pkSeed : PkSeed) (seed : Seed) :
    IsQueryBoundP (publicKeyOf H pkSeed (prf H pkSeed seed)) IsSeedLengthQuery 0 :=
  publicKeyOf_isQueryBoundP_zero H _
    (fun pkSeed A payload hA _ hsize =>
      H_thInput_isQueryBoundP_seedLength pkSeed A payload hA hsize)
    (fun A _ => prf_H_isQueryBoundP_seedLength pkSeed seed A) pkSeed

/-- In the game, verification makes no seed-length query. -/
theorem verifyWith_H_isQueryBoundP_seedLength (pk : PublicKey) (msg : Message)
    (sig : Signature) : IsQueryBoundP (verifyWith H pk msg sig) IsSeedLengthQuery 0 :=
  verifyWith_isQueryBoundP_zero H H_thInput_isQueryBoundP_seedLength
    H_digestInput_isQueryBoundP_seedLength pk msg sig

/-- In the game, one hash call is at most one seed-length query. -/
theorem H_isQueryBoundP_seedLength_one (x : ByteArray) :
    IsQueryBoundP (H x) IsSeedLengthQuery 1 :=
  (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)

/-- In the game, the key expansion makes two seed-length queries at most: its own two calls. -/
theorem expandKey_H_isQueryBoundP_seedLength (seed : Seed) :
    IsQueryBoundP (expandKey H seed) IsSeedLengthQuery 2 :=
  isQueryBoundP_bind (H_isQueryBoundP_seedLength_one _) fun _ _ =>
    (isQueryBoundP_bind (m := 0) (H_isQueryBoundP_seedLength_one _) fun _ _ =>
      isQueryBoundP_pure _ _ _)

/-- In the game, key generation makes two seed-length queries at most: the key expansion's. -/
theorem keyGenWith_H_isQueryBoundP_seedLength (seed : Seed) :
    IsQueryBoundP (keyGenWith H seed) IsSeedLengthQuery 2 :=
  keyGenWith_isQueryBoundP H H_thInput_isQueryBoundP_seedLength seed
    (expandKey_H_isQueryBoundP_seedLength seed)
    fun pkSeed => prf_H_isQueryBoundP_seedLength pkSeed seed

/-- In the game, signing makes two seed-length queries at most: the key expansion's. -/
theorem signWith_H_isQueryBoundP_seedLength (sk : SecretKey) (msg : Message) :
    IsQueryBoundP (signWith H sk msg) IsSeedLengthQuery 2 :=
  signWith_isQueryBoundP H H_thInput_isQueryBoundP_seedLength sk msg
    (expandKey_H_isQueryBoundP_seedLength sk.seed) H_digestInput_isQueryBoundP_seedLength
    (fun _ _ => H_isQueryBoundP_seedLength (by rw [size_randomizerInput]; decide))
    fun pkSeed => prf_H_isQueryBoundP_seedLength pkSeed sk.seed

end EthLib.Cryptography.Sphincs.Unforgeability
