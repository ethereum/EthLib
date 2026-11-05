module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Cryptography.Proofs.QueryAvoidance
public import EthLib.Cryptography.Proofs.Sphincs.Address
public import EthLib.Cryptography.Proofs.Sphincs.Serialization
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.VerifyQueries

/-!
# Proofs: the hash calls of leanSPHINCS key generation and signing

Key generation and signing under a map of monads, and the inputs they never hash.

A map of monads that keeps `pure` and `bind` sends key generation and signing to themselves.

The mapped algorithms take the mapped hash and the mapped derivations.

The random-oracle proof uses this to move the algorithms between oracle worlds.

Below the scheme seed, the honest algorithms make three kinds of call.

- A derivation from the seed, at a derivation address: the chain starts, the FORS secrets, the
  public parameter and the randomizer.
- An encoding of a one-time key, at the key's encoding address, with a payload of at least
  16 bytes.
- A hash at an address of another type, with a payload of at least 16 bytes.

So a query that no call of the last two kinds makes is made only through the derivations.

The encodings are a kind of their own because a key's counter search queries them.

A hypothesis on each key's encodings then shows which calls avoid another key's search inputs.

Two such sets of queries matter for the proof.

- The 43-byte inputs, the length of the input that grows the scheme seed.
  A call of the second kind hashes at least `32 + 16 = 48` bytes, and a derivation at least 64.
- The inputs at a derivation address.

In the game, the honest algorithms query a 43-byte input only to grow the scheme seed.
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
  (H : ByteArray → m (Vector UInt8 32)) (prf : SeedPrf m)

/-- The derivations mapped one by one. -/
abbrev mapPrf : SeedPrf n := fun pp A suffix => φ (prf pp A suffix)

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
theorem chainStarts_map_monad (pp : PublicParam) (key : OtsKey) :
    φ (chainStarts pp prf key) = chainStarts pp (mapPrf φ prf) key := by
  rw [chainStarts, chainStarts, map_bind, ofFnInOrder_map_monad φ map_pure map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

/-- A one-time key's leaf, from the seed, commutes with the map. -/
theorem otsPublicLeaf_map_monad (pp : PublicParam) (key : OtsKey) :
    φ (otsPublicLeaf H pp prf key) = otsPublicLeaf (fun x => φ (H x)) pp (mapPrf φ prf) key := by
  rw [otsPublicLeaf, otsPublicLeaf, map_bind, chainStarts_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun starts => ?_)
  simp only [map_bind, ofFnInOrder_map_monad φ map_pure map_bind, chain,
    chain_map_monad φ map_pure map_bind, chainStep_map_monad φ map_pure map_bind, otsLeafHash,
    th_map_monad φ map_pure map_bind]

/-- The counter search commutes with the map. -/
theorem findCounter_map_monad [LawfulMonad m] [LawfulMonad n] (pp : PublicParam) (key : OtsKey)
    (msg : ByteArray) (c fuel : Nat) :
    φ (Internal.findCounter H pp key msg c fuel)
      = Internal.findCounter (fun x => φ (H x)) pp key msg c fuel := by
  rw [Internal.findCounter, Internal.findCounter, findFirst_map_monad φ map_pure map_bind]
  refine congrArg (fun test => Wots.findFirst UInt32.ofNat test c fuel) (funext fun k => ?_)
  rw [encode, encode, map_monad_map φ map_pure map_bind, th_map_monad φ map_pure map_bind]

/-- A one-time signature commutes with the map. -/
theorem otsSign_map_monad [LawfulMonad m] [LawfulMonad n] (pp : PublicParam) (key : OtsKey)
    (msg : ByteArray) :
    φ (otsSign H pp prf key msg) = otsSign (fun x => φ (H x)) pp (mapPrf φ prf) key msg := by
  rw [otsSign, otsSign, map_bind, findCounter_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun found => ?_)
  cases found with
  | none => exact map_pure _
  | some found =>
    simp only [map_bind, map_pure, chainStarts_map_monad φ map_pure map_bind,
      ofFnInOrder_map_monad φ map_pure map_bind, chain, chain_map_monad φ map_pure map_bind,
      chainStep_map_monad φ map_pure map_bind]

/-- A hypertree node commutes with the map. -/
theorem node_map_monad (pp : PublicParam) (layer : Layer) (tree level j : Nat) :
    φ (node H pp prf layer tree level j)
      = node (fun x => φ (H x)) pp (mapPrf φ prf) layer tree level j := by
  rw [node, node, Merkle.node_map _ φ map_bind]
  simp only [nodeHash_map_monad φ map_pure map_bind, leaves,
    otsPublicLeaf_map_monad φ map_pure map_bind]
  rfl

/-- A tree's root commutes with the map. -/
theorem treeRoot_map_monad (pp : PublicParam) (layer : Layer) (tree : Nat) :
    φ (treeRoot H pp prf layer tree) = treeRoot (fun x => φ (H x)) pp (mapPrf φ prf) layer tree :=
  node_map_monad φ map_pure map_bind H prf pp layer tree _ 0

/-- A key's path commutes with the map. -/
theorem path_map_monad (pp : PublicParam) (layer : Layer) (tree e : Nat) :
    φ (path H pp prf layer tree e) = path (fun x => φ (H x)) pp (mapPrf φ prf) layer tree e := by
  rw [path, path, Merkle.path_map _ φ map_pure map_bind]
  simp only [nodeHash_map_monad φ map_pure map_bind, leaves,
    otsPublicLeaf_map_monad φ map_pure map_bind]
  rfl

/-- A FORS secret commutes with the map. -/
theorem forsSecret_map_monad (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) :
    φ (forsSecret pp prf idx kappa l) = forsSecret pp (mapPrf φ prf) idx kappa l := by
  rw [forsSecret, forsSecret, map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

/-- A FORS leaf, from the seed, commutes with the map. -/
theorem forsLeaves_map_monad (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES) (j : Nat) :
    φ (forsLeaves H pp prf idx kappa j)
      = forsLeaves (fun x => φ (H x)) pp (mapPrf φ prf) idx kappa j := by
  rw [forsLeaves, forsLeaves, map_bind, forsSecret_map_monad φ map_pure map_bind]
  simp only [forsLeafHash, th_map_monad φ map_pure map_bind]

/-- A FORS node commutes with the map. -/
theorem forsNode_map_monad (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (level j : Nat) :
    φ (forsNode H pp prf idx kappa level j)
      = forsNode (fun x => φ (H x)) pp (mapPrf φ prf) idx kappa level j := by
  rw [forsNode, forsNode, Merkle.node_map _ φ map_bind]
  simp only [forsNodeHash_map_monad φ map_pure map_bind,
    forsLeaves_map_monad φ map_pure map_bind]

/-- A FORS key commutes with the map. -/
theorem forsKey_map_monad (pp : PublicParam) (idx : Nat) :
    φ (forsKey H pp prf idx) = forsKey (fun x => φ (H x)) pp (mapPrf φ prf) idx := by
  rw [forsKey, forsKey, ofFnInOrder_map_monad φ map_pure map_bind]
  simp only [map_bind, map_pure, forsNode_map_monad φ map_pure map_bind]

/-- A FORS opening commutes with the map. -/
theorem treeOpen_map_monad (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) :
    φ (treeOpen H pp prf idx kappa l)
      = treeOpen (fun x => φ (H x)) pp (mapPrf φ prf) idx kappa l := by
  rw [treeOpen, treeOpen, map_bind, forsSecret_map_monad φ map_pure map_bind]
  simp only [map_bind, map_pure, Merkle.path_map _ φ map_pure map_bind,
    forsNodeHash_map_monad φ map_pure map_bind, forsLeaves_map_monad φ map_pure map_bind]

/-- The FORS openings commute with the map. -/
theorem forsSign_map_monad (pp : PublicParam) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    φ (forsSign H pp prf idx leaves)
      = forsSign (fun x => φ (H x)) pp (mapPrf φ prf) idx leaves := by
  rw [forsSign, forsSign, ofFnInOrder_map_monad φ map_pure map_bind]
  simp only [treeOpen_map_monad φ map_pure map_bind]

/-- The randomizer commutes with the map. -/
theorem randomizer_map_monad (pp : PublicParam) (msg : Message) :
    φ (randomizer pp prf msg) = randomizer pp (mapPrf φ prf) msg := by
  rw [randomizer, randomizer]
  erw [map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

/-- What a layer's key signs commutes with the map. -/
theorem layerMessage_map_monad (pp : PublicParam) (layer : Layer) (idx : Nat) :
    φ (layerMessage H pp prf layer idx)
      = layerMessage (fun x => φ (H x)) pp (mapPrf φ prf) layer idx := by
  cases layer <;>
    simp only [layerMessage, map_bind, map_pure, forsKey_map_monad φ map_pure map_bind,
      treeRoot_map_monad φ map_pure map_bind]

/-- A layer's signature commutes with the map. -/
theorem signLayer_map_monad [LawfulMonad m] [LawfulMonad n] (pp : PublicParam) (layer : Layer)
    (idx : Nat) (msg : ByteArray) :
    φ (signLayer H pp prf layer idx msg)
      = signLayer (fun x => φ (H x)) pp (mapPrf φ prf) layer idx msg := by
  rw [signLayer, signLayer, map_bind, otsSign_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun found => ?_)
  cases found with
  | none => exact map_pure _
  | some found =>
    simp only [map_bind, map_pure, path_map_monad φ map_pure map_bind]

/-- The public parameter commutes with the map. -/
theorem publicParamOf_map_monad :
    φ (publicParamOf prf) = publicParamOf (mapPrf φ prf) := by
  rw [publicParamOf, publicParamOf]
  erw [map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

/-- The public key commutes with the map. -/
theorem publicKeyOf_map_monad :
    φ (publicKeyOf H prf) = publicKeyOf (fun x => φ (H x)) (mapPrf φ prf) := by
  rw [publicKeyOf, publicKeyOf, map_bind, publicParamOf_map_monad φ map_pure map_bind]
  simp only [map_bind, map_pure, treeRoot_map_monad φ map_pure map_bind]

/-- Signing from the derivations commutes with the map. -/
theorem signDerived_map_monad [LawfulMonad m] [LawfulMonad n] (pp : PublicParam) (msg : Message) :
    φ (signDerived H prf pp msg) = signDerived (fun x => φ (H x)) (mapPrf φ prf) pp msg := by
  rw [signDerived, signDerived, map_bind, randomizer_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun rho => ?_)
  rw [map_bind, messageDigest_map_monad φ map_pure map_bind]
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

omit [Monad m] [Monad n] map_pure map_bind in
/-- The scheme seed commutes with the map: it is one hash. -/
theorem schemeSeed_map_monad (seed : Seed) :
    φ (schemeSeed H seed) = schemeSeed (fun x => φ (H x)) seed :=
  rfl

/-- Key generation commutes with the map. -/
theorem keyGenWith_map_monad (seed : Seed) :
    φ (keyGenWith H seed) = keyGenWith (fun x => φ (H x)) seed := by
  rw [keyGenWith, keyGenWith, map_bind]
  refine congrArg _ (funext fun s => ?_)
  rw [map_bind, publicKeyOf_map_monad φ map_pure map_bind]
  exact congrArg _ (funext fun _ => map_pure _)

/-- Signing commutes with the map. -/
theorem signWith_map_monad [LawfulMonad m] [LawfulMonad n] (sk : SecretKey) (msg : Message) :
    φ (signWith H sk msg) = signWith (fun x => φ (H x)) sk msg := by
  rw [signWith, signWith, map_bind]
  refine congrArg _ (funext fun s => ?_)
  rw [map_bind, publicParamOf_map_monad φ map_pure map_bind]
  refine congrArg _ (funext fun pp => ?_)
  exact signDerived_map_monad φ map_pure map_bind H _ pp msg

omit [Monad m] [Monad n] map_pure map_bind in
/-- The derivations from a seed commute with the map: they are hashes. -/
theorem mapPrf_seedPrf (s : Seed) :
    mapPrf φ (seedPrf H s) = seedPrf (fun x => φ (H x)) s :=
  rfl

end Map

/-! ## Derivation addresses -/

/-- The address types of the derivations from the seed.

They are the chain starts, the public parameter, the randomizer and the FORS secrets. -/
def derivationTypes : List AddressType :=
  [.prf, .param, .rnd, .forsPrf]

/-- An address of one of the derivation types. -/
def IsDerivationAddress (A : Address) : Prop :=
  ∃ type ∈ derivationTypes, ∃ step layer tree hi lo,
    A = encodeAddress type.code step layer tree hi lo

/-- An address of another type is not a derivation address. -/
theorem not_isDerivationAddress {type : AddressType} (htype : type ∉ derivationTypes)
    (step : Fin 8) (layer : Fin 256) (tree : UInt32) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    ¬IsDerivationAddress (encodeAddress type.code step layer tree hi lo) := by
  rintro ⟨type', htype', step', layer', tree', hi', lo', h⟩
  obtain rfl := AddressType.code_injective (encodeAddress_inj.1 h).1
  exact htype htype'

/-- An address of a derivation type is a derivation address. -/
theorem isDerivationAddress_of_mem {type : AddressType} (htype : type ∈ derivationTypes)
    (step : Fin 8) (layer : Fin 256) (tree : UInt32) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    IsDerivationAddress (encodeAddress type.code step layer tree hi lo) :=
  ⟨type, htype, step, layer, tree, hi, lo, rfl⟩

/-- A chain start is at a derivation address. -/
theorem isDerivationAddress_addrPrf (key : OtsKey) (j : Fin (V / 2)) :
    IsDerivationAddress (addrPrf key j) :=
  isDerivationAddress_of_mem (type := .prf) (by decide) _ _ _ _ _

/-- The public parameter is at a derivation address. -/
theorem isDerivationAddress_addrParam : IsDerivationAddress addrParam :=
  isDerivationAddress_of_mem (type := .param) (by decide) _ _ _ _ _

/-- The randomizer is at a derivation address. -/
theorem isDerivationAddress_addrRnd : IsDerivationAddress addrRnd :=
  isDerivationAddress_of_mem (type := .rnd) (by decide) _ _ _ _ _

/-- A pair of FORS secrets is at a derivation address. -/
theorem isDerivationAddress_addrForsPrf (idx : Nat) (kappa : Fin FORS_TREES)
    (p : Fin (2 ^ FORS_HEIGHT / 2)) : IsDerivationAddress (addrForsPrf idx kappa p) :=
  isDerivationAddress_of_mem (type := .forsPrf) (by decide) _ _ _ _ _

/-- A chain step is not at a derivation address. -/
theorem not_isDerivationAddress_addrChain (key : OtsKey) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) : ¬IsDerivationAddress (addrChain key i mu) :=
  not_isDerivationAddress (type := .chain) (by decide) _ _ _ _ _

/-- A one-time leaf is not at a derivation address. -/
theorem not_isDerivationAddress_addrLeaf (key : OtsKey) : ¬IsDerivationAddress (addrLeaf key) :=
  not_isDerivationAddress (type := .leaf) (by decide) _ _ _ _ _

/-- An encoding is not at a derivation address. -/
theorem not_isDerivationAddress_addrEncoding (key : OtsKey) :
    ¬IsDerivationAddress (addrEncoding key) :=
  not_isDerivationAddress (type := .encoding) (by decide) _ _ _ _ _

/-- A hypertree node is not at a derivation address. -/
theorem not_isDerivationAddress_addrNode (layer : Layer) (tree : Nat)
    (level : Fin (TOP_HEIGHT + 1)) (j : Nat) : ¬IsDerivationAddress (addrNode layer tree level j) :=
  not_isDerivationAddress (type := .node) (by decide) _ _ _ _ _

/-- A digest call is not at a derivation address. -/
theorem not_isDerivationAddress_addrMsg (call : Fin DIGEST_CALLS) :
    ¬IsDerivationAddress (addrMsg call) :=
  not_isDerivationAddress (type := .msg) (by decide) _ _ _ _ _

/-- A FORS leaf is not at a derivation address. -/
theorem not_isDerivationAddress_addrForsLeaf (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) : ¬IsDerivationAddress (addrForsLeaf idx kappa l) :=
  not_isDerivationAddress (type := .forsLeaf) (by decide) _ _ _ _ _

/-- A FORS node is not at a derivation address. -/
theorem not_isDerivationAddress_addrForsNode (idx : Nat) (kappa : Fin FORS_TREES)
    (level : Fin 16) (j : Fin (2 ^ FORS_HEIGHT)) :
    ¬IsDerivationAddress (addrForsNode idx kappa level j) :=
  not_isDerivationAddress (type := .forsNode) (by decide) _ _ _ _ _

/-- The bytes of a digest are 16 bytes. -/
theorem size_packBytes_digest (d : Digest) : (packBytes d).size = 16 :=
  Base.size_packBytes d

/-- The bytes of a FORS key are 768 bytes. -/
theorem size_forsKeyBytes (key : ForsKey) : (forsKeyBytes key).size = 768 := by
  simp [forsKeyBytes, FORS_TREES, N]

/-- An address of another type than the encoding is not an encoding address. -/
theorem ne_addrEncoding {type : AddressType} (htype : type ≠ .encoding) (step : Fin 8)
    (layer : Fin 256) (tree : UInt32) (hi : Fin (2 ^ 24)) (lo : UInt32) (key : OtsKey) :
    encodeAddress type.code step layer tree hi lo ≠ addrEncoding key := by
  rw [addrEncoding, keyAddress]
  exact encodeAddress_ne_of_type_ne _ _ _ _ _ _ _ _ _ _ fun h =>
    htype (AddressType.code_injective h)

/-! ## Inputs the honest algorithms never hash

A predicate `p` on queries that no allowed call satisfies is never queried.

An allowed call is one of three kinds.

- A derivation, at a derivation address.
- An encoding of a key, with a payload of at least 16 bytes.
- A hash at an address of another type, with a payload of at least 16 bytes.

The encodings are asked of each key apart, since a key's counter search queries its own. -/

/-- A key's encodings query `p` nowhere.

This holds for every parameter and every payload of at least 16 bytes. -/
def EncodingAvoids {ι : Type} {spec : OracleSpec ι} (p : spec.Domain → Prop) [DecidablePred p]
    (H : ByteArray → OracleComp spec (Vector UInt8 32)) (key : OtsKey) : Prop :=
  ∀ pp payload, 16 ≤ payload.size → IsQueryBoundP (H (thInput pp (addrEncoding key) payload)) p 0

section Avoid

variable {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Prop} [DecidablePred p]

variable (H : ByteArray → OracleComp spec (Vector UInt8 32)) (prf : SeedPrf (OracleComp spec))
  (hH : ∀ pp A payload, ¬IsDerivationAddress A → (∀ key, A ≠ addrEncoding key) →
    16 ≤ payload.size → IsQueryBoundP (H (thInput pp A payload)) p 0)
  (hprf : ∀ pp A suffix, IsDerivationAddress A → IsQueryBoundP (prf pp A suffix) p 0)

/-- A tweakable hash call queries `p` nowhere when its hash does not. -/
theorem th_isQueryBoundP_zero_of_hash {pp : PublicParam} {A : Address} {payload : ByteArray}
    (h : IsQueryBoundP (H (thInput pp A payload)) p 0) : IsQueryBoundP (th H pp A payload) p 0 :=
  isQueryBoundP_bind_zero _ _ h fun _ => isQueryBoundP_pure _ _ _

include hH

/-- A tweakable hash call outside the derivations and the encodings queries `p` nowhere. -/
theorem th_isQueryBoundP_zero {pp : PublicParam} {A : Address} {payload : ByteArray}
    (hA : ¬IsDerivationAddress A) (hE : ∀ key, A ≠ addrEncoding key)
    (hsize : 16 ≤ payload.size) : IsQueryBoundP (th H pp A payload) p 0 :=
  th_isQueryBoundP_zero_of_hash H (hH pp A payload hA hE hsize)

/-- A chain step queries `p` nowhere. -/
theorem chainStep_isQueryBoundP_zero (pp : PublicParam) (key : OtsKey) (i : Fin V)
    (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) :
    IsQueryBoundP (chainStep H pp key i mu value) p 0 :=
  th_isQueryBoundP_zero H hH (not_isDerivationAddress_addrChain key i mu)
    (ne_addrEncoding (type := .chain) (by decide) _ _ _ _ _) (by simp; decide)

/-- A walk along a chain queries `p` nowhere. -/
theorem chainWalk_isQueryBoundP_zero (pp : PublicParam) (key : OtsKey) (i : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    IsQueryBoundP (chain H pp key i start steps h value) p 0 :=
  chain_isQueryBoundP_zero _ (fun _ _ => chainStep_isQueryBoundP_zero H hH _ _ _ _ _) _ _ _ _

/-- A one-time leaf hash queries `p` nowhere. -/
theorem otsLeafHash_isQueryBoundP_zero (pp : PublicParam) (key : OtsKey) (ends : Vector Digest V) :
    IsQueryBoundP (otsLeafHash H pp key ends) p 0 :=
  th_isQueryBoundP_zero H hH (not_isDerivationAddress_addrLeaf key)
    (ne_addrEncoding (type := .leaf) (by decide) _ _ _ _ _)
    (by rw [Sphincs.size_packDigests]; decide)

omit hH in
/-- An encoding of a message of at least 12 bytes queries `p` nowhere.

The key's encodings must query `p` nowhere. -/
theorem encode_isQueryBoundP_zero (pp : PublicParam) {key : OtsKey} (hE : EncodingAvoids p H key)
    {msg : ByteArray} (hmsg : 12 ≤ msg.size) (counter : UInt32) :
    IsQueryBoundP (encode H pp key msg counter) p 0 :=
  (isQueryBoundP_map_iff _ _ _).2 <| th_isQueryBoundP_zero_of_hash H
    (hE pp (msg ++ packBytes (uintToBytes COUNTER_LEN counter.toNat))
      (by simp [COUNTER_LEN]; omega))

/-- A one-time leaf, from a signature of a message of at least 12 bytes, queries `p` nowhere.

The key's encodings must query `p` nowhere. -/
theorem otsLeaf_isQueryBoundP_zero (pp : PublicParam) {key : OtsKey} (hE : EncodingAvoids p H key)
    {msg : ByteArray} (hmsg : 12 ≤ msg.size) (counter : UInt32) (y : Vector Digest V) :
    IsQueryBoundP (otsLeaf H pp key msg counter y) p 0 := by
  rw [otsLeaf]
  refine isQueryBoundP_bind_zero _ _ (encode_isQueryBoundP_zero H pp hE hmsg counter)
    fun x => ?_
  cases x with
  | none => exact isQueryBoundP_pure _ _ _
  | some x =>
    exact isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
      chainWalk_isQueryBoundP_zero H hH _ _ _ _ _ _ _) fun _ =>
        isQueryBoundP_bind_zero _ _ (otsLeafHash_isQueryBoundP_zero H hH _ _ _)
          fun _ => isQueryBoundP_pure _ _ _

/-- A hypertree node hash queries `p` nowhere. -/
theorem nodeHash_isQueryBoundP_zero (pp : PublicParam) (layer : Layer) (tree level j : Nat)
    (left right : Digest) : IsQueryBoundP (nodeHash H pp layer tree level j left right) p 0 :=
  th_isQueryBoundP_zero H hH (not_isDerivationAddress_addrNode _ _ _ _)
    (ne_addrEncoding (type := .node) (by decide) _ _ _ _ _) (by simp; decide)

/-- A FORS leaf hash queries `p` nowhere. -/
theorem forsLeafHash_isQueryBoundP_zero (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) (secret : Digest) :
    IsQueryBoundP (forsLeafHash H pp idx kappa l secret) p 0 :=
  th_isQueryBoundP_zero H hH (not_isDerivationAddress_addrForsLeaf _ _ _)
    (ne_addrEncoding (type := .forsLeaf) (by decide) _ _ _ _ _) (by simp; decide)

/-- A FORS node hash queries `p` nowhere. -/
theorem forsNodeHash_isQueryBoundP_zero (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (level j : Nat) (left right : Digest) :
    IsQueryBoundP (forsNodeHash H pp idx kappa level j left right) p 0 :=
  th_isQueryBoundP_zero H hH (not_isDerivationAddress_addrForsNode _ _ _ _)
    (ne_addrEncoding (type := .forsNode) (by decide) _ _ _ _ _) (by simp; decide)

/-- The message digest queries `p` nowhere. -/
theorem messageDigest_isQueryBoundP_zero (pp : PublicParam) (msg : Message) (rho : Randomizer) :
    IsQueryBoundP (messageDigest H pp msg rho) p 0 := by
  rw [messageDigest]
  exact isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun call =>
    hH _ _ _ (not_isDerivationAddress_addrMsg call)
      (ne_addrEncoding (type := .msg) (by decide) _ _ _ _ _)
      (by rw [ByteArray.size_append, Base.size_packBytes, Base.size_packBytes]; decide))
    fun _ => isQueryBoundP_pure _ _ _

/-- Recovering one FORS tree queries `p` nowhere. -/
theorem treeRecover_isQueryBoundP_zero (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) (opening : TreeOpening) :
    IsQueryBoundP (treeRecover H pp idx kappa l opening) p 0 := by
  rw [treeRecover]
  exact isQueryBoundP_bind_zero _ _ (forsLeafHash_isQueryBoundP_zero H hH _ _ _ _ _) fun _ =>
    isQueryBoundP_bind_zero _ _ (climb_isQueryBoundP_zero _
      (fun _ _ _ _ => forsNodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _ _ _)
      fun _ => isQueryBoundP_pure _ _ _

/-- Recovering a FORS key queries `p` nowhere. -/
theorem forsRecover_isQueryBoundP_zero (pp : PublicParam) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES)
    (openings : Vector TreeOpening FORS_TREES) :
    IsQueryBoundP (forsRecover H pp idx leaves openings) p 0 :=
  ofFnInOrder_isQueryBoundP_zero _ _ fun _ => treeRecover_isQueryBoundP_zero H hH _ _ _ _ _

/-- A layer's root, from a message of at least 12 bytes, queries `p` nowhere.

The encodings of the layer's key must query `p` nowhere. -/
theorem layerRoot_isQueryBoundP_zero (pp : PublicParam) (layer : Layer) (idx : Nat)
    (hE : EncodingAvoids p H (OtsKey.ofIndex layer idx)) {msg : ByteArray} (hmsg : 12 ≤ msg.size)
    (sig : LayerSignature layer) : IsQueryBoundP (layerRoot H pp layer idx msg sig) p 0 := by
  rw [layerRoot]
  refine isQueryBoundP_bind_zero _ _ (otsLeaf_isQueryBoundP_zero H hH _ hE hmsg _ _) fun leaf => ?_
  cases leaf with
  | none => exact isQueryBoundP_pure _ _ _
  | some leaf =>
    exact isQueryBoundP_bind_zero _ _ (climb_isQueryBoundP_zero _
      (fun _ _ _ _ => nodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _ _ _)
      fun _ => isQueryBoundP_pure _ _ _

include hprf

omit hH in
/-- The chain starts query `p` nowhere, outside the derivations. -/
theorem chainStarts_isQueryBoundP_zero (pp : PublicParam) (key : OtsKey) :
    IsQueryBoundP (chainStarts pp prf key) p 0 :=
  isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
    hprf _ _ _ (isDerivationAddress_addrPrf _ _))
    fun _ => isQueryBoundP_pure _ _ _

/-- A one-time key's leaf, from the seed, queries `p` nowhere. -/
theorem otsPublicLeaf_isQueryBoundP_zero (pp : PublicParam) (key : OtsKey) :
    IsQueryBoundP (otsPublicLeaf H pp prf key) p 0 :=
  isQueryBoundP_bind_zero _ _ (chainStarts_isQueryBoundP_zero prf hprf _ _) fun _ =>
    isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
      chainWalk_isQueryBoundP_zero H hH _ _ _ _ _ _ _) fun _ =>
        otsLeafHash_isQueryBoundP_zero H hH _ _ _

/-- A one-time signature of a message of at least 12 bytes queries `p` nowhere.

The key's encodings must query `p` nowhere. -/
theorem otsSign_isQueryBoundP_zero (pp : PublicParam) {key : OtsKey} (hE : EncodingAvoids p H key)
    {msg : ByteArray} (hmsg : 12 ≤ msg.size) : IsQueryBoundP (otsSign H pp prf key msg) p 0 := by
  rw [otsSign]
  refine isQueryBoundP_bind_zero _ _ (findFirst_isQueryBoundP_zero _ _
    (fun _ => encode_isQueryBoundP_zero H pp hE hmsg _) _ _) fun found => ?_
  cases found with
  | none => exact isQueryBoundP_pure _ _ _
  | some found =>
    exact isQueryBoundP_bind_zero _ _ (chainStarts_isQueryBoundP_zero prf hprf _ _) fun _ =>
      isQueryBoundP_bind_zero _ _ (ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
        chainWalk_isQueryBoundP_zero H hH _ _ _ _ _ _ _) fun _ => isQueryBoundP_pure _ _ _

/-- A hypertree node queries `p` nowhere. -/
theorem node_isQueryBoundP_zero (pp : PublicParam) (layer : Layer) (tree level j : Nat) :
    IsQueryBoundP (node H pp prf layer tree level j) p 0 :=
  merkleNode_isQueryBoundP_zero _ _ (fun _ => otsPublicLeaf_isQueryBoundP_zero H prf hH hprf _ _)
    (fun _ _ _ _ => nodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _

/-- A key's path queries `p` nowhere. -/
theorem path_isQueryBoundP_zero (pp : PublicParam) (layer : Layer) (tree e : Nat) :
    IsQueryBoundP (path H pp prf layer tree e) p 0 :=
  merkleSiblings_isQueryBoundP_zero _ _
    (fun _ => otsPublicLeaf_isQueryBoundP_zero H prf hH hprf _ _)
    (fun _ _ _ _ => nodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _ _

omit hH in
/-- A FORS secret queries `p` nowhere, outside the derivations. -/
theorem forsSecret_isQueryBoundP_zero (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) : IsQueryBoundP (forsSecret pp prf idx kappa l) p 0 :=
  isQueryBoundP_bind_zero _ _ (hprf _ _ _ (isDerivationAddress_addrForsPrf _ _ _))
    fun _ => isQueryBoundP_pure _ _ _

/-- A FORS leaf, from the seed, queries `p` nowhere. -/
theorem forsLeaves_isQueryBoundP_zero (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (j : Nat) : IsQueryBoundP (forsLeaves H pp prf idx kappa j) p 0 :=
  isQueryBoundP_bind_zero _ _ (forsSecret_isQueryBoundP_zero prf hprf _ _ _ _) fun _ =>
    forsLeafHash_isQueryBoundP_zero H hH _ _ _ _ _

/-- A FORS node queries `p` nowhere. -/
theorem forsNode_isQueryBoundP_zero (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (level j : Nat) : IsQueryBoundP (forsNode H pp prf idx kappa level j) p 0 :=
  merkleNode_isQueryBoundP_zero _ _ (fun _ => forsLeaves_isQueryBoundP_zero H prf hH hprf _ _ _ _)
    (fun _ _ _ _ => forsNodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _

/-- A FORS key queries `p` nowhere. -/
theorem forsKey_isQueryBoundP_zero (pp : PublicParam) (idx : Nat) :
    IsQueryBoundP (forsKey H pp prf idx) p 0 :=
  ofFnInOrder_isQueryBoundP_zero _ _ fun _ =>
    isQueryBoundP_bind_zero _ _ (forsNode_isQueryBoundP_zero H prf hH hprf _ _ _ _ _) fun _ =>
      isQueryBoundP_bind_zero _ _ (forsNode_isQueryBoundP_zero H prf hH hprf _ _ _ _ _)
        fun _ => isQueryBoundP_pure _ _ _

/-- A FORS opening queries `p` nowhere. -/
theorem treeOpen_isQueryBoundP_zero (pp : PublicParam) (idx : Nat) (kappa : Fin FORS_TREES)
    (l : Fin (2 ^ FORS_HEIGHT)) : IsQueryBoundP (treeOpen H pp prf idx kappa l) p 0 :=
  isQueryBoundP_bind_zero _ _ (forsSecret_isQueryBoundP_zero prf hprf _ _ _ _) fun _ =>
    isQueryBoundP_bind_zero _ _ (merkleSiblings_isQueryBoundP_zero _ _
      (fun _ => forsLeaves_isQueryBoundP_zero H prf hH hprf _ _ _ _)
      (fun _ _ _ _ => forsNodeHash_isQueryBoundP_zero H hH _ _ _ _ _ _ _) _ _ _)
      fun _ => isQueryBoundP_pure _ _ _

/-- The FORS openings query `p` nowhere. -/
theorem forsSign_isQueryBoundP_zero (pp : PublicParam) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    IsQueryBoundP (forsSign H pp prf idx leaves) p 0 :=
  ofFnInOrder_isQueryBoundP_zero _ _ fun _ => treeOpen_isQueryBoundP_zero H prf hH hprf _ _ _ _

omit hH in
/-- The randomizer queries `p` nowhere, outside the derivations. -/
theorem randomizer_isQueryBoundP_zero (pp : PublicParam) (msg : Message) :
    IsQueryBoundP (randomizer pp prf msg) p 0 :=
  isQueryBoundP_bind_zero _ _ (hprf _ _ _ isDerivationAddress_addrRnd)
    fun _ => isQueryBoundP_pure _ _ _

end Avoid

/-! ## Signing and key generation never hash the avoided inputs -/

section AvoidSign

variable {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Prop} [DecidablePred p]
  (H : ByteArray → OracleComp spec (Vector UInt8 32)) (prf : SeedPrf (OracleComp spec))

/-- What a layer's key signs takes at least 12 bytes: 768 for a FORS key, 16 for a root. -/
theorem size_of_mem_support_layerMessage {pp : PublicParam} {layer : Layer} {idx : Nat}
    {msg : ByteArray} (hmsg : msg ∈ support (layerMessage H pp prf layer idx)) :
    12 ≤ msg.size := by
  cases layer <;> simp only [layerMessage, bind_pure_comp, support_map, Set.mem_image] at hmsg <;>
    obtain ⟨x, -, rfl⟩ := hmsg
  · rw [size_forsKeyBytes]
    decide
  all_goals
    rw [size_packBytes_digest]
    decide

variable (hH : ∀ pp A payload, ¬IsDerivationAddress A → (∀ key, A ≠ addrEncoding key) →
    16 ≤ payload.size → IsQueryBoundP (H (thInput pp A payload)) p 0)
  (hprf : ∀ pp A suffix, IsDerivationAddress A → IsQueryBoundP (prf pp A suffix) p 0)

include hH hprf

/-- A tree's root queries `p` nowhere. -/
theorem treeRoot_isQueryBoundP_zero (pp : PublicParam) (layer : Layer) (tree : Nat) :
    IsQueryBoundP (treeRoot H pp prf layer tree) p 0 :=
  node_isQueryBoundP_zero H prf hH hprf pp layer tree _ 0

/-- What a layer's key signs queries `p` nowhere. -/
theorem layerMessage_isQueryBoundP_zero (pp : PublicParam) (layer : Layer) (idx : Nat) :
    IsQueryBoundP (layerMessage H pp prf layer idx) p 0 := by
  cases layer <;> simp only [layerMessage, bind_pure_comp, isQueryBoundP_map_iff]
  · exact forsKey_isQueryBoundP_zero H prf hH hprf _ _
  all_goals exact treeRoot_isQueryBoundP_zero H prf hH hprf _ _ _

/-- A layer's signature of a message of at least 12 bytes queries `p` nowhere.

The encodings of the layer's key must query `p` nowhere. -/
theorem signLayer_isQueryBoundP_zero (pp : PublicParam) (layer : Layer) (idx : Nat)
    (hE : EncodingAvoids p H (OtsKey.ofIndex layer idx)) {msg : ByteArray}
    (hmsg : 12 ≤ msg.size) : IsQueryBoundP (signLayer H pp prf layer idx msg) p 0 := by
  rw [signLayer]
  refine isQueryBoundP_bind_zero _ _ (otsSign_isQueryBoundP_zero H prf hH hprf _ hE hmsg)
    fun found => ?_
  cases found with
  | none => exact isQueryBoundP_pure _ _ _
  | some found =>
    exact isQueryBoundP_bind_zero _ _ (path_isQueryBoundP_zero H prf hH hprf _ _ _ _)
      fun _ => isQueryBoundP_pure _ _ _

/-- A layer signs what its layer message gives, and that queries `p` nowhere.

The encodings of the layer's key must query `p` nowhere. -/
theorem layerMessage_bind_signLayer_isQueryBoundP_zero {β : Type} (pp : PublicParam)
    (layer : Layer) (idx : Nat) (hE : EncodingAvoids p H (OtsKey.ofIndex layer idx))
    (k : Except SphincsError (LayerSignature layer) → OracleComp spec β)
    (hk : ∀ r, IsQueryBoundP (k r) p 0) :
    IsQueryBoundP (layerMessage H pp prf layer idx >>= fun msg =>
      signLayer H pp prf layer idx msg >>= k) p 0 :=
  isQueryBoundP_bind (layerMessage_isQueryBoundP_zero H prf hH hprf pp layer idx) fun _ hmsg =>
    isQueryBoundP_bind_zero _ _ (signLayer_isQueryBoundP_zero H prf hH hprf pp layer idx hE
      (size_of_mem_support_layerMessage H prf hmsg)) hk

end AvoidSign

/-! ## One hypothesis for every call outside the derivations

Here every hash outside the derivations avoids `p`, encodings included.

Every derivation avoids `p` too, at any address. -/

section AvoidAll

variable {ι : Type} {spec : OracleSpec ι} {p : spec.Domain → Prop} [DecidablePred p]
  (H : ByteArray → OracleComp spec (Vector UInt8 32)) (prf : SeedPrf (OracleComp spec))
  (hH : ∀ pp A payload, ¬IsDerivationAddress A → 16 ≤ payload.size →
    IsQueryBoundP (H (thInput pp A payload)) p 0)
  (hprf : ∀ pp A suffix, IsQueryBoundP (prf pp A suffix) p 0)

include hH in
/-- Every key's encodings avoid `p`: an encoding address is not a derivation address. -/
theorem encodingAvoids_of_forall (key : OtsKey) : EncodingAvoids p H key :=
  fun pp payload hsize => hH pp _ payload (not_isDerivationAddress_addrEncoding key) hsize

include hH in
/-- Verification queries `p` nowhere. -/
theorem verifyWith_isQueryBoundP_zero (pk : PublicKey) (msg : Message) (sig : Signature) :
    IsQueryBoundP (verifyWith H pk msg sig) p 0 := by
  have hH' : ∀ pp A payload, ¬IsDerivationAddress A → (∀ key, A ≠ addrEncoding key) →
      16 ≤ payload.size → IsQueryBoundP (H (thInput pp A payload)) p 0 :=
    fun pp A payload hA _ hsize => hH pp A payload hA hsize
  have hE : ∀ key, EncodingAvoids p H key := encodingAvoids_of_forall H hH
  have hroot : ∀ r : Digest, 12 ≤ (packBytes r).size := fun r => by simp; decide
  rw [verifyWith]
  refine isQueryBoundP_bind_zero _ _ (messageDigest_isQueryBoundP_zero H hH' _ _ _) fun d =>
    isQueryBoundP_bind_zero _ _ (forsRecover_isQueryBoundP_zero H hH' _ _ _ _) fun key =>
    isQueryBoundP_bind_zero _ _
      (layerRoot_isQueryBoundP_zero H hH' _ _ _ (hE _) (by rw [size_forsKeyBytes]; omega) _)
      fun r₀ => ?_
  cases r₀ with
  | none => exact isQueryBoundP_pure _ _ _
  | some r₀ =>
    refine isQueryBoundP_bind_zero _ _
      (layerRoot_isQueryBoundP_zero H hH' _ _ _ (hE _) (hroot r₀) _) fun r₁ => ?_
    cases r₁ with
    | none => exact isQueryBoundP_pure _ _ _
    | some r₁ =>
      refine isQueryBoundP_bind_zero _ _
        (layerRoot_isQueryBoundP_zero H hH' _ _ _ (hE _) (hroot r₁) _) fun r₂ => ?_
      cases r₂ with
      | none => exact isQueryBoundP_pure _ _ _
      | some r₂ => exact isQueryBoundP_pure _ _ _

include hH hprf

/-- Signing from the derivations queries `p` nowhere. -/
theorem signDerived_isQueryBoundP_zero (pp : PublicParam) (msg : Message) :
    IsQueryBoundP (signDerived H prf pp msg) p 0 := by
  have hH' : ∀ pp A payload, ¬IsDerivationAddress A → (∀ key, A ≠ addrEncoding key) →
      16 ≤ payload.size → IsQueryBoundP (H (thInput pp A payload)) p 0 :=
    fun pp A payload hA _ hsize => hH pp A payload hA hsize
  have hprf' : ∀ pp A suffix, IsDerivationAddress A → IsQueryBoundP (prf pp A suffix) p 0 :=
    fun pp A suffix _ => hprf pp A suffix
  have hE : ∀ key, EncodingAvoids p H key := encodingAvoids_of_forall H hH
  rw [signDerived]
  refine isQueryBoundP_bind_zero _ _ (randomizer_isQueryBoundP_zero prf hprf' _ _) fun rho =>
    isQueryBoundP_bind_zero _ _ (messageDigest_isQueryBoundP_zero H hH' _ _ _) fun d =>
    isQueryBoundP_bind_zero _ _ (forsSign_isQueryBoundP_zero H prf hH' hprf' _ _ _) fun fors =>
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

omit hH in
/-- The public parameter queries `p` nowhere, outside the derivations. -/
theorem publicParamOf_isQueryBoundP_zero : IsQueryBoundP (publicParamOf prf) p 0 :=
  isQueryBoundP_bind_zero _ _ (hprf _ _ _) fun _ => isQueryBoundP_pure _ _ _

/-- The public key queries `p` nowhere. -/
theorem publicKeyOf_isQueryBoundP_zero : IsQueryBoundP (publicKeyOf H prf) p 0 :=
  isQueryBoundP_bind_zero _ _ (publicParamOf_isQueryBoundP_zero prf hprf) fun _ =>
    isQueryBoundP_bind_zero _ _ (treeRoot_isQueryBoundP_zero H prf
      (fun pp A payload hA _ hsize => hH pp A payload hA hsize)
      (fun pp A suffix _ => hprf pp A suffix)
      _ _ _) fun _ => isQueryBoundP_pure _ _ _

end AvoidAll

/-! ## Input lengths -/

/-- The input that grows the scheme seed: the scheme's name, then the seed. -/
def seedInput (seed : Seed) : ByteArray :=
  ByteArray.mk SEED_TAG.toArray ++ packBytes seed

/-- Growing the scheme seed hashes its input. -/
theorem schemeSeed_eq {m : Type → Type} (H : ByteArray → m (Vector UInt8 32)) (seed : Seed) :
    schemeSeed H seed = H (seedInput seed) :=
  rfl

/-- The input that grows the scheme seed has 43 bytes: 11 for the name, 32 for the seed. -/
theorem size_seedInput (seed : Seed) : (seedInput seed).size = 43 := by
  rw [seedInput, ByteArray.size_append, Base.size_packBytes, seed_tag_eq]
  rfl

/-- A tweakable hash input has 32 bytes before its payload: the parameter and the address. -/
theorem size_thInput (pp : PublicParam) (A : Address) (payload : ByteArray) :
    (thInput pp A payload).size = 32 + payload.size := by
  rw [thInput, ByteArray.size_append, ByteArray.size_append, Base.size_packBytes,
    Base.size_packBytes]
  rfl

/-- A tweakable hash input with a payload of at least 16 bytes is not a seed input. -/
theorem thInput_ne_seedInput {payload : ByteArray} (h : 16 ≤ payload.size) (pp : PublicParam)
    (A : Address) (seed : Seed) : thInput pp A payload ≠ seedInput seed := fun heq => by
  have := congrArg ByteArray.size heq
  rw [size_thInput, size_seedInput] at this
  omega

/-! ## In the game -/

/-- A query of the game's oracle at an input of 43 bytes, the length of the seed input. -/
def IsSeedLengthQuery : HashSig.OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr x => x.length = 43

instance : DecidablePred IsSeedLengthQuery := by
  rintro (_ | _) <;> simp only [IsSeedLengthQuery] <;> infer_instance

/-- In the game, a hash of an input that is not 43 bytes long makes no seed-length query. -/
theorem H_isQueryBoundP_seedLength {x : ByteArray} (hx : x.size ≠ 43) :
    IsQueryBoundP (H x) IsSeedLengthQuery 0 := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
  exact absurd (by simpa [IsSeedLengthQuery] using h) hx

/-- In the game, no call outside the derivations is a seed-length query. -/
theorem H_thInput_isQueryBoundP_seedLength (pp : PublicParam) (A : Address)
    (payload : ByteArray) (_ : ¬IsDerivationAddress A) (h : 16 ≤ payload.size) :
    IsQueryBoundP (H (thInput pp A payload)) IsSeedLengthQuery 0 :=
  H_isQueryBoundP_seedLength (by rw [size_thInput]; omega)

/-- In the game, a derivation from any scheme seed is not a seed-length query.

It hashes the parameter, the address and the 32-byte seed, at least 64 bytes. -/
theorem seedPrf_H_isQueryBoundP_seedLength (s : Seed) (pp : PublicParam) (A : Address)
    (suffix : ByteArray) : IsQueryBoundP (seedPrf H s pp A suffix) IsSeedLengthQuery 0 :=
  H_isQueryBoundP_seedLength (by
    rw [size_thInput, ByteArray.size_append, Base.size_packBytes]
    simp only [SEED_LEN]
    omega)

/-- In the game, signing from the derivations of any scheme seed makes no seed-length query.

Only the hash that grows the scheme seed from the key's seed has 43 bytes. -/
theorem signDerived_H_isQueryBoundP_seedLength (s : Seed) (pp : PublicParam) (msg : Message) :
    IsQueryBoundP (signDerived H (seedPrf H s) pp msg) IsSeedLengthQuery 0 :=
  signDerived_isQueryBoundP_zero H _ H_thInput_isQueryBoundP_seedLength
    (seedPrf_H_isQueryBoundP_seedLength s) pp msg

/-- In the game, the public key of the derivations of any scheme seed makes no seed-length
query. -/
theorem publicKeyOf_H_isQueryBoundP_seedLength (s : Seed) :
    IsQueryBoundP (publicKeyOf H (seedPrf H s)) IsSeedLengthQuery 0 :=
  publicKeyOf_isQueryBoundP_zero H _ H_thInput_isQueryBoundP_seedLength
    (seedPrf_H_isQueryBoundP_seedLength s)

/-- In the game, verification makes no seed-length query. -/
theorem verifyWith_H_isQueryBoundP_seedLength (pk : PublicKey) (msg : Message)
    (sig : Signature) : IsQueryBoundP (verifyWith H pk msg sig) IsSeedLengthQuery 0 :=
  verifyWith_isQueryBoundP_zero H H_thInput_isQueryBoundP_seedLength pk msg sig

/-- In the game, one hash call is at most one seed-length query. -/
theorem H_isQueryBoundP_seedLength_one (x : ByteArray) :
    IsQueryBoundP (H x) IsSeedLengthQuery 1 :=
  (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)

/-- In the game, key generation makes one seed-length query at most: the scheme seed's. -/
theorem keyGenWith_H_isQueryBoundP_seedLength (seed : Seed) :
    IsQueryBoundP (keyGenWith H seed) IsSeedLengthQuery 1 :=
  isQueryBoundP_bind (m := 0) (H_isQueryBoundP_seedLength_one _) fun s _ =>
    isQueryBoundP_bind_zero _ _ (publicKeyOf_H_isQueryBoundP_seedLength s)
      fun _ => isQueryBoundP_pure _ _ _

/-- In the game, signing makes one seed-length query at most: the scheme seed's. -/
theorem signWith_H_isQueryBoundP_seedLength (sk : SecretKey) (msg : Message) :
    IsQueryBoundP (signWith H sk msg) IsSeedLengthQuery 1 :=
  isQueryBoundP_bind (m := 0) (H_isQueryBoundP_seedLength_one _) fun s _ =>
    isQueryBoundP_bind_zero _ _ (publicParamOf_isQueryBoundP_zero _
      (seedPrf_H_isQueryBoundP_seedLength s)) fun pp =>
      signDerived_H_isQueryBoundP_seedLength s pp msg

end EthLib.Cryptography.Sphincs.Unforgeability
