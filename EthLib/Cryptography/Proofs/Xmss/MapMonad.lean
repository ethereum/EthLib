module

public import EthLib.Cryptography.Xmss.Sign
public import EthLib.Cryptography.Proofs.HashSig
public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Proofs.Merkle.Completeness

/-!
# Proofs: the leanXMSS algorithms commute with maps of monads

Take a map of monads that keeps `pure` and `bind`.

It sends each algorithm over a hash `H` and a seed function to the algorithm over their images.

Simulating the oracle queries of a computation is such a map.

So a game written over one oracle is, once simulated, the same game over another.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {m m' : Type → Type} [Monad m] [Monad m'] (φ : ∀ {β : Type}, m β → m' β)
  (map_pure : ∀ {β : Type} (b : β), φ (pure b) = pure b)
  (map_bind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ x >>= fun b => φ (f b))
  (H : ByteArray → m (Vector UInt8 32)) (prf : SeedPrf m)

include map_pure map_bind

/-! ## Hashing and chains -/

/-- A tweakable hash call, over the image of `H`. -/
theorem th_map_monad (pp : PublicParam) (address : Address) (payload : ByteArray) :
    φ (th H pp address payload) = th (fun x => φ (H x)) pp address payload := by
  simp only [th, map_bind, map_pure]

/-- The starts of a key's chains, over the image of the seed function. -/
theorem chainStarts_map_monad (pp : PublicParam) (layer : Layer) (e : UInt32) :
    φ (chainStarts pp prf layer e) =
      chainStarts pp (fun pp a suffix => φ (prf pp a suffix)) layer e := by
  simp only [chainStarts, map_bind, map_pure, HashSig.ofFnInOrder_map_monad φ map_pure map_bind]

/-- A walk on one chain, over the image of `H`. -/
theorem chain_map_monad (pp : PublicParam) (layer : Layer) (e : UInt32) (i : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    φ (chain H pp layer e i start steps h value) =
      chain (fun x => φ (H x)) pp layer e i start steps h value := by
  simp only [chain, Wots.chain_map_monad φ map_pure map_bind, chainStep,
    th_map_monad φ map_pure map_bind]
  rfl

/-- The leaf of a key, over the images of `H` and of the seed function. -/
theorem otsPublicLeaf_map_monad (pp : PublicParam) (layer : Layer) (e : UInt32) :
    φ (otsPublicLeaf H pp prf layer e) =
      otsPublicLeaf (fun x => φ (H x)) pp (fun pp a suffix => φ (prf pp a suffix)) layer e := by
  simp only [otsPublicLeaf, map_bind, chainStarts_map_monad φ map_pure map_bind,
    HashSig.ofFnInOrder_map_monad φ map_pure map_bind, chain_map_monad φ map_pure map_bind,
    otsLeafHash, th_map_monad φ map_pure map_bind]

/-! ## Trees -/

/-- A node of a layer, over the images of `H` and of the seed function. -/
theorem node_map_monad (pp : PublicParam) (layer : Layer) (level j : Nat) :
    φ (node H pp prf layer level j) =
      node (fun x => φ (H x)) pp (fun pp a suffix => φ (prf pp a suffix)) layer level j := by
  simp only [node, Merkle.node_map _ φ map_bind, nodeHash, leaves,
    th_map_monad φ map_pure map_bind, otsPublicLeaf_map_monad φ map_pure map_bind]
  rfl

/-- The path of a key, over the images of `H` and of the seed function. -/
theorem path_map_monad (pp : PublicParam) (layer : Layer) (e : Nat) :
    φ (path H pp prf layer e) =
      path (fun x => φ (H x)) pp (fun pp a suffix => φ (prf pp a suffix)) layer e := by
  simp only [path, Merkle.path_map _ φ map_pure map_bind, nodeHash, leaves,
    th_map_monad φ map_pure map_bind, otsPublicLeaf_map_monad φ map_pure map_bind]
  rfl

/-- The root a path leads to, over the image of `H`. -/
theorem fold_map_monad (pp : PublicParam) (layer : Layer) (e : Nat) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) :
    φ (fold H pp layer e leaf pi) = fold (fun x => φ (H x)) pp layer e leaf pi := by
  simp only [fold, Merkle.climb_map_monad _ φ map_pure map_bind, nodeHash,
    th_map_monad φ map_pure map_bind]
  rfl

/-! ## Verification -/

/-- The leaf a one-time signature leads to, over the image of `H`. -/
theorem otsLeaf_map_monad (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray)
    (rho : Randomizer) (y : Vector Digest V) :
    φ (otsLeaf H pp layer e msg rho y) = otsLeaf (fun x => φ (H x)) pp layer e msg rho y := by
  simp only [otsLeaf, map_bind, messageDigest, th_map_monad φ map_pure map_bind]
  refine bind_congr fun d => ?_
  cases codeword? d with
  | none => exact map_pure _
  | some x =>
    simp only [map_bind, map_pure, HashSig.ofFnInOrder_map_monad φ map_pure map_bind,
      chain_map_monad φ map_pure map_bind, otsLeafHash, th_map_monad φ map_pure map_bind]

/-- The root one layer's signature leads to, over the image of `H`. -/
theorem layerRoot_map_monad (pp : PublicParam) (layer : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature) :
    φ (layerRoot H pp layer e msg sig) = layerRoot (fun x => φ (H x)) pp layer e msg sig := by
  simp only [layerRoot, map_bind, otsLeaf_map_monad φ map_pure map_bind]
  refine bind_congr fun r => ?_
  cases r with
  | none => exact map_pure _
  | some leaf => simp only [map_bind, map_pure, fold_map_monad φ map_pure map_bind]

/-! ## Signing

The codeword test maps a digest, so these lemmas also ask that the map keep `map`. -/

section Sign

variable (map_map : ∀ {β γ : Type} (f : β → γ) (x : m β), φ (f <$> x) = f <$> φ x)

/-- The base of the randomizer trials, over the image of the seed function. -/
theorem randomizerBase_map_monad (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) :
    φ (randomizerBase pp prf layer e msg) =
      randomizerBase pp (fun pp a suffix => φ (prf pp a suffix)) layer e msg :=
  (map_bind _ _).trans (bind_congr fun _ => map_pure _)

include map_map

/-- The codeword search, over the image of `H`. -/
theorem findCodeword_map_monad (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    φ (Internal.findCodeword H pp layer e msg base c fuel) =
      Internal.findCodeword (fun x => φ (H x)) pp layer e msg base c fuel := by
  simp only [Internal.findCodeword, Wots.findFirst_map_monad φ map_pure map_bind, map_map,
    messageDigest, th_map_monad φ map_pure map_bind]

/-- A one-time signature, over the images of `H` and of the seed function. -/
theorem otsSign_map_monad (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray) :
    φ (otsSign H pp prf layer e msg) =
      otsSign (fun x => φ (H x)) pp (fun pp a suffix => φ (prf pp a suffix)) layer e msg := by
  simp only [otsSign, map_bind, randomizerBase_map_monad φ map_pure map_bind,
    findCodeword_map_monad φ map_pure map_bind H map_map]
  refine bind_congr fun base => bind_congr fun r => ?_
  cases r with
  | none => exact map_pure _
  | some r =>
    simp only [map_bind, map_pure, chainStarts_map_monad φ map_pure map_bind,
      HashSig.ofFnInOrder_map_monad φ map_pure map_bind, chain_map_monad φ map_pure map_bind]

/-- One layer's signature, over the images of `H` and of the seed function. -/
theorem signLayer_map_monad (pp : PublicParam) (layer : Layer) (e : Nat) (msg : ByteArray) :
    φ (signLayer H pp prf layer e msg) =
      signLayer (fun x => φ (H x)) pp (fun pp a suffix => φ (prf pp a suffix)) layer e msg := by
  simp only [signLayer, map_bind, otsSign_map_monad φ map_pure map_bind H prf map_map]
  refine bind_congr fun r => ?_
  cases r with
  | none => exact map_pure _
  | some r => simp only [map_bind, map_pure, path_map_monad φ map_pure map_bind]

end Sign

/-! ## The algorithms -/

/-- The public parameter, over the image of the seed function. -/
theorem publicParamOf_map_monad :
    φ (publicParamOf prf) = publicParamOf fun pp a suffix => φ (prf pp a suffix) := by
  exact (map_bind _ _).trans (bind_congr fun _ => map_pure _)

/-- The public key, over the images of `H` and of the seed function. -/
theorem publicKeyOf_map_monad :
    φ (publicKeyOf H prf) =
      publicKeyOf (fun x => φ (H x)) fun pp a suffix => φ (prf pp a suffix) := by
  simp only [publicKeyOf, map_bind, map_pure, publicParamOf_map_monad φ map_pure map_bind,
    node_map_monad φ map_pure map_bind]

/-- A signature from the derivations, over the images of `H` and of the seed function. -/
theorem signDerived_map_monad
    (map_map : ∀ {β γ : Type} (f : β → γ) (x : m β), φ (f <$> x) = f <$> φ x)
    (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    φ (signDerived H prf pp idx msg) =
      signDerived (fun x => φ (H x)) (fun pp a suffix => φ (prf pp a suffix)) pp idx msg := by
  simp only [signDerived, map_bind, signLayer_map_monad φ map_pure map_bind H prf map_map]
  refine bind_congr fun r => ?_
  cases r with
  | error err => exact map_pure _
  | ok bottom =>
    simp only [map_bind, map_pure, node_map_monad φ map_pure map_bind,
      signLayer_map_monad φ map_pure map_bind H prf map_map]
    refine bind_congr fun _ => bind_congr fun _ => bind_congr fun r => ?_
    cases r with
    | error err => exact map_pure _
    | ok top => simp only [map_bind, map_pure]

/-- Verification, over the image of `H`. -/
theorem verifyWith_map_monad (pk : PublicKey) (msg : Message) (sig : Signature) :
    φ (verifyWith H pk msg sig) = verifyWith (fun x => φ (H x)) pk msg sig := by
  simp only [verifyWith, map_bind, layerRoot_map_monad φ map_pure map_bind]
  refine bind_congr fun r => ?_
  cases r with
  | none => exact map_pure _
  | some bottomRoot =>
    simp only [map_bind, layerRoot_map_monad φ map_pure map_bind]
    refine bind_congr fun r => ?_
    cases r with
    | none => exact map_pure _
    | some root => exact map_pure _

end EthLib.Cryptography.Xmss
