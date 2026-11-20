module

public import EthLib.Cryptography.Proofs.Xmss.Reference
public import EthLib.Cryptography.Proofs.Xmss.KeyGen
public import EthLib.Cryptography.Proofs.Xmss.Ots
public import EthLib.Cryptography.Proofs.Xmss.Serialization
public import EthLib.Cryptography.Proofs.Xmss.Tree

/-!
# Proofs: leanXMSS signing

What a successful signature holds, and how signing can fail.

Each theorem holds for every hash function `f`, run in the identity monad.

`sign` is the case `f = hash`.

The stateless signer of the note builds the bottom tree once, for the key's path and the root.

It signs exactly as the form that computes the path, then builds the whole tree for the root.

The specification's signer reads its trees from the key, or builds and keeps them.

Every key that key generation and signing reach holds the trees the stateless signer builds.

So that signer returns the stateless signature, byte for byte, whatever trees the key keeps.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {f : ByteArray → Vector UInt8 32} {pp : PublicParam} {s : Seed} {prf : SeedPrf Id}
  {layer : Layer} {e : Nat}
  {msg : ByteArray} {sig : LayerSignature}

/-! ## One build gives the path and the root -/

/-- Reading the key's path and the root from one build signs as computing them apart.

The right side signs the bottom layer with its path, then computes the root of the whole tree.

Both sides give the same signature, byte for byte, for every hash in the identity monad. -/
theorem signDerived_eq_path_node (H : ByteArray → Id (Vector UInt8 32)) (prf : SeedPrf Id)
    (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    signDerived H prf pp idx msg = (do
      let bottom ← match ← signLayer H pp prf .bottom idx.toNat (packBytes msg) with
        | .ok sig => pure sig
        | .error err => return .error err
      let bottomRoot ← node H pp prf .bottom LAYER_HEIGHT (bottomTree idx)
      let top ← match ← signLayer H pp prf .top (bottomTree idx) (packBytes bottomRoot) with
        | .ok sig => pure sig
        | .error err => return .error err
      return .ok { leafIndex := idx, bottom, top }) := by
  unfold signDerived signLayer
  -- Name the bottom one-time signature, so no tree is evaluated.
  generalize otsSign H pp prf .bottom (UInt32.ofNat idx.toNat) (packBytes msg) = found
  rcases found with _ | ⟨randomizer, chainValues⟩
  · rfl
  · -- The path and the root, computed apart, are the two read from the one build.
    have hpath : path H pp prf .bottom idx.toNat =
        (build H pp prf .bottom LAYER_HEIGHT (bottomTree idx)).run.path LAYER_HEIGHT idx.toNat :=
      (path_build_run idx.toNat).symm
    have hroot : node H pp prf .bottom LAYER_HEIGHT (bottomTree idx) =
        (build H pp prf .bottom LAYER_HEIGHT (bottomTree idx)).run.value :=
      (value_build_run _ _).symm
    rw [hpath, hroot]
    rfl

/-! ## The signer as a value

`rw` unfolds the signer, not `simp`, as for the one-time signer. -/

/-- What a layer's signature computes: the one-time signature with the key's path, or the error. -/
theorem signLayer_run :
    (signLayer (pureHash f) pp prf layer e msg).run
      = match (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run with
        | none => .error (.noAdmissibleEncoding layer e)
        | some (randomizer, chainValues) =>
          .ok { randomizer, chainValues, path := (path (pureHash f) pp prf layer e).run } := by
  rw [signLayer, Id.run_bind]
  cases (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run with
  | none => rfl
  | some found => rfl

/-- What signing computes, one layer after the other, as a computation in `Except`.

- `s` and `pp` are the scheme seed and the public parameter, from the secret key's seed.
- Both layers derive their secrets from `s`.
- The top layer signs the root of bottom tree `b`, which signing builds. -/
theorem statelessSignWith_run {seed : Seed} {idx : LeafIndex} {m : Message}
    (hs : (schemeSeed (pureHash f) seed).run = s)
    (hpp : (publicParamOf (seedPrf (pureHash f) s)).run = pp) :
    (statelessSignWith (pureHash f) seed idx m).run
      = (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .bottom idx.toNat
          (packBytes m)).run.bind fun bottom =>
          (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .top (bottomTree idx)
            (packBytes (node (pureHash f) pp (seedPrf (pureHash f) s) .bottom LAYER_HEIGHT
              (bottomTree idx)).run)).run.bind fun top =>
            .ok { leafIndex := idx, bottom, top } := by
  subst hs hpp
  rw [statelessSignWith, Id.run_bind, Id.run_bind, signDerived_eq_path_node, Id.run_bind]
  cases (signLayer (pureHash f)
      (publicParamOf (seedPrf (pureHash f) (schemeSeed (pureHash f) seed).run)).run
      (seedPrf (pureHash f) (schemeSeed (pureHash f) seed).run) .bottom idx.toNat
      (packBytes m)).run with
  | error err => rfl
  | ok bottom =>
    -- No signer is unfolded here, so `simp` may reduce the matches on `.ok`.
    simp only [Id.run_bind, Id.run_pure, Except.bind]
    cases (signLayer (pureHash f)
        (publicParamOf (seedPrf (pureHash f) (schemeSeed (pureHash f) seed).run)).run
        (seedPrf (pureHash f) (schemeSeed (pureHash f) seed).run) .top (bottomTree idx)
        (packBytes (node (pureHash f)
          (publicParamOf (seedPrf (pureHash f) (schemeSeed (pureHash f) seed).run)).run
          (seedPrf (pureHash f) (schemeSeed (pureHash f) seed).run) .bottom LAYER_HEIGHT
          (bottomTree idx)).run)).run with
    | error err => rfl
    | ok top => rfl

/-! ## Layers -/

/-- A layer's signature is a one-time signature, with the key's honest path. -/
theorem signLayer_eq_ok (h : (signLayer (pureHash f) pp prf layer e msg).run = .ok sig) :
    (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run
        = some (sig.randomizer, sig.chainValues) ∧
      sig.path = (path (pureHash f) pp prf layer e).run := by
  rw [signLayer_run] at h
  -- Name the one-time signature, so the match reduces without evaluating it.
  cases hots : (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run with
  | none =>
    rw [hots] at h
    cases h
  | some found =>
    obtain ⟨randomizer, chainValues⟩ := found
    rw [hots] at h
    -- The accepting branch packs the one-time signature with the path.
    cases h
    exact ⟨rfl, rfl⟩

/-- A layer fails only when no randomizer trial gives a codeword. -/
theorem signLayer_error {err : XmssError}
    (h : (signLayer (pureHash f) pp prf layer e msg).run = .error err) :
    (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run = none ∧
      err = .noAdmissibleEncoding layer e := by
  rw [signLayer_run] at h
  cases hots : (otsSign (pureHash f) pp prf layer (UInt32.ofNat e) msg).run with
  | none =>
    rw [hots] at h
    cases h
    exact ⟨rfl, rfl⟩
  | some found =>
    obtain ⟨randomizer, chainValues⟩ := found
    rw [hots] at h
    cases h

/-! ## Signatures -/

/-- A signature holds one honest signature per layer.

- The bottom key `idx` signs the message.
- The top key `b` signs the root of bottom tree `b`. -/
theorem statelessSign_eq_ok {seed : Seed} {idx : LeafIndex} {m : Message} {σ : Signature}
    (hs : (schemeSeed (pureHash f) seed).run = s)
    (hpp : (publicParamOf (seedPrf (pureHash f) s)).run = pp)
    (h : (statelessSignWith (pureHash f) seed idx m).run = .ok σ) :
    σ.leafIndex = idx ∧
      (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .bottom idx.toNat
        (packBytes m)).run = .ok σ.bottom ∧
      (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .top (bottomTree idx)
        (packBytes (node (pureHash f) pp (seedPrf (pureHash f) s) .bottom LAYER_HEIGHT
          (bottomTree idx)).run)).run = .ok σ.top := by
  rw [statelessSignWith_run hs hpp] at h
  -- Each layer is either an error, which propagates, or a value the next step uses.
  cases hbottom : (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .bottom idx.toNat
      (packBytes m)).run with
  | error err =>
    rw [hbottom] at h
    cases h
  | ok bottom =>
    rw [hbottom, Except.bind] at h
    cases htop : (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .top (bottomTree idx)
        (packBytes (node (pureHash f) pp (seedPrf (pureHash f) s) .bottom LAYER_HEIGHT
          (bottomTree idx)).run)).run with
    | error err =>
      rw [htop] at h
      cases h
    | ok top =>
      rw [htop] at h
      cases h
      exact ⟨rfl, rfl, rfl⟩

/-- Signing fails only when one layer's one-time key finds no codeword. -/
theorem statelessSign_error {seed : Seed} {idx : LeafIndex} {m : Message} {err : XmssError}
    (h : (statelessSignWith (pureHash f) seed idx m).run = .error err) :
    ∃ layer key, err = .noAdmissibleEncoding layer key := by
  -- Name the scheme seed and the parameter, so the layers stay short.
  obtain ⟨s, hs⟩ : ∃ s, (schemeSeed (pureHash f) seed).run = s := ⟨_, rfl⟩
  obtain ⟨pp, hpp⟩ : ∃ pp, (publicParamOf (seedPrf (pureHash f) s)).run = pp := ⟨_, rfl⟩
  rw [statelessSignWith_run hs hpp] at h
  -- The error comes from one of the two layers.
  cases hbottom : (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .bottom idx.toNat
      (packBytes m)).run with
  | error e' =>
    rw [hbottom] at h
    cases h
    exact ⟨_, _, (signLayer_error hbottom).2⟩
  | ok bottom =>
    rw [hbottom, Except.bind] at h
    cases htop : (signLayer (pureHash f) pp (seedPrf (pureHash f) s) .top (bottomTree idx)
        (packBytes (node (pureHash f) pp (seedPrf (pureHash f) s) .bottom LAYER_HEIGHT
          (bottomTree idx)).run)).run with
    | error e' =>
      rw [htop] at h
      cases h
      exact ⟨_, _, (signLayer_error htop).2⟩
    | ok top =>
      rw [htop] at h
      cases h

/-! ## Keys that key generation and signing reach

A key holds the stateless trees of a seed when it holds what the stateless signer computes.

Key generation gives such a key, and signing keeps it one.

Such a key signs as the stateless signer, byte for byte. -/

/-- The bottom tree of a leaf index is a key of the top tree: it is below `2^16`. -/
theorem bottomTree_lt (idx : LeafIndex) : bottomTree idx < 2 ^ LAYER_HEIGHT := by
  have := idx.toNat_lt_size
  simp only [bottomTree, LAYER_HEIGHT, UInt32.size] at *
  omega

/-- A kept tree as the stateless signer computes it from the scheme seed `s` and the parameter.

The tree is its bottom tree, built from the seed.

The top signature is the top layer's signature of the tree's root, path computed from the seed. -/
def CachedTree.IsStateless (H : ByteArray → Id (Vector UInt8 32)) (s : Seed) (pp : PublicParam)
    (t : CachedTree) : Prop :=
  t.tree = (build H pp (seedPrf H s) .bottom LAYER_HEIGHT t.index).run ∧
    t.top = (signLayer H pp (seedPrf H s) .top t.index (packBytes t.tree.value)).run

/-- A secret key that holds what the stateless signer computes from a seed. -/
structure SecretKey.IsStatelessOf (H : ByteArray → Id (Vector UInt8 32)) (seed : Seed)
    (sk : SecretKey) : Prop where
  /-- The scheme seed `S` of the seed. -/
  schemeSeed_eq : sk.schemeSeed = (Xmss.schemeSeed H seed).run
  /-- The parameter `P`, derived from `S`. -/
  publicParam_eq : sk.publicParam = (publicParamOf (seedPrf H sk.schemeSeed)).run
  /-- The top tree, built from `S`. -/
  top_eq : sk.top = (build H sk.publicParam (seedPrf H sk.schemeSeed) .top LAYER_HEIGHT 0).run
  /-- Each kept tree, with its top signature, as the stateless signer computes it. -/
  cache_isStateless : ∀ t ∈ sk.cache, t.IsStateless H sk.schemeSeed sk.publicParam

section Stateless

variable {H : ByteArray → Id (Vector UInt8 32)} {seed : Seed} {sk : SecretKey}

/-- Key generation gives a key with the stateless trees of its seed, and no bottom tree. -/
theorem isStatelessOf_keyGenWith (H : ByteArray → Id (Vector UInt8 32)) (seed : Seed) :
    (keyGenWith H seed).run.2.IsStatelessOf H seed :=
  ⟨rfl, rfl, rfl, fun _ h => absurd h List.not_mem_nil⟩

/-- The top signature of a root, path read from the top tree, is the one the seed gives. -/
theorem signRootWith_run (h : sk.IsStatelessOf H seed) {b : Nat} (hb : b < 2 ^ LAYER_HEIGHT)
    (root : Digest) :
    (signRootWith H sk b root).run =
      (signLayer H sk.publicParam (seedPrf H sk.schemeSeed) .top b (packBytes root)).run := by
  -- The top key's path, read from the top tree, is the path computed from the seed.
  have hpath : sk.top.path LAYER_HEIGHT b =
      (path H sk.publicParam (seedPrf H sk.schemeSeed) .top b).run := by
    have := path_build_run (H := H) (pp := sk.publicParam) (prf := seedPrf H sk.schemeSeed)
      (layer := .top) b
    rwa [Nat.div_eq_of_lt hb, ← h.top_eq] at this
  unfold signRootWith signLayer
  rw [Id.run_bind, Id.run_bind]
  -- Name the top search, so no tree is evaluated.
  cases (otsSign H sk.publicParam (seedPrf H sk.schemeSeed) .top (UInt32.ofNat b)
      (packBytes root)).run with
  | none => rfl
  | some found =>
    obtain ⟨randomizer, chainValues⟩ := found
    simp only [Id.run_bind, hpath]

/-- A tree built for a key of the top tree is the one the stateless signer computes. -/
theorem isStateless_cacheTreeWith (h : sk.IsStatelessOf H seed) {b : Nat}
    (hb : b < 2 ^ LAYER_HEIGHT) :
    (cacheTreeWith H sk b).run.IsStateless H sk.schemeSeed sk.publicParam :=
  ⟨rfl, signRootWith_run h hb _⟩

/-- A fetched tree is the stateless one of its index.

The updated key still holds the stateless trees. -/
theorem fetchTreeWith_run (h : sk.IsStatelessOf H seed) {b : Nat} (hb : b < 2 ^ LAYER_HEIGHT) :
    (fetchTreeWith H sk b).run.1.index = b ∧
      (fetchTreeWith H sk b).run.1.IsStateless H sk.schemeSeed sk.publicParam ∧
      (fetchTreeWith H sk b).run.2.IsStatelessOf H seed := by
  unfold fetchTreeWith
  split
  next t ht =>
    -- A kept tree moves to the front; the others stay.
    have hmem := List.mem_of_find?_eq_some ht
    refine ⟨by simpa using List.find?_some ht, h.cache_isStateless t hmem,
      ⟨h.schemeSeed_eq, h.publicParam_eq, h.top_eq, fun u hu => ?_⟩⟩
    rcases List.mem_cons.1 hu with rfl | hu
    · exact h.cache_isStateless _ hmem
    · exact h.cache_isStateless u (List.mem_filter.1 hu).1
  next =>
    -- A new tree goes in front, and the trees past the limit are dropped.
    refine ⟨rfl, isStateless_cacheTreeWith h hb,
      ⟨h.schemeSeed_eq, h.publicParam_eq, h.top_eq, fun u hu => ?_⟩⟩
    rcases List.mem_cons.1 (List.mem_of_mem_take hu) with rfl | hu
    · exact isStateless_cacheTreeWith h hb
    · exact h.cache_isStateless u hu

/-- Signing keeps a key with the stateless trees of its seed. -/
theorem isStatelessOf_signWith (h : sk.IsStatelessOf H seed) (idx : LeafIndex) (msg : Message) :
    (signWith H sk idx msg).run.2.IsStatelessOf H seed := by
  have hfetch := (fetchTreeWith_run h (bottomTree_lt idx)).2.2
  unfold signWith
  rw [Id.run_bind]
  cases (otsSign H sk.publicParam (seedPrf H sk.schemeSeed) .bottom (UInt32.ofNat idx.toNat)
      (packBytes msg)).run with
  | none => exact h
  | some found =>
    obtain ⟨randomizer, chainValues⟩ := found
    rw [Id.run_bind]
    -- Name the fetched tree and key: only the key matters.
    generalize (fetchTreeWith H sk (bottomTree idx)).run = r at hfetch ⊢
    obtain ⟨t, sk'⟩ := r
    dsimp only at hfetch ⊢
    cases t.top <;> exact hfetch

/-- A key with the stateless trees of its seed signs as the stateless signer, byte for byte. -/
theorem signWith_fst_of_isStatelessOf (h : sk.IsStatelessOf H seed) (idx : LeafIndex)
    (msg : Message) :
    (signWith H sk idx msg).run.1 = (statelessSignWith H seed idx msg).run := by
  obtain ⟨hindex, ⟨htree, htop⟩, -⟩ := fetchTreeWith_run h (bottomTree_lt idx)
  -- The stateless signer derives the key's scheme seed and parameter.
  have hs : (statelessSignWith H seed idx msg).run =
      (signDerived H (seedPrf H sk.schemeSeed) sk.publicParam idx msg).run := by
    rw [h.publicParam_eq, h.schemeSeed_eq]
    rfl
  rw [hs]
  unfold signWith signDerived
  rw [Id.run_bind, Id.run_bind]
  -- Name the bottom search, so no tree is evaluated.
  cases (otsSign H sk.publicParam (seedPrf H sk.schemeSeed) .bottom (UInt32.ofNat idx.toNat)
      (packBytes msg)).run with
  | none => rfl
  | some found =>
    obtain ⟨randomizer, chainValues⟩ := found
    rw [Id.run_bind, Id.run_bind]
    -- Name the fetched tree, whose tree and top signature are the stateless ones.
    generalize (fetchTreeWith H sk (bottomTree idx)).run = r at hindex htree htop ⊢
    obtain ⟨t, sk'⟩ := r
    dsimp only at hindex htree htop ⊢
    rw [hindex] at htree htop
    rw [← htree, Id.run_bind, ← htop]
    cases t.top <;> rfl

end Stateless

/-- The keys that key generation from a seed, then any sequence of signatures, give. -/
inductive SecretKey.Reachable (H : ByteArray → Id (Vector UInt8 32)) (seed : Seed) :
    SecretKey → Prop
  /-- The key of key generation. -/
  | keyGen : SecretKey.Reachable H seed (keyGenWith H seed).run.2
  /-- A reachable key, updated by signing a message at a leaf index. -/
  | sign {sk : SecretKey} (idx : LeafIndex) (msg : Message) :
      SecretKey.Reachable H seed sk → SecretKey.Reachable H seed (signWith H sk idx msg).run.2

/-- A reachable key holds the stateless trees of its seed. -/
theorem SecretKey.Reachable.isStatelessOf {H : ByteArray → Id (Vector UInt8 32)} {seed : Seed}
    {sk : SecretKey} (h : sk.Reachable H seed) : sk.IsStatelessOf H seed := by
  induction h with
  | keyGen => exact isStatelessOf_keyGenWith H seed
  | sign idx msg _ ih => exact isStatelessOf_signWith ih idx msg

/-- **A reachable key signs as the stateless signer, byte for byte, at every leaf index.**

The key is any one that key generation, then any sequence of signatures, gives.

So the trees a key keeps, and the order it used them in, never change a signature.

It holds for every hash in the identity monad. -/
theorem SecretKey.Reachable.signWith_fst {H : ByteArray → Id (Vector UInt8 32)} {seed : Seed}
    {sk : SecretKey} (h : sk.Reachable H seed) (idx : LeafIndex) (msg : Message) :
    (signWith H sk idx msg).run.1 = (statelessSignWith H seed idx msg).run :=
  signWith_fst_of_isStatelessOf h.isStatelessOf idx msg

/-- **With Keccak-256, a reachable key signs as the stateless signer, byte for byte.** -/
theorem SecretKey.Reachable.sign_fst {seed : Seed} {sk : SecretKey} (h : sk.Reachable hashId seed)
    (idx : LeafIndex) (msg : Message) : (Xmss.sign sk idx msg).1 = statelessSign seed idx msg :=
  h.signWith_fst idx msg

/-- **Key generation gives the public key of the stateless scheme.**

It is the root of the top tree, computed as a node, and the parameter `P`. -/
theorem keyGenWith_fst (H : ByteArray → Id (Vector UInt8 32)) (seed : Seed) :
    (keyGenWith H seed).run.1 = (statelessKeyGenWith H seed).run.2 := by
  simp only [keyGenWith, statelessKeyGenWith, publicKeyOf, Id.run_bind, Id.run_pure,
    value_build_run]

/-! ## Signatures of the specification's signer -/

/-- A signature holds the leaf index it was signed at, whatever the key. -/
theorem leafIndex_signWith {H : ByteArray → Id (Vector UInt8 32)} {sk : SecretKey}
    {idx : LeafIndex} {m : Message} {σ : Signature} (h : (signWith H sk idx m).run.1 = .ok σ) :
    σ.leafIndex = idx := by
  unfold signWith at h
  rw [Id.run_bind] at h
  generalize (otsSign H sk.publicParam (seedPrf H sk.schemeSeed) .bottom (UInt32.ofNat idx.toNat)
      (packBytes m)).run = found at h
  rcases found with _ | ⟨randomizer, chainValues⟩
  · cases h
  · rw [Id.run_bind] at h
    generalize (fetchTreeWith H sk (bottomTree idx)).run = r at h
    obtain ⟨t, sk'⟩ := r
    dsimp only at h
    cases ht : t.top with
    | ok top =>
      rw [ht] at h
      cases h
      rfl
    | error err =>
      rw [ht] at h
      cases h

/-- An encoded signature carries the leaf index it was signed at, whatever the key.

So a verifier that reads the index from the bytes learns which one-time key signed. -/
theorem signatureIndex_sign {sk : SecretKey} {idx : LeafIndex} {m : Message} {σ : Signature}
    (h : (sign sk idx m).1 = .ok σ) :
    signatureIndex (encodeSignature σ) = .ok idx := by
  rw [signatureIndex_encodeSignature, leafIndex_signWith h]

/-- With a reachable key, signing fails only when one layer's one-time key finds no codeword. -/
theorem sign_error {seed : Seed} {sk : SecretKey} (hsk : sk.Reachable (pureHash f) seed)
    {idx : LeafIndex} {m : Message} {err : XmssError}
    (h : (signWith (pureHash f) sk idx m).run.1 = .error err) :
    ∃ layer key, err = .noAdmissibleEncoding layer key :=
  statelessSign_error ((hsk.signWith_fst idx m).symm.trans h)

end EthLib.Cryptography.Xmss
