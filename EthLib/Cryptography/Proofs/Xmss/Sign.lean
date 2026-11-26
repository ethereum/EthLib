module

public import EthLib.Cryptography.Xmss.Sign
public import EthLib.Cryptography.Proofs.Xmss.KeyGen
public import EthLib.Cryptography.Proofs.Xmss.Ots
public import EthLib.Cryptography.Proofs.Xmss.Trials
public import EthLib.Cryptography.Proofs.Xmss.Serialization
public import EthLib.Cryptography.Proofs.Xmss.Tree
public import EthLib.Cryptography.Proofs.Xmss.Verify

/-!
# Proofs: leanXMSS signing

What signing computes, and how it can fail.

Each theorem holds for every hash function `f`, run in the identity monad.

`sign` is the case `f = hash`, by a theorem that signing with Keccak-256 is the signer over it.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.Xmss.Internal (signRootWith cacheTreeWith fetchTreeWith)

variable {f : Array UInt64 → Lanes4}

/-! ## Keys that key generation and signing reach

A key holds the trees of a seed when its parts are what the seed gives.

Key generation gives such a key, and signing keeps it one. -/

/-- A secret key that holds what its seed gives.

Its scheme seed, parameter and top tree are those of the seed.

Each kept tree is the tree its index names, built and signed from the key's seed. -/
structure SecretKey.IsOfSeed (H : Array UInt64 → Id Lanes4) (seed : Seed)
    (sk : SecretKey) : Prop where
  /-- The scheme seed `S` of the seed. -/
  schemeSeed_eq : sk.schemeSeed = (Xmss.schemeSeed H seed).run
  /-- The parameter `P`, derived from `S`. -/
  publicParam_eq : sk.publicParam = (publicParamOf (seedPrf H sk.schemeSeed)).run
  /-- The top tree, built from `S`. -/
  top_eq : sk.top = (build H sk.publicParam (seedPrf H sk.schemeSeed) .top LAYER_HEIGHT 0).run
  /-- Each kept tree, with its top signature, as signing builds it from `S`. -/
  cache_eq : ∀ t ∈ sk.cache, t = (cacheTreeWith H (seedPrf H sk.schemeSeed) sk t.index).run

section OfSeed

variable {H : Array UInt64 → Id Lanes4} {seed : Seed} {sk : SecretKey}

/-- Key generation gives a key with the trees of its seed, and no bottom tree. -/
theorem isOfSeed_keyGenWith (H : Array UInt64 → Id Lanes4) (seed : Seed) :
    (keyGenWith H seed).run.2.IsOfSeed H seed :=
  ⟨rfl, rfl, rfl, fun _ h => absurd h List.not_mem_nil⟩

/-- The top signature of a root: the top key's one-time signature, with the key's path.

The path is read from the top tree, and it is the path the seed gives. -/
theorem signRootWith_run (h : sk.IsOfSeed H seed) {b : Nat} (hb : b < 2 ^ LAYER_HEIGHT)
    (root : Digest) :
    (signRootWith H (seedPrf H sk.schemeSeed) sk b root).run =
      match (otsSign H sk.publicParam (seedPrf H sk.schemeSeed) .top (UInt32.ofNat b)
          root.toArray).run with
      | none => .error (.noAdmissibleEncoding .top b)
      | some (randomizer, chainValues) =>
        .ok { randomizer := randomizer, chainValues := chainValues,
              path := (path H sk.publicParam (seedPrf H sk.schemeSeed) .top b).run } := by
  -- The top key's path, read from the top tree, is the path computed from the seed.
  have hpath : sk.top.path LAYER_HEIGHT b =
      (path H sk.publicParam (seedPrf H sk.schemeSeed) .top b).run := by
    have := path_build_run (H := H) (publicParam := sk.publicParam) (prf := seedPrf H sk.schemeSeed)
      (layer := .top) b
    rwa [Nat.div_eq_of_lt hb, ← h.top_eq] at this
  unfold signRootWith
  simp only [Internal.otsSignTrials_hashTrials]
  rw [Id.run_bind]
  -- Name the top search, so no tree is evaluated.
  cases (otsSign H sk.publicParam (seedPrf H sk.schemeSeed) .top (UInt32.ofNat b)
      root.toArray).run with
  | none => rfl
  | some found =>
    obtain ⟨randomizer, chainValues⟩ := found
    simp only [Id.run_pure, hpath]

/-- A fetched tree is the tree its index names, as signing builds it from the seed.

The updated key still holds the trees of its seed. -/
theorem fetchTreeWith_run (h : sk.IsOfSeed H seed) (b : Nat) :
    (fetchTreeWith H (seedPrf H sk.schemeSeed) sk b).run.1 =
        (cacheTreeWith H (seedPrf H sk.schemeSeed) sk b).run ∧
      (fetchTreeWith H (seedPrf H sk.schemeSeed) sk b).run.2.IsOfSeed H seed := by
  unfold fetchTreeWith
  split
  next t ht =>
    -- A kept tree moves to the front; the others stay.
    have hmem := List.mem_of_find?_eq_some ht
    have hidx : t.index = b := by simpa using List.find?_some ht
    refine ⟨hidx ▸ h.cache_eq t hmem,
      ⟨h.schemeSeed_eq, h.publicParam_eq, h.top_eq, fun u hu => ?_⟩⟩
    rcases List.mem_cons.1 hu with rfl | hu
    · exact h.cache_eq _ hmem
    · exact h.cache_eq u (List.mem_filter.1 hu).1
  next =>
    -- A new tree goes in front, and the trees past the limit are dropped.
    refine ⟨rfl, ⟨h.schemeSeed_eq, h.publicParam_eq, h.top_eq, fun u hu => ?_⟩⟩
    rcases List.mem_cons.1 (List.mem_of_mem_take hu) with rfl | hu
    · rfl
    · exact h.cache_eq u hu

/-- Signing keeps a key with the trees of its seed. -/
theorem isOfSeed_signWith (h : sk.IsOfSeed H seed) (idx : LeafIndex) (msg : Message) :
    (signWith H sk idx msg).run.2.IsOfSeed H seed := by
  have hfetch := (fetchTreeWith_run h (bottomTree idx)).2
  unfold signWith Internal.signWithTrials
  simp only [Internal.otsSignTrials_hashTrials]
  rw [Id.run_bind]
  cases (otsSign H sk.publicParam (seedPrf H sk.schemeSeed) .bottom (UInt32.ofNat idx.toNat)
      (msg.toArray)).run with
  | none => exact h
  | some found =>
    obtain ⟨randomizer, chainValues⟩ := found
    rw [Id.run_bind]
    -- Name the fetched tree and key: only the key matters.
    generalize (fetchTreeWith H (seedPrf H sk.schemeSeed) sk (bottomTree idx)).run = r
      at hfetch ⊢
    obtain ⟨t, sk'⟩ := r
    dsimp only at hfetch ⊢
    cases t.top <;> exact hfetch

end OfSeed

/-- The keys that key generation from a seed, then any sequence of signatures, give. -/
inductive SecretKey.Reachable (H : Array UInt64 → Id Lanes4) (seed : Seed) :
    SecretKey → Prop
  /-- The key of key generation. -/
  | keyGen : SecretKey.Reachable H seed (keyGenWith H seed).run.2
  /-- A reachable key, updated by signing a message at a leaf index. -/
  | sign {sk : SecretKey} (idx : LeafIndex) (msg : Message) :
      SecretKey.Reachable H seed sk → SecretKey.Reachable H seed (signWith H sk idx msg).run.2

/-- A reachable key holds the trees of its seed. -/
theorem SecretKey.Reachable.isOfSeed {H : Array UInt64 → Id Lanes4} {seed : Seed}
    {sk : SecretKey} (h : sk.Reachable H seed) : sk.IsOfSeed H seed := by
  induction h with
  | keyGen => exact isOfSeed_keyGenWith H seed
  | sign idx msg _ ih => exact isOfSeed_signWith ih idx msg

/-- **A reachable key gives the note's signature, byte for byte, at every leaf index.**

`s` and `publicParam` are the scheme seed and the parameter of the seed.

- The bottom key `idx` signs the message, with its path in bottom tree `b`.
- The top key `b` signs the root of bottom tree `b`, with its path in the top tree.

Either search finding no codeword is the error of its layer.

So the trees a key keeps, and the order it used them in, never change a signature.

It holds for every hash in the identity monad. -/
theorem SecretKey.Reachable.signWith_fst {H : Array UInt64 → Id Lanes4} {seed : Seed}
    {sk : SecretKey} {s : Seed} {publicParam : PublicParam} (h : sk.Reachable H seed)
    (hs : (Xmss.schemeSeed H seed).run = s) (hpp : (publicParamOf (seedPrf H s)).run = publicParam)
    (idx : LeafIndex) (msg : Message) :
    (signWith H sk idx msg).run.1 =
      match (otsSign H publicParam (seedPrf H s) .bottom
        (UInt32.ofNat idx.toNat) msg.toArray).run with
      | none => .error (.noAdmissibleEncoding .bottom idx.toNat)
      | some (randomizer, chainValues) =>
        match (otsSign H publicParam (seedPrf H s) .top (UInt32.ofNat (bottomTree idx))
            (node H publicParam (seedPrf H s) .bottom LAYER_HEIGHT
              (bottomTree idx)).run.toArray).run with
        | none => .error (.noAdmissibleEncoding .top (bottomTree idx))
        | some (topRandomizer, topChainValues) =>
          .ok
            { leafIndex := idx
              bottom :=
                { randomizer := randomizer, chainValues := chainValues
                  path := (path H publicParam (seedPrf H s) .bottom idx.toNat).run }
              top :=
                { randomizer := topRandomizer, chainValues := topChainValues
                  path := (path H publicParam (seedPrf H s) .top (bottomTree idx)).run } } := by
  have hk := h.isOfSeed
  have hsk : sk.schemeSeed = s := hk.schemeSeed_eq.trans hs
  have hppk : sk.publicParam = publicParam := by rw [hk.publicParam_eq, hsk, hpp]
  subst hsk hppk
  have hfetch := (fetchTreeWith_run hk (bottomTree idx)).1
  -- The key's path and the root both come from the one build of bottom tree `b`.
  have hpath : (build H sk.publicParam (seedPrf H sk.schemeSeed) .bottom LAYER_HEIGHT
      (bottomTree idx)).run.path LAYER_HEIGHT idx.toNat =
        (path H sk.publicParam (seedPrf H sk.schemeSeed) .bottom idx.toNat).run :=
    path_build_run _
  have hroot := value_build_run (H := H) (publicParam := sk.publicParam)
    (prf := seedPrf H sk.schemeSeed)
    (layer := .bottom) LAYER_HEIGHT (bottomTree idx)
  unfold signWith Internal.signWithTrials
  simp only [Internal.otsSignTrials_hashTrials]
  rw [Id.run_bind]
  -- Name the bottom search, so no tree is evaluated.
  cases (otsSign H sk.publicParam (seedPrf H sk.schemeSeed) .bottom (UInt32.ofNat idx.toNat)
      (msg.toArray)).run with
  | none => rfl
  | some found =>
    obtain ⟨randomizer, chainValues⟩ := found
    rw [Id.run_bind]
    -- Name the fetched tree: it is the tree that signing builds, with its top signature.
    generalize (fetchTreeWith H (seedPrf H sk.schemeSeed) sk (bottomTree idx)).run = r
      at hfetch ⊢
    obtain ⟨t, sk'⟩ := r
    dsimp only at hfetch ⊢
    have htree : t.tree = (build H sk.publicParam (seedPrf H sk.schemeSeed) .bottom LAYER_HEIGHT
        (bottomTree idx)).run := by
      rw [hfetch]
      rfl
    have htop : t.top = (signRootWith H (seedPrf H sk.schemeSeed) sk (bottomTree idx)
        (build H sk.publicParam (seedPrf H sk.schemeSeed) .bottom LAYER_HEIGHT
          (bottomTree idx)).run.value).run := by
      rw [hfetch]
      rfl
    rw [htop, hroot, signRootWith_run hk (bottomTree_lt idx), htree, hpath]
    cases (otsSign H sk.publicParam (seedPrf H sk.schemeSeed) .top (UInt32.ofNat (bottomTree idx))
        (node H sk.publicParam (seedPrf H sk.schemeSeed) .bottom LAYER_HEIGHT
          (bottomTree idx)).run.toArray).run <;> rfl

/-- Two keys reachable from one seed sign alike: the same signature or the same error. -/
theorem SecretKey.Reachable.signWith_fst_eq {H : Array UInt64 → Id Lanes4} {seed : Seed}
    {sk sk' : SecretKey} (h : sk.Reachable H seed) (h' : sk'.Reachable H seed)
    (idx : LeafIndex) (msg : Message) :
    (signWith H sk idx msg).run.1 = (signWith H sk' idx msg).run.1 := by
  rw [h.signWith_fst rfl rfl, h'.signWith_fst rfl rfl]

/-- **A reachable key's signature holds one honest signature per layer.**

- The bottom key `idx` signs the message, and the path is the key's path in bottom tree `b`.
- The top key `b` signs the root of bottom tree `b`, and the path is its path in the top tree. -/
theorem SecretKey.Reachable.signWith_eq_ok {H : Array UInt64 → Id Lanes4} {seed : Seed}
    {sk : SecretKey} {s : Seed} {publicParam : PublicParam} (h : sk.Reachable H seed)
    (hs : (Xmss.schemeSeed H seed).run = s) (hpp : (publicParamOf (seedPrf H s)).run = publicParam)
    {idx : LeafIndex} {msg : Message} {σ : Signature} (hσ : (signWith H sk idx msg).run.1 = .ok σ) :
    σ.leafIndex = idx ∧
      (otsSign H publicParam (seedPrf H s) .bottom (UInt32.ofNat idx.toNat) msg.toArray).run
        = some (σ.bottom.randomizer, σ.bottom.chainValues) ∧
      σ.bottom.path = (path H publicParam (seedPrf H s) .bottom idx.toNat).run ∧
      (otsSign H publicParam (seedPrf H s) .top (UInt32.ofNat (bottomTree idx))
          (node H publicParam (seedPrf H s) .bottom LAYER_HEIGHT (bottomTree idx)).run.toArray).run
        = some (σ.top.randomizer, σ.top.chainValues) ∧
      σ.top.path = (path H publicParam (seedPrf H s) .top (bottomTree idx)).run := by
  rw [h.signWith_fst hs hpp] at hσ
  -- Each search either fails, which is an error, or gives the layer's signature.
  cases hbottom : (otsSign H publicParam (seedPrf H s) .bottom
    (UInt32.ofNat idx.toNat) msg.toArray).run with
  | none =>
    rw [hbottom] at hσ
    cases hσ
  | some found =>
    obtain ⟨randomizer, chainValues⟩ := found
    rw [hbottom] at hσ
    cases htop : (otsSign H publicParam (seedPrf H s) .top (UInt32.ofNat (bottomTree idx))
        (node H publicParam (seedPrf H s) .bottom LAYER_HEIGHT
          (bottomTree idx)).run.toArray).run with
    | none =>
      rw [htop] at hσ
      cases hσ
    | some found =>
      obtain ⟨topRandomizer, topChainValues⟩ := found
      rw [htop] at hσ
      cases hσ
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Signing with Keccak-256 is the signer over the hash, byte for byte, key included.**

Its randomizer trials permute a state built once per search, and give what hashing gives. -/
theorem sign_eq (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    Xmss.sign sk idx msg = (signWith hashId sk idx msg).run := by
  rw [Xmss.sign, keccakTrials_eq, signWith]

/-- **Key generation gives the root of the top tree and the parameter `P` of the seed.**

The root is node 0 on level 16 of the top layer. -/
theorem keyGenWith_fst (H : Array UInt64 → Id Lanes4) (seed : Seed) :
    (keyGenWith H seed).run.1 =
      { root := (node H (publicParamOf (seedPrf H (schemeSeed H seed).run)).run
          (seedPrf H (schemeSeed H seed).run) .top LAYER_HEIGHT 0).run
        publicParam := (publicParamOf (seedPrf H (schemeSeed H seed).run)).run } := by
  simp only [keyGenWith, Internal.keyGenFrom, Id.run_bind, Id.run_pure, value_build_run]

/-! ## Signatures of the specification's signer

The specification's signer reads its trees from the key, or builds and keeps them.
-/

/-- A signature holds the leaf index it was signed at, whatever the key. -/
theorem leafIndex_signWith {H : Array UInt64 → Id Lanes4} {sk : SecretKey}
    {idx : LeafIndex} {m : Message} {σ : Signature} (h : (signWith H sk idx m).run.1 = .ok σ) :
    σ.leafIndex = idx := by
  unfold signWith Internal.signWithTrials at h
  simp only [Internal.otsSignTrials_hashTrials] at h
  rw [Id.run_bind] at h
  generalize (otsSign H sk.publicParam (seedPrf H sk.schemeSeed) .bottom (UInt32.ofNat idx.toNat)
      m.toArray).run = found at h
  rcases found with _ | ⟨randomizer, chainValues⟩
  · cases h
  · rw [Id.run_bind] at h
    generalize (fetchTreeWith H (seedPrf H sk.schemeSeed) sk (bottomTree idx)).run = r at h
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
  rw [sign_eq] at h
  rw [signatureIndex_encodeSignature, leafIndex_signWith h]

/-- With a reachable key, signing fails only when one layer's one-time key finds no codeword. -/
theorem sign_error {seed : Seed} {sk : SecretKey} (hsk : sk.Reachable (pureHash f) seed)
    {idx : LeafIndex} {m : Message} {err : XmssError}
    (h : (signWith (pureHash f) sk idx m).run.1 = .error err) :
    ∃ layer key, err = .noAdmissibleEncoding layer key := by
  rw [hsk.signWith_fst rfl rfl] at h
  -- The error comes from one of the two searches.
  split at h
  · cases h
    exact ⟨_, _, rfl⟩
  · split at h
    · cases h
      exact ⟨_, _, rfl⟩
    · cases h

end EthLib.Cryptography.Xmss
