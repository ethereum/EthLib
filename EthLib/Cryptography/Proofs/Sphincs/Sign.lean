module

public import EthLib.Cryptography.Sphincs.Sign
public import EthLib.Cryptography.Proofs.Sphincs.Ots
public import EthLib.Cryptography.Proofs.Sphincs.Fors
public import EthLib.Cryptography.Proofs.Sphincs.Digest

/-!
# Proofs: leanSPHINCS signing

What a successful signature is made of, and why signing can fail.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## A signer that computes each path and each root apart

It is the reference the signer is proved equal to: proofs use it, and no signer runs it. -/

namespace Recompute

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-- The opening of a FORS tree at a leaf: the leaf's secret, then its path, computed alone. -/
def treeOpen (pkSeed : PkSeed) (prf : Prf m) (idx : Nat) (kappa : Fin FORS_TREES)
    (s : Fin (2 ^ FORS_HEIGHT)) : m TreeOpening := do
  let secret ← forsSecret prf idx kappa s.val
  let path ← Merkle.path (forsNodeHash H pkSeed idx kappa) (forsLeaves H pkSeed prf idx kappa)
    FORS_HEIGHT s.val
  return { secret, path }

/-- The openings of the FORS trees, in order, tree 0 first. -/
def forsSign (pkSeed : PkSeed) (prf : Prf m) (idx : Nat)
    (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) : m (Vector TreeOpening FORS_TREES) :=
  ofFnInOrder FORS_TREES fun kappa => treeOpen H pkSeed prf idx kappa leaves[kappa]

/-- What a layer's key signs: the FORS public key, or the root of the tree below, built anew. -/
def layerMessage (pkSeed : PkSeed) (prf : Prf m) (layer : Layer) (idx : Nat) : m Digest :=
  match layer with
  | .bottom => forsKey H pkSeed prf idx
  | .middle => treeRoot H pkSeed prf .bottom (OtsKey.ofIndex .bottom idx).tree
  | .top => treeRoot H pkSeed prf .middle (OtsKey.ofIndex .middle idx).tree

/-- A layer's signature of a message, with the key's path computed alone. -/
def signLayer (pkSeed : PkSeed) (prf : Prf m) (layer : Layer) (idx : Nat) (msg : Digest) :
    m (Except SphincsError (LayerSignature layer)) := do
  let key := OtsKey.ofIndex layer idx
  let some (counter, chainValues) ← otsSign H pkSeed prf key msg
    | return .error (.noAdmissibleEncoding layer)
  return .ok { counter, chainValues, path := ← path H pkSeed prf layer key.tree key.leaf }

/-- Signing from the secrets, the public key and `R`: each path, then each root, apart. -/
def signDerived (prf : Prf m) (pk : PublicKey) (rho : Randomizer) (msg : Message) :
    m (Except SphincsError Signature) := do
  let pkSeed := pk.pkSeed
  let d ← hMsg H rho pkSeed pk.root msg
  let idx := digestIndex d
  let fors ← forsSign H pkSeed prf idx (digestLeaves d)
  let bottomMsg ← layerMessage H pkSeed prf .bottom idx
  let bottom ← match ← signLayer H pkSeed prf .bottom idx bottomMsg with
    | .ok sig => pure sig
    | .error err => return .error err
  let middleMsg ← layerMessage H pkSeed prf .middle idx
  let middle ← match ← signLayer H pkSeed prf .middle idx middleMsg with
    | .ok sig => pure sig
    | .error err => return .error err
  let topMsg ← layerMessage H pkSeed prf .top idx
  let top ← match ← signLayer H pkSeed prf .top idx topMsg with
    | .ok sig => pure sig
    | .error err => return .error err
  return .ok { randomizer := rho, fors, bottom, middle, top }

/-- Signing: the public key, whose root builds the top tree, then `R`, then each path and root. -/
def signWith (sk : SecretKey) (msg : Message) : m (Except SphincsError Signature) := do
  let key ← expandKey H sk.seed
  let secrets := prf H key.pkSeed sk.seed
  let pk ← publicKeyOf H key.pkSeed secrets
  let rho ← prfMsg H key.skPrf key.pkSeed msg
  signDerived H secrets pk rho msg

end Recompute

-- Each theorem holds for every hash function `f`, run in the identity monad.
--
-- The specification's signer is the case `f = hash`.
variable {f : ByteArray → Vector UInt8 32}

section Layers

variable {pkSeed : PkSeed} {prf : Prf Id} {layer : Layer} {idx : Nat}
  {tree : Merkle.Built Digest} {msg : Digest}

/-! ## The signer as a value

`rw` unfolds the signer, not `simp`, as for the one-time signer. -/

/-- What a layer's signature computes: the one-time signature with the key's path, or the error.

The path is read from the tree it is given. -/
theorem signLayer_run :
    (signLayer (pureHash f) pkSeed prf layer idx tree msg).run
      = match (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run with
        | none => .error (.noAdmissibleEncoding layer)
        | some (counter, chainValues) =>
          .ok { counter, chainValues,
                path := tree.path layer.height (OtsKey.ofIndex layer idx).leaf } := by
  rw [signLayer, Id.run_bind]
  cases (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run with
  | none => rfl
  | some found => rfl

/-- What signing from a source of secrets, `PK.seed`, the top tree and `R` computes, in `Except`.

Each layer signs what the layer below gives, at the index the digest names. -/
theorem signDerived_run {top : Merkle.Built Digest} {rho : Randomizer} {m : Message} :
    (signDerived (pureHash f) prf pkSeed top rho m).run
      = let d := (hMsg (pureHash f) rho pkSeed top.value m).run
        let fors := (forsSign (pureHash f) pkSeed prf (digestIndex d) (digestLeaves d)).run
        let bottomTree := (buildTree (pureHash f) pkSeed prf .bottom
          (OtsKey.ofIndex .bottom (digestIndex d)).tree).run
        let middleTree := (buildTree (pureHash f) pkSeed prf .middle
          (OtsKey.ofIndex .middle (digestIndex d)).tree).run
        (signLayer (pureHash f) pkSeed prf .bottom (digestIndex d) bottomTree fors.2).run.bind
          fun bottom => (signLayer (pureHash f) pkSeed prf .middle (digestIndex d) middleTree
            bottomTree.value).run.bind
          fun middle => (signLayer (pureHash f) pkSeed prf .top (digestIndex d) top
            middleTree.value).run.bind
          fun topSig => .ok ⟨rho, fors.1, bottom, middle, topSig⟩ := by
  rw [signDerived]
  simp only [Id.run_bind]
  -- Each layer is either an error, which ends signing, or a value the next layer uses.
  split
  · rename_i bottom hb
    rw [hb]
    simp only [Id.run_bind, Id.run_pure]
    split
    · rename_i middle hm
      rw [hm]
      simp only [Id.run_bind, Id.run_pure]
      split
      · rename_i topSig ht
        rw [ht]
        rfl
      · rename_i err ht
        rw [ht]
        rfl
    · rename_i err hm
      rw [hm]
      rfl
  · rename_i err hb
    rw [hb]
    rfl

/-! ## Layers -/

/-- A layer signature is the one-time signature of the layer's key, with the key's path in a tree.

The path is read from the tree the layer is given. -/
theorem signLayer_eq_ok {sig : LayerSignature layer}
    (h : (signLayer (pureHash f) pkSeed prf layer idx tree msg).run = .ok sig) :
    (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run
        = some (sig.counter, sig.chainValues) ∧
      sig.path = tree.path layer.height (OtsKey.ofIndex layer idx).leaf := by
  rw [signLayer_run] at h
  -- Name the one-time signature, so the match reduces without evaluating it.
  cases hots : (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run with
  -- No codeword: the result is an error, not a signature.
  | none =>
    rw [hots] at h
    cases h
  -- A codeword: the signature packs the one-time signature with the path.
  | some ots =>
    obtain ⟨counter, chainValues⟩ := ots
    rw [hots] at h
    cases h
    exact ⟨rfl, rfl⟩

/-- A layer fails only when its key finds no codeword, and then says which layer it was. -/
theorem signLayer_error {e : SphincsError}
    (h : (signLayer (pureHash f) pkSeed prf layer idx tree msg).run = .error e) :
    e = .noAdmissibleEncoding layer ∧
      (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run = none := by
  rw [signLayer_run] at h
  cases hots : (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run with
  -- No codeword: the error names the layer.
  | none =>
    rw [hots] at h
    cases h
    exact ⟨rfl, rfl⟩
  -- A codeword: the result is a signature, not an error.
  | some ots =>
    obtain ⟨counter, chainValues⟩ := ots
    rw [hots] at h
    cases h

end Layers

/-! ## Signatures -/

/-- What signing computes: the signature from `PK.seed`, the secrets, the top tree and `R`.

- The secrets are `PRF(PK.seed, SK.seed, ADRS)`.
- The top tree is built from those secrets, and its root is `PK.root`.
- The randomizer is `PRF_msg(SK.prf, PK.seed, M')`, with `SK.prf` expanded from `SK.seed`. -/
theorem signWith_run {sk : SecretKey} {m : Message} :
    (signWith (pureHash f) sk m).run
      = let key := (expandKey (pureHash f) sk.seed).run
        let secrets := prf (pureHash f) key.pkSeed sk.seed
        (signDerived (pureHash f) secrets key.pkSeed
          (buildTree (pureHash f) key.pkSeed secrets .top 0).run
          (prfMsg (pureHash f) key.skPrf key.pkSeed m).run m).run :=
  rfl

/-! ## One build gives the path and the root -/

section Equal

variable (f) (prf : Prf Id) (pkSeed : PkSeed)

/-- An opening read from one build is the opening computed alone, with the tree's root. -/
theorem treeOpen_eq_recompute (idx : Nat) (kappa : Fin FORS_TREES) (s : Fin (2 ^ FORS_HEIGHT)) :
    (treeOpen (pureHash f) pkSeed prf idx kappa s).run
      = ((Recompute.treeOpen (pureHash f) pkSeed prf idx kappa s).run,
          (forsRoot (pureHash f) pkSeed prf idx kappa).run) :=
  treeOpen_run s

/-- The FORS signer gives the openings computed alone, and the FORS public key. -/
theorem forsSign_eq_recompute (idx : Nat) (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    (forsSign (pureHash f) pkSeed prf idx leaves).run
      = ((Recompute.forsSign (pureHash f) pkSeed prf idx leaves).run,
          (forsKey (pureHash f) pkSeed prf idx).run) := by
  rw [forsSign_run, Recompute.forsSign, HashSig.ofFnInOrder_run]
  simp only [treeOpen_eq_recompute]

/-- A layer's signature, with the path read from the key's tree, is the one computed alone. -/
theorem signLayer_buildTree_eq_recompute (layer : Layer) (idx : Nat) (msg : Digest) :
    (signLayer (pureHash f) pkSeed prf layer idx
        (buildTree (pureHash f) pkSeed prf layer (OtsKey.ofIndex layer idx).tree).run msg).run
      = (Recompute.signLayer (pureHash f) pkSeed prf layer idx msg).run := by
  rw [signLayer_run, Recompute.signLayer, Id.run_bind]
  -- Name the one-time signature, so no tree is evaluated.
  cases (otsSign (pureHash f) pkSeed prf (OtsKey.ofIndex layer idx) msg).run with
  | none => rfl
  | some found =>
    -- The key's path, read from the build, is the path computed alone.
    rw [path_buildTree_run (OtsKey.ofIndex_leaf_lt layer idx)]
    rfl

/-- What the reference signer computes from a public key and `R`, in `Except`. -/
theorem Recompute.signDerived_run {pk : PublicKey} {rho : Randomizer} {m : Message} :
    (Recompute.signDerived (pureHash f) prf pk rho m).run
      = let d := (hMsg (pureHash f) rho pk.pkSeed pk.root m).run
        (Recompute.signLayer (pureHash f) pk.pkSeed prf .bottom (digestIndex d)
            (Recompute.layerMessage (pureHash f) pk.pkSeed prf .bottom (digestIndex d)).run).run
          |>.bind
          fun bottom => (Recompute.signLayer (pureHash f) pk.pkSeed prf .middle (digestIndex d)
            (Recompute.layerMessage (pureHash f) pk.pkSeed prf .middle (digestIndex d)).run).run
          |>.bind
          fun middle => (Recompute.signLayer (pureHash f) pk.pkSeed prf .top (digestIndex d)
            (Recompute.layerMessage (pureHash f) pk.pkSeed prf .top (digestIndex d)).run).run.bind
          fun top => .ok ⟨rho,
            (Recompute.forsSign (pureHash f) pk.pkSeed prf (digestIndex d) (digestLeaves d)).run,
            bottom, middle, top⟩ := by
  rw [Recompute.signDerived]
  simp only [Id.run_bind]
  -- Each layer is either an error, which ends signing, or a value the next layer uses.
  cases (Recompute.signLayer (pureHash f) pk.pkSeed prf .bottom
      (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)
      (Recompute.layerMessage (pureHash f) pk.pkSeed prf .bottom
        (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)).run).run with
  | error err => rfl
  | ok bottom =>
    simp only [Id.run_bind, Id.run_pure, Except.bind]
    cases (Recompute.signLayer (pureHash f) pk.pkSeed prf .middle
        (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)
        (Recompute.layerMessage (pureHash f) pk.pkSeed prf .middle
          (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)).run).run with
    | error err => rfl
    | ok middle =>
      simp only [Id.run_bind, Id.run_pure]
      cases (Recompute.signLayer (pureHash f) pk.pkSeed prf .top
          (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)
          (Recompute.layerMessage (pureHash f) pk.pkSeed prf .top
            (digestIndex (hMsg (pureHash f) rho pk.pkSeed pk.root m).run)).run).run with
      | error err => rfl
      | ok top => rfl

/-- Signing from the built top tree is signing from the public key, each tree built twice.

Both sides give the same result, byte for byte, for every hash in the identity monad. -/
theorem signDerived_eq_recompute (rho : Randomizer) (msg : Message) :
    (signDerived (pureHash f) prf pkSeed (buildTree (pureHash f) pkSeed prf .top 0).run rho
        msg).run
      = (Recompute.signDerived (pureHash f) prf
          ⟨pkSeed, (treeRoot (pureHash f) pkSeed prf .top 0).run⟩ rho msg).run := by
  rw [signDerived_run, Recompute.signDerived_run, value_buildTree_run]
  dsimp only
  generalize hidx : digestIndex (hMsg (pureHash f) rho pkSeed
    (treeRoot (pureHash f) pkSeed prf .top 0).run msg).run = idx
  -- The top key's tree is the one top tree.
  have htop : (buildTree (pureHash f) pkSeed prf .top 0).run
      = (buildTree (pureHash f) pkSeed prf .top (OtsKey.ofIndex .top idx).tree).run := by
    rw [← hidx, OtsKey.ofIndex_top_tree (digestIndex_lt _)]
  rw [htop, forsSign_eq_recompute, value_buildTree_run, value_buildTree_run,
    signLayer_buildTree_eq_recompute, signLayer_buildTree_eq_recompute,
    signLayer_buildTree_eq_recompute]
  rfl

/-- Signing builds each tree once, and signs exactly as the signer that builds each tree twice.

The right side computes each path alone, and builds each tree again for the root above it.

Both sides give the same signature, byte for byte, for every hash in the identity monad. -/
theorem signWith_eq_recompute (sk : SecretKey) (msg : Message) :
    (signWith (pureHash f) sk msg).run = (Recompute.signWith (pureHash f) sk msg).run := by
  rw [signWith_run, signDerived_eq_recompute]
  rfl

end Equal

/-- A signature holds the randomizer, the FORS openings its digest picks, and three layers.

- `pk` is the public key that key generation gives `SK.seed`.
- The randomizer is `R = PRF_msg(SK.prf, PK.seed, M')`.
- Every secret is `PRF(PK.seed, SK.seed, ADRS)`.
- Each layer's key signs what the layer below gives, with its path in its key's tree.
- The bottom key signs the FORS public key, and a higher key the root of the tree below. -/
theorem sign_eq_ok {sk : SecretKey} {pk : PublicKey} {m : Message} {σ : Signature}
    (hpk : (keyGenWith (pureHash f) sk.seed).run.2 = pk)
    (h : (signWith (pureHash f) sk m).run = .ok σ) :
    let secrets := prf (pureHash f) pk.pkSeed sk.seed
    let d := (hMsg (pureHash f) σ.randomizer pk.pkSeed pk.root m).run
    let bottomTree := (buildTree (pureHash f) pk.pkSeed secrets .bottom
      (OtsKey.ofIndex .bottom (digestIndex d)).tree).run
    let middleTree := (buildTree (pureHash f) pk.pkSeed secrets .middle
      (OtsKey.ofIndex .middle (digestIndex d)).tree).run
    let topTree := (buildTree (pureHash f) pk.pkSeed secrets .top
      (OtsKey.ofIndex .top (digestIndex d)).tree).run
    σ.randomizer
        = (prfMsg (pureHash f) (expandKey (pureHash f) sk.seed).run.skPrf pk.pkSeed m).run ∧
      σ.fors = (forsSign (pureHash f) pk.pkSeed secrets (digestIndex d) (digestLeaves d)).run.1 ∧
      (signLayer (pureHash f) pk.pkSeed secrets .bottom (digestIndex d) bottomTree
          (forsKey (pureHash f) pk.pkSeed secrets (digestIndex d)).run).run = .ok σ.bottom ∧
      (signLayer (pureHash f) pk.pkSeed secrets .middle (digestIndex d) middleTree
          bottomTree.value).run = .ok σ.middle ∧
      (signLayer (pureHash f) pk.pkSeed secrets .top (digestIndex d) topTree
          middleTree.value).run = .ok σ.top := by
  subst hpk
  rw [signWith_run, signDerived_run, value_buildTree_run] at h
  -- Peel the three layers off the signer, one bind at a time.
  simp only [Except.bind] at h
  split at h
  · cases h
  rename_i bottom hbottom
  split at h
  · cases h
  rename_i middle hmiddle
  split at h
  · cases h
  rename_i top htop
  -- What is left is the signature itself, under the top tree, tree 0.
  cases h
  dsimp only
  rw [OtsKey.ofIndex_top_tree (digestIndex_lt _), ← forsSign_run_snd]
  exact ⟨rfl, rfl, hbottom, hmiddle, htop⟩

/-- Signing fails only when a one-time key finds no codeword in `2^32` counters.

The error names the layer of that key. -/
theorem sign_error {sk : SecretKey} {m : Message} {e : SphincsError}
    (h : (signWith (pureHash f) sk m).run = .error e) :
    ∃ layer, e = .noAdmissibleEncoding layer := by
  rw [signWith_run, signDerived_run] at h
  simp only [Except.bind] at h
  -- Each layer either fails, with its own error, or passes to the next.
  split at h
  · rename_i e' he
    cases h
    exact ⟨.bottom, (signLayer_error he).1⟩
  split at h
  · rename_i e' he
    cases h
    exact ⟨.middle, (signLayer_error he).1⟩
  split at h
  · rename_i e' he
    cases h
    exact ⟨.top, (signLayer_error he).1⟩
  -- With every layer passing, the result is a signature, not an error.
  · cases h

end EthLib.Cryptography.Sphincs
