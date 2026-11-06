module
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MerkleCache
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.Model
/-!
# Connected signing prefixes under the raw random oracle

Each possible signer outcome comes with intermediate replies and caches that the signer reaches.

The bottom layer may fail before the root, or succeed before the root and top layer run.

Then the cache after the chosen path answers every query of its sibling subtrees.

So the root is the climb from the chosen leaf, with the same value and cache.

Uniform queries are forwarded without being stored in the raw cache.

Source: the leanXMSS specification draft, section "The scheme", paragraph "Signing".

The root reconstruction follows section "Trees".
-/

public section

open OracleComp OracleSpec EthLib.Cryptography
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV
open Xmss.Unforgeability
universe v
variable {m n : Type → Type} [Monad m] [Monad n]
    (F : m →ᵐ n)

-- The ordered collector keeps every callback under a monad homomorphism.
private theorem collect_natural {Y : Type} : ∀ k (f : Fin k → m Y),
    F (Xmss.ofFnInOrder k f) = Xmss.ofFnInOrder k (fun i => F (f i))
  | 0, _ => F.mmap_pure _
  | k+1, f => by
    simp only [Xmss.ofFnInOrder, MonadHom.mmap_bind, MonadHom.mmap_pure,
      collect_natural k]

-- Transport the bounded chain, with the same start and step bounds.
private theorem chain_natural {Y : Type} {length : Nat}
    (step : Fin length → Y → m Y) (start : Nat) : ∀ steps (h : start + steps ≤ length) value,
    F (Wots.chain step start steps h value) =
      Wots.chain (fun i y => F (step i y)) start steps h value
  | 0, _, _ => F.mmap_pure _
  | steps+1, h, value => by
    simp only [Wots.chain, MonadHom.mmap_bind, chain_natural step start steps]

-- The full hash reply is transported before its first half is selected.
private theorem th_natural (H : ByteArray → m (Vector UInt8 32))
    (pp : Xmss.PublicParam) (addr : Xmss.Address) (payload : ByteArray) :
    F (Xmss.th H pp addr payload) = Xmss.th (fun x => F (H x)) pp addr payload := by
  simp only [Xmss.th, MonadHom.mmap_bind, MonadHom.mmap_pure]

-- Both halves of each full seed-hash word remain available to the leaf program.
private theorem leaf_natural (H : ByteArray → m (Vector UInt8 32))
    (pp : Xmss.PublicParam) (seed : Xmss.Seed) (layer : Xmss.Layer) (key : UInt32) :
    F (Xmss.otsPublicLeaf H pp seed layer key) =
      Xmss.otsPublicLeaf (fun x => F (H x)) pp seed layer key := by
  simp only [Xmss.otsPublicLeaf, Xmss.chainStarts, MonadHom.mmap_bind,
    MonadHom.mmap_pure, collect_natural, Xmss.chain, chain_natural,
    Xmss.chainStep, Xmss.otsLeafHash, th_natural]
  rfl

-- Only the hash callback changes; the actual node address and child order remain.
private theorem nodeHash_natural (H : ByteArray → m (Vector UInt8 32))
    (pp : Xmss.PublicParam) (layer : Xmss.Layer) (level idx : Nat)
    (left right : Xmss.Digest) :
    F (Xmss.nodeHash H pp layer level idx left right) =
      Xmss.nodeHash (fun x => F (H x)) pp layer level idx left right :=
  th_natural F H pp _ _

-- Use the tree transport instead of a new traversal.
private theorem node_natural (H : ByteArray → m (Vector UInt8 32))
    (pp : Xmss.PublicParam) (seed : Xmss.Seed) (layer : Xmss.Layer) (h idx : Nat) :
    F (Xmss.node H pp seed layer h idx) =
      Xmss.node (fun x => F (H x)) pp seed layer h idx := by
  unfold Xmss.node
  rw [Merkle.node_map _ (fun {Y} (x : m Y) => F x) (fun x f => F.mmap_bind x f)]
  simp only [nodeHash_natural, Xmss.leaves, leaf_natural]
  rfl

-- Use the path transport with the same global index.
private theorem path_natural (H : ByteArray → m (Vector UInt8 32))
    (pp : Xmss.PublicParam) (seed : Xmss.Seed) (layer : Xmss.Layer) (idx : Nat) :
    F (Xmss.path H pp seed layer idx) =
      Xmss.path (fun x => F (H x)) pp seed layer idx := by
  unfold Xmss.path
  rw [Merkle.path_map _ (fun {Y} (x : m Y) => F x)
    (fun x => F.mmap_pure x) (fun x f => F.mmap_bind x f)]
  simp only [nodeHash_natural, Xmss.leaves, leaf_natural]
  rfl

-- The climb transports with its leaf-to-root order.
private theorem fold_natural (H : ByteArray → m (Vector UInt8 32))
    (pp : Xmss.PublicParam) (layer : Xmss.Layer) (idx : Nat) (leaf : Xmss.Digest)
    (pi : Vector Xmss.Digest Xmss.Constants.LAYER_HEIGHT) :
    F (Xmss.fold H pp layer idx leaf pi) =
      Xmss.fold (fun x => F (H x)) pp layer idx leaf pi := by
  unfold Xmss.fold
  rw [Merkle.climb_map_monad _ (fun {Y} (x : m Y) => F x)
    (fun x => F.mmap_pure x) (fun x f => F.mmap_bind x f)]
  simp only [nodeHash_natural]

open Xmss.Unforgeability
-- The raw query inclusion is exactly the model hash, retaining all 32 reply bytes.
private theorem raw_callback_world :
    (fun input : ByteArray =>
      (simulateQ' (QueryImpl.ofLift HashSig.HashSpec (OracleComp VCV.World)))
      (HashSig.ofOutput <$> HashSig.HashSpec.query input.data.toList)) = VCV.H := by
  funext input
  simp only [simulateQ_map, simulateQ_spec_query, QueryImpl.ofLift_apply, VCV.H]

-- The actual leaf uses only the raw summand of the world.
private theorem world_leaf (pp : Xmss.PublicParam) (seed : Xmss.Seed)
    (layer : Xmss.Layer) (key : UInt32) :
    simulateQ (QueryImpl.ofLift HashSig.HashSpec (OracleComp VCV.World))
      (Xmss.otsPublicLeaf (fun input => HashSig.ofOutput <$>
        HashSig.HashSpec.query input.data.toList) pp seed layer key) =
      Xmss.otsPublicLeaf VCV.H pp seed layer key := by
  have h := leaf_natural
    (simulateQ' (QueryImpl.ofLift HashSig.HashSpec (OracleComp VCV.World)))
    (fun input => HashSig.ofOutput <$> HashSig.HashSpec.query input.data.toList)
    pp seed layer key
  simpa only [simulateQ'_apply, raw_callback_world] using h

-- The actual path uses the same raw inclusion as its leaves and nodes.
private theorem world_path (pp : Xmss.PublicParam) (seed : Xmss.Seed)
    (layer : Xmss.Layer) (key : Nat) :
    simulateQ (QueryImpl.ofLift HashSig.HashSpec (OracleComp VCV.World))
      (Xmss.path (fun input => HashSig.ofOutput <$>
        HashSig.HashSpec.query input.data.toList) pp seed layer key) =
      Xmss.path VCV.H pp seed layer key := by
  have h := path_natural
    (simulateQ' (QueryImpl.ofLift HashSig.HashSpec (OracleComp VCV.World)))
    (fun input => HashSig.ofOutput <$> HashSig.HashSpec.query input.data.toList)
    pp seed layer key
  simpa only [simulateQ'_apply, raw_callback_world] using h

-- Uniform forwarding remains uncached; only raw queries reach the caching handler.
private theorem raw_world_sim {Y : Type} (oa : OracleComp HashSig.HashSpec Y) :
    simulateQ HashSig.HashSpec.romImpl
      (simulateQ (QueryImpl.ofLift HashSig.HashSpec (OracleComp VCV.World)) oa) =
    simulateQ HashSig.HashSpec.randomOracle oa := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro t
  change simulateQ (unifFwdImpl HashSig.HashSpec + HashSig.HashSpec.randomOracle)
    (liftM (HashSig.HashSpec.query t)) = _
  exact QueryImpl.simulateQ_add_liftM_query_right _ _ t

-- The actual full-root program is the inclusion of the same raw program.
private theorem world_node (pp : Xmss.PublicParam) (seed : Xmss.Seed)
    (layer : Xmss.Layer) (h key : Nat) :
    simulateQ (QueryImpl.ofLift HashSig.HashSpec (OracleComp VCV.World))
      (Xmss.node (fun input => HashSig.ofOutput <$>
        HashSig.HashSpec.query input.data.toList) pp seed layer h key) =
      Xmss.node VCV.H pp seed layer h key := by
  have hn := node_natural
    (simulateQ' (QueryImpl.ofLift HashSig.HashSpec (OracleComp VCV.World)))
    (fun input => HashSig.ofOutput <$> HashSig.HashSpec.query input.data.toList)
    pp seed layer h key
  simpa only [simulateQ'_apply, raw_callback_world] using hn

-- The selected leaf and fold use that same inclusion, in order.
private theorem world_spine (pp : Xmss.PublicParam) (seed : Xmss.Seed)
    (layer : Xmss.Layer) (key : Nat) (pi : Vector Xmss.Digest Xmss.Constants.LAYER_HEIGHT) :
    simulateQ (QueryImpl.ofLift HashSig.HashSpec (OracleComp VCV.World)) (do
      let leaf ← Xmss.leaves (fun input => HashSig.ofOutput <$>
        HashSig.HashSpec.query input.data.toList) pp seed layer key
      Xmss.fold (fun input => HashSig.ofOutput <$>
        HashSig.HashSpec.query input.data.toList) pp layer key leaf pi) = (do
      let leaf ← Xmss.leaves VCV.H pp seed layer key
      Xmss.fold VCV.H pp layer key leaf pi) := by
  rw [simulateQ_bind]
  simp only [Xmss.leaves, world_leaf]
  congr 1
  funext leaf
  have hf := fold_natural
    (simulateQ' (QueryImpl.ofLift HashSig.HashSpec (OracleComp VCV.World)))
    (fun input => HashSig.ofOutput <$> HashSig.HashSpec.query input.data.toList)
    pp layer key leaf pi
  simpa only [simulateQ'_apply, raw_callback_world] using hf

-- Settlement comes from this supported path endpoint, not from an independent completion.
private theorem actual_world_root_joint (pp : Xmss.PublicParam) (seed : Xmss.Seed)
    (layer : Xmss.Layer) (key : Nat) (initial known live : HashSig.HashSpec.QueryCache)
    (hle : known ≤ live) (pi : Vector Xmss.Digest Xmss.Constants.LAYER_HEIGHT)
    (hp : (pi, known) ∈ support ((simulateQ HashSig.HashSpec.romImpl
      (Xmss.path VCV.H pp seed layer key)).run initial)) :
    (simulateQ HashSig.HashSpec.romImpl
      (Xmss.node VCV.H pp seed layer Xmss.Constants.LAYER_HEIGHT
        (key / 2 ^ Xmss.Constants.LAYER_HEIGHT))).run live =
    (simulateQ HashSig.HashSpec.romImpl (do
      let leaf ← Xmss.leaves VCV.H pp seed layer key
      Xmss.fold VCV.H pp layer key leaf pi)).run live := by
  rw [← world_path, raw_world_sim] at hp
  have settled := QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching
    (uniformSampleImpl (spec := HashSig.HashSpec)) _ hp
  have joint := VCV.run_node_eq_run_selected_fold_of_path_settled
    (uniformSampleImpl (spec := HashSig.HashSpec))
    (fun input => HashSig.ofOutput <$> HashSig.HashSpec.query input.data.toList)
    pp seed layer key hle pi settled
  rw [← world_node, ← world_spine, raw_world_sim, raw_world_sim]
  exact joint

-- A successful layer contains the actual OTS reply followed by the actual path run.
private theorem layer_ok_path_state_support {ι : Type} {spec : OracleSpec ι} {σ : Type}
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    (impl : QueryImpl spec (StateT σ m)) (H : ByteArray → OracleComp spec (Vector UInt8 32))
    (pp : Xmss.PublicParam) (seed : Xmss.Seed) (layer : Xmss.Layer)
    (key : Nat) (msg : ByteArray) (initial final : σ) (sig : Xmss.LayerSignature)
    (hz : (.ok sig, final) ∈ support ((simulateQ impl
      (Xmss.signLayer H pp seed layer key msg)).run initial)) :
    ∃ afterOTS,
      (some (sig.randomizer, sig.chainValues), afterOTS) ∈ support
        ((simulateQ impl (Xmss.otsSign H pp seed layer (UInt32.ofNat key) msg)).run initial) ∧
      (sig.path, final) ∈ support
        ((simulateQ impl (Xmss.path H pp seed layer key)).run afterOTS) := by
  rw [Xmss.signLayer, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨result, afterOTS⟩, hOTS, hrest⟩ := hz
  cases result with
  | none => simp at hrest
  | some result =>
    rcases result with ⟨rho, values⟩
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
    obtain ⟨⟨path, afterPath⟩, hpath, hend⟩ := hrest
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hend
    cases hend
    exact ⟨afterOTS, hOTS, hpath⟩

-- A normal layer error comes from None at the exact same OTS endpoint.
private theorem layer_error_state_support {ι : Type} {spec : OracleSpec ι} {σ : Type}
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    (impl : QueryImpl spec (StateT σ m)) (H : ByteArray → OracleComp spec (Vector UInt8 32))
    (pp : Xmss.PublicParam) (seed : Xmss.Seed) (layer : Xmss.Layer) (key : Nat)
    (msg : ByteArray) (initial final : σ) (err : Xmss.XmssError)
    (hz : (.error err, final) ∈ support ((simulateQ impl
      (Xmss.signLayer H pp seed layer key msg)).run initial)) :
    err = .noAdmissibleEncoding layer key ∧
      (none, final) ∈ support ((simulateQ impl
        (Xmss.otsSign H pp seed layer (UInt32.ofNat key) msg)).run initial) := by
  rw [Xmss.signLayer, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨result, afterOTS⟩, hOTS, hrest⟩ := hz
  cases result with
  | none =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
    cases hrest
    exact ⟨rfl, hOTS⟩
  | some result =>
    rcases result with ⟨rho, values⟩
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
    obtain ⟨⟨path, afterPath⟩, _, hend⟩ := hrest
    simp at hend

-- Keep finite support assembly abstract so it does not normalize a concrete height-16 tree.
private theorem connected_support_of_root_joint
    {ι : Type} {spec : OracleSpec ι} {σ : Type}
    {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
    (impl : QueryImpl spec (StateT σ m)) (H : ByteArray → OracleComp spec (Vector UInt8 32))
    (pp : Xmss.PublicParam) (seed : Xmss.Seed) (idx : Xmss.LeafIndex) (msg : Xmss.Message)
    (initial : σ)
    (z : Except Xmss.XmssError Xmss.Signature × σ)
    (hz : z ∈ support ((simulateQ impl
      (Xmss.signDerived H seed pp idx msg)).run initial))
    (jointAfterPath : ∀ (afterOTS beforeRoot : σ)
      (pi : Vector Xmss.Digest Xmss.Constants.LAYER_HEIGHT),
      (pi, beforeRoot) ∈ support ((simulateQ impl
        (Xmss.path H pp seed .bottom idx.toNat)).run afterOTS) →
      (simulateQ impl (Xmss.node H pp seed .bottom Xmss.Constants.LAYER_HEIGHT
        (Xmss.bottomTree idx))).run beforeRoot =
      (simulateQ impl (do
        let y ← Xmss.leaves H pp seed .bottom idx.toNat
        Xmss.fold H pp .bottom idx.toNat y pi)).run beforeRoot) :
    (z.1 = .error (.noAdmissibleEncoding .bottom idx.toNat) ∧
      (none, z.2) ∈ support ((simulateQ impl
        (Xmss.otsSign H pp seed .bottom (UInt32.ofNat idx.toNat)
          (Xmss.packBytes msg))).run initial)) ∨
    (∃ bottom afterOTS beforeRoot root afterRoot top,
      (.ok bottom, beforeRoot) ∈ support ((simulateQ impl
        (Xmss.signLayer H pp seed .bottom idx.toNat (Xmss.packBytes msg))).run initial) ∧
      (some (bottom.randomizer, bottom.chainValues), afterOTS) ∈ support
        ((simulateQ impl (Xmss.otsSign H pp seed .bottom
          (UInt32.ofNat idx.toNat) (Xmss.packBytes msg))).run initial) ∧
      (bottom.path, beforeRoot) ∈ support ((simulateQ impl
        (Xmss.path H pp seed .bottom idx.toNat)).run afterOTS) ∧
      (root, afterRoot) ∈ support ((simulateQ impl
        (Xmss.node H pp seed .bottom Xmss.Constants.LAYER_HEIGHT
          (Xmss.bottomTree idx))).run beforeRoot) ∧
      (top, z.2) ∈ support ((simulateQ impl
        (Xmss.signLayer H pp seed .top (Xmss.bottomTree idx)
          (Xmss.packBytes root))).run afterRoot) ∧
      z.1 = top.map (fun t => { leafIndex := idx, bottom, top := t }) ∧
      (simulateQ impl
        (Xmss.node H pp seed .bottom Xmss.Constants.LAYER_HEIGHT
          (Xmss.bottomTree idx))).run beforeRoot =
        (simulateQ impl (do
          let selected ← Xmss.leaves H pp seed .bottom idx.toNat
          Xmss.fold H pp .bottom idx.toNat selected bottom.path)).run beforeRoot ∧
      (∀ err, top = .error err →
        err = .noAdmissibleEncoding .top (Xmss.bottomTree idx) ∧
        VCV.readback z.1 = none ∧
        (none, z.2) ∈ support ((simulateQ impl
          (Xmss.otsSign H pp seed .top (UInt32.ofNat (Xmss.bottomTree idx))
            (Xmss.packBytes root))).run afterRoot))) := by
  -- These are the signer's three sequential calls, including its early return.
  rw [Xmss.signDerived, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨bottomReply, beforeRoot⟩, hbottom, hrest⟩ := hz
  cases bottomReply with
  | error err =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
    cases hrest
    obtain ⟨herr, hnone⟩ := layer_error_state_support impl H
      pp seed .bottom idx.toNat (Xmss.packBytes msg) initial beforeRoot err hbottom
    subst err
    exact Or.inl ⟨rfl, hnone⟩
  | ok bottom =>
    simp only [pure_bind] at hrest
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
    obtain ⟨⟨root, afterRoot⟩, hroot, htopBind⟩ := hrest
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at htopBind
    obtain ⟨⟨topReply, afterTop⟩, htop, hend⟩ := htopBind
    -- The normal reply map preserves the exact final cache in both top-layer branches.
    have hfinal : z = (topReply.map (fun t =>
        { leafIndex := idx, bottom, top := t }), afterTop) := by
      cases topReply <;>
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Except.map] using hend
    cases hfinal
    obtain ⟨afterOTS, hOTS, hpath⟩ := layer_ok_path_state_support impl H
      pp seed .bottom idx.toNat (Xmss.packBytes msg) initial beforeRoot bottom hbottom
    have joint := jointAfterPath afterOTS beforeRoot bottom.path hpath
    refine Or.inr ⟨bottom, afterOTS, beforeRoot, root, afterRoot, topReply, ?_⟩
    refine ⟨hbottom, hOTS, hpath, ?_⟩
    -- Restrict elaboration to the named endpoint fact rather than unfolding the tree.
    with_reducible refine ⟨hroot, htop, rfl, joint, ?_⟩
    intro err he
    have herror : (.error err, afterTop) ∈ support ((simulateQ impl
        (Xmss.signLayer H pp seed .top (Xmss.bottomTree idx)
          (Xmss.packBytes root))).run afterRoot) := by
      simpa only [he] using htop
    obtain ⟨herr, hnone⟩ := layer_error_state_support impl H
      pp seed .top (Xmss.bottomTree idx) (Xmss.packBytes root) afterRoot afterTop err herror
    refine ⟨herr, ?_, hnone⟩
    rw [he]
    rfl

/-- A supported signer run keeps its connected layer, path and root endpoints.

A bottom failure is the actual one-time signer returning `none`, with the same final raw cache.

Otherwise the chosen bottom path settles the sibling programs before the full root runs.

The root can then be reconstructed with the same value and full raw cache.

A normal top failure still has that prefix and exposes no signature through `readback`.

This is a support statement, not an equality of whole signer programs or their query costs.
-/
theorem actual_signDerived_support_cases
    (pp : Xmss.PublicParam) (seed : Xmss.Seed) (idx : Xmss.LeafIndex) (msg : Xmss.Message)
    (initial : HashSig.HashSpec.QueryCache)
    (z : Except Xmss.XmssError Xmss.Signature × HashSig.HashSpec.QueryCache)
    (hz : z ∈ support ((simulateQ HashSig.HashSpec.romImpl
      (Xmss.signDerived VCV.H seed pp idx msg)).run initial)) :
    (z.1 = .error (.noAdmissibleEncoding .bottom idx.toNat) ∧
      (none, z.2) ∈ support ((simulateQ HashSig.HashSpec.romImpl
        (Xmss.otsSign VCV.H pp seed .bottom (UInt32.ofNat idx.toNat)
          (Xmss.packBytes msg))).run initial)) ∨
    (∃ bottom afterOTS beforeRoot root afterRoot top,
      (.ok bottom, beforeRoot) ∈ support ((simulateQ HashSig.HashSpec.romImpl
        (Xmss.signLayer VCV.H pp seed .bottom idx.toNat (Xmss.packBytes msg))).run initial) ∧
      (some (bottom.randomizer, bottom.chainValues), afterOTS) ∈ support
        ((simulateQ HashSig.HashSpec.romImpl (Xmss.otsSign VCV.H pp seed .bottom
          (UInt32.ofNat idx.toNat) (Xmss.packBytes msg))).run initial) ∧
      (bottom.path, beforeRoot) ∈ support ((simulateQ HashSig.HashSpec.romImpl
        (Xmss.path VCV.H pp seed .bottom idx.toNat)).run afterOTS) ∧
      (root, afterRoot) ∈ support ((simulateQ HashSig.HashSpec.romImpl
        (Xmss.node VCV.H pp seed .bottom Xmss.Constants.LAYER_HEIGHT
          (Xmss.bottomTree idx))).run beforeRoot) ∧
      (top, z.2) ∈ support ((simulateQ HashSig.HashSpec.romImpl
        (Xmss.signLayer VCV.H pp seed .top (Xmss.bottomTree idx)
          (Xmss.packBytes root))).run afterRoot) ∧
      z.1 = top.map (fun t => { leafIndex := idx, bottom, top := t }) ∧
      (simulateQ HashSig.HashSpec.romImpl
        (Xmss.node VCV.H pp seed .bottom Xmss.Constants.LAYER_HEIGHT
          (Xmss.bottomTree idx))).run beforeRoot =
        (simulateQ HashSig.HashSpec.romImpl (do
          let selected ← Xmss.leaves VCV.H pp seed .bottom idx.toNat
          Xmss.fold VCV.H pp .bottom idx.toNat selected bottom.path)).run beforeRoot ∧
      (∀ err, top = .error err →
        err = .noAdmissibleEncoding .top (Xmss.bottomTree idx) ∧
        VCV.readback z.1 = none ∧
        (none, z.2) ∈ support ((simulateQ HashSig.HashSpec.romImpl
          (Xmss.otsSign VCV.H pp seed .top (UInt32.ofNat (Xmss.bottomTree idx))
            (Xmss.packBytes root))).run afterRoot))) := by
  exact connected_support_of_root_joint HashSig.HashSpec.romImpl VCV.H pp seed idx msg initial z hz
    (fun afterOTS beforeRoot pi => actual_world_root_joint pp seed .bottom idx.toNat
      afterOTS beforeRoot beforeRoot le_rfl pi)

end EthLib.Cryptography.Xmss.Unforgeability.VCV
