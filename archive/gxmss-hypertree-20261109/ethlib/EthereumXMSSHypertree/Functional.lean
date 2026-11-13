/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthLib.Cryptography.Xmss.Sign
public import EthLib.Cryptography.Proofs.HashSig

/-!
# Deterministic evaluation of the source algorithms

The pure functions evaluate the selected source's chain, tree and signing operations under one
fixed deterministic hash. Signing failure is observed with `Except.toOption`. These equations
compare returned values; they do not assert equality of oracle call traces.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography
open Xmss Xmss.Constants

namespace Pure

/-- A full deterministic source response. -/
abbrev Hash := ByteArray → Vector UInt8 32

/-- A deterministic source derivation, retaining all 32 response bytes. -/
abbrev Derivation := PublicParam → Address → ByteArray → Vector UInt8 32

/-- Lift deterministic derivations into the source's identity monad. -/
@[expose] def derivation (prf : Derivation) : SeedPrf Id :=
  fun pp address suffix => pure (prf pp address suffix)

/-- The source's first-half addressed hash. -/
@[expose] def addressed (H : Hash) (pp : PublicParam) (address : Address)
    (payload : ByteArray) : Digest :=
  halfOf 0 (H (thInput pp address payload))

/-- The exact source step, including the chain index after its value. -/
@[expose] def step (H : Hash) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) (value : Digest) : Digest :=
  addressed H pp (addrChain layer e mu)
    (packBytes value ++ packBytes (uintToBytes 16 i.val))

/-- Evaluate the source chain at its actual source step positions. -/
@[expose] def chain (H : Hash) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (i : Fin V) (start : Nat) :
    (steps : Nat) → start + steps < CHAIN_LENGTH → Digest → Digest
  | 0, _, value => value
  | steps + 1, h, value =>
    step H pp layer e i ⟨start + steps, by omega⟩
      (chain H pp layer e i start steps (by omega) value)

/-- Decode all 58 starts from 29 ordered, full derivation responses. -/
@[expose] def starts (pp : PublicParam) (prf : Derivation) (layer : Layer) (e : UInt32) :
    Vector Digest V :=
  Vector.ofFn fun i =>
    halfOf ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
      (prf pp (addrPrf layer e ⟨i.val / 2, by have := i.isLt; simp only [V] at *; omega⟩)
        .empty)

/-- Hash the ordered source chain endpoints into its leaf. -/
@[expose] def leafHash (H : Hash) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (ends : Vector Digest V) : Digest :=
  addressed H pp (addrLeaf layer e) (packDigests ends)

/-- Evaluate one source public leaf from all its chain starts. -/
@[expose] def publicLeaf (H : Hash) (pp : PublicParam) (prf : Derivation)
    (layer : Layer) (e : UInt32) : Digest :=
  leafHash H pp layer e (Vector.ofFn fun i =>
    chain H pp layer e i 0 (CHAIN_LENGTH - 1) (by decide) (starts pp prf layer e)[i])

/-- Evaluate the source ordered node input, retaining its total address conversion. -/
@[expose] def nodeHash (H : Hash) (pp : PublicParam) (layer : Layer) (level j : Nat)
    (left right : Digest) : Digest :=
  addressed H pp (addrNode layer (Fin.ofNat _ level) (UInt32.ofNat j))
    (packBytes left ++ packBytes right)

/-- Evaluate a concrete source node by its left subtree, right subtree and parent hash. -/
@[expose] def node (H : Hash) (pp : PublicParam) (prf : Derivation) (layer : Layer) :
    (level j : Nat) → Digest
  | 0, j => publicLeaf H pp prf layer (UInt32.ofNat j)
  | level + 1, j => nodeHash H pp layer (level + 1) j
      (node H pp prf layer level (2 * j)) (node H pp prf layer level (2 * j + 1))

/-- Evaluate the concrete source sibling list from the current node upward. -/
@[expose] def siblings (H : Hash) (pp : PublicParam) (prf : Derivation) (layer : Layer) :
    (level j n : Nat) → Vector Digest n
  | _, _, 0 => #v[]
  | level, j, n + 1 =>
    (#v[node H pp prf layer level (j ^^^ 1)] ++
      siblings H pp prf layer (level + 1) (j / 2) n).cast (Nat.add_comm 1 n)

/-- The source path is leaf-first and has exactly sixteen siblings. -/
@[expose] def path (H : Hash) (pp : PublicParam) (prf : Derivation) (layer : Layer)
    (e : Nat) : Vector Digest LAYER_HEIGHT :=
  siblings H pp prf layer 0 e LAYER_HEIGHT

/-- Climb a source path with the current-index parity controlling child order. -/
@[expose] def climb (H : Hash) (pp : PublicParam) (layer : Layer) :
    (level j : Nat) → Digest → List Digest → Digest
  | _, _, current, [] => current
  | level, j, current, sibling :: rest =>
    let children := Merkle.ordered j current sibling
    climb H pp layer (level + 1) (j / 2)
      (nodeHash H pp layer (level + 1) (j / 2) children.1 children.2) rest

end Pure

/-- Identity evaluation of the source addressed hash preserves its exact byte input. -/
theorem th_run (H : Pure.Hash) (pp : PublicParam) (address : Address) (payload : ByteArray) :
    (th (pureHash H) pp address payload).run = Pure.addressed H pp address payload := rfl

/-- Identity evaluation of the source chain equals the pure chain at every legal length. -/
theorem chain_run (H : Pure.Hash) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (i : Fin V) (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    (Xmss.chain (pureHash H) pp layer e i start steps h value).run =
      Pure.chain H pp layer e i start steps h value := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [Xmss.chain, Wots.chain, Id.run_bind, chainStep, th, pureHash,
      Id.run_pure, Pure.chain, Pure.step, Pure.addressed]
    simp only [Xmss.chain] at ih
    rw [ih]

/-- The source starts retain both halves of each full derivation in chain order. -/
theorem chainStarts_run (pp : PublicParam) (prf : Pure.Derivation) (layer : Layer)
    (e : UInt32) :
    (chainStarts pp (Pure.derivation prf) layer e).run = Pure.starts pp prf layer e := by
  simp [chainStarts, Pure.starts, Pure.derivation, HashSig.ofFnInOrder_run]

/-- The pure source leaf hashes the same ordered endpoint vector. -/
theorem otsPublicLeaf_run (H : Pure.Hash) (pp : PublicParam) (prf : Pure.Derivation)
    (layer : Layer) (e : UInt32) :
    (otsPublicLeaf (pureHash H) pp (Pure.derivation prf) layer e).run =
      Pure.publicLeaf H pp prf layer e := by
  simp [otsPublicLeaf, chainStarts_run, HashSig.ofFnInOrder_run, chain_run,
    otsLeafHash, th_run, Pure.publicLeaf, Pure.leafHash]

/-- The pure source node equals the identity-monad source at every height. -/
theorem node_run (H : Pure.Hash) (pp : PublicParam) (prf : Pure.Derivation)
    (layer : Layer) (level j : Nat) :
    (node (pureHash H) pp (Pure.derivation prf) layer level j).run =
      Pure.node H pp prf layer level j := by
  induction level generalizing j with
  | zero => exact otsPublicLeaf_run H pp prf layer (UInt32.ofNat j)
  | succ level ih =>
    simp only [node, Merkle.node, Id.run_bind, nodeHash, th, pureHash, Id.run_pure,
      Pure.node, Pure.nodeHash, Pure.addressed]
    simp only [node] at ih
    rw [ih, ih]

/-- The pure source sibling list preserves the source's leaf-first order. -/
theorem siblings_run (H : Pure.Hash) (pp : PublicParam) (prf : Pure.Derivation)
    (layer : Layer) (level j n : Nat) :
    (Merkle.siblings (nodeHash (pureHash H) pp layer)
      (leaves (pureHash H) pp (Pure.derivation prf) layer) level j n).run =
        Pure.siblings H pp prf layer level j n := by
  induction n generalizing level j with
  | zero => rfl
  | succ n ih =>
    simp only [Merkle.siblings, Id.run_bind, Id.run_pure, Pure.siblings]
    rw [show (Merkle.node (nodeHash (pureHash H) pp layer)
      (leaves (pureHash H) pp (Pure.derivation prf) layer) level (j ^^^ 1)).run =
        Pure.node H pp prf layer level (j ^^^ 1) from node_run H pp prf layer level (j ^^^ 1)]
    rw [ih]

/-- Identity evaluation of the full source path equals the pure sibling vector. -/
theorem path_run (H : Pure.Hash) (pp : PublicParam) (prf : Pure.Derivation)
    (layer : Layer) (e : Nat) :
    (path (pureHash H) pp (Pure.derivation prf) layer e).run = Pure.path H pp prf layer e :=
  siblings_run H pp prf layer 0 e LAYER_HEIGHT

/-- Identity evaluation of the source climb preserves left/right orientation. -/
theorem climb_run (H : Pure.Hash) (pp : PublicParam) (layer : Layer)
    (level j : Nat) (current : Digest) (siblings : List Digest) :
    (Merkle.climb (nodeHash (pureHash H) pp layer) level j current siblings).run =
      Pure.climb H pp layer level j current siblings := by
  induction siblings generalizing level j current with
  | nil => rfl
  | cons sibling rest ih =>
    simp [Merkle.climb, Pure.climb, nodeHash, th_run, Pure.nodeHash, ih]

namespace Pure

/-- Hash the source message fibre together with its explicit randomizer. -/
@[expose] def messageHash (H : Hash) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (rho : Randomizer) : Digest :=
  addressed H pp (addrMsg layer e) (msg ++ packBytes rho)

/-- One full response supplies the source randomizer base. -/
@[expose] def randomizerBase (pp : PublicParam) (prf : Derivation) (layer : Layer)
    (e : UInt32) (msg : ByteArray) : Randomizer :=
  halfOf 0 (prf pp (addrRnd layer e) msg)

/-- The actual source counter search, evaluated under the fixed deterministic hash. -/
@[expose] def search (H : Hash) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) : Option (Randomizer × Vector (Fin CHAIN_LENGTH) V) :=
  (Internal.findCodeword (pureHash H) pp layer e msg base 0 MAX_RANDOMIZER_TRIALS).run

/-- The pure source OTS signer retains exhaustion and the successful randomizer. -/
@[expose] def otsSign (H : Hash) (pp : PublicParam) (prf : Derivation) (layer : Layer)
    (e : UInt32) (msg : ByteArray) : Option (Randomizer × Vector Digest V) :=
  match search H pp layer e msg (randomizerBase pp prf layer e msg) with
  | none => none
  | some (rho, x) => some (rho, Vector.ofFn fun i =>
      chain H pp layer e i 0 x[i] (by simp) (starts pp prf layer e)[i])

/-- The pure source OTS recovery rejects an inadmissible digest before walking chains. -/
@[expose] def otsLeaf (H : Hash) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (rho : Randomizer) (y : Vector Digest V) : Option Digest :=
  match codeword? (messageHash H pp layer e msg rho) with
  | none => none
  | some x => some (leafHash H pp layer e (Vector.ofFn fun i =>
      chain H pp layer e i x[i] (CHAIN_LENGTH - 1 - x[i])
        (by have := x[i].isLt; omega) y[i]))

/-- The pure source layer signer preserves its explicit error and path order. -/
@[expose] def signLayer (H : Hash) (pp : PublicParam) (prf : Derivation) (layer : Layer)
    (e : Nat) (msg : ByteArray) : Except XmssError LayerSignature :=
  match otsSign H pp prf layer (UInt32.ofNat e) msg with
  | none => .error (.noAdmissibleEncoding layer e)
  | some (rho, y) => .ok ⟨rho, y, path H pp prf layer e⟩

/-- The pure source layer recovery retains the complete optional-root observation. -/
@[expose] def layerRoot (H : Hash) (pp : PublicParam) (layer : Layer) (e : Nat)
    (msg : ByteArray) (sig : LayerSignature) : Option Digest :=
  match otsLeaf H pp layer (UInt32.ofNat e) msg sig.randomizer sig.chainValues with
  | none => none
  | some leaf => some (climb H pp layer 0 e leaf sig.path.toList)

/-- The source bottom failure precedes every computation needed only for the top layer. -/
@[expose] def signDerived (H : Hash) (prf : Derivation) (pp : PublicParam)
    (idx : LeafIndex) (msg : Message) : Except XmssError Signature :=
  match signLayer H pp prf .bottom idx.toNat (packBytes msg) with
  | .error err => .error err
  | .ok bottom =>
    let bottomRoot := node H pp prf .bottom LAYER_HEIGHT (bottomTree idx)
    match signLayer H pp prf .top (bottomTree idx) (packBytes bottomRoot) with
    | .error err => .error err
    | .ok top => .ok ⟨idx, bottom, top⟩

/-- The source verifier recovers the bottom root before the top certificate's message. -/
@[expose] def verify (H : Hash) (pk : PublicKey) (msg : Message) (sig : Signature) : Bool :=
  match layerRoot H pk.publicParam .bottom sig.leafIndex.toNat (packBytes msg) sig.bottom with
  | none => false
  | some bottomRoot =>
    match layerRoot H pk.publicParam .top (bottomTree sig.leafIndex) (packBytes bottomRoot) sig.top with
    | none => false
    | some root => decide (root = pk.root)

/-- The source raw seed derives its scheme seed through the exact tag and bytes. -/
@[expose] def schemeSeed (H : Hash) (rawSeed : Seed) : Seed :=
  H (ByteArray.mk SEED_TAG.toArray ++ packBytes rawSeed)

/-- Full responses keyed by the derived seed, without any distributional assertion about it. -/
@[expose] def derivedResponse (H : Hash) (seed : Seed) : Derivation :=
  fun pp address suffix => H (thInput pp address (packBytes seed ++ suffix))

/-- The public parameter is the first half of the distinguished full response. -/
@[expose] def publicParam (prf : Derivation) : PublicParam :=
  halfOf 0 (prf (Vector.replicate PUBLIC_PARAM_LEN 0) addrParam .empty)

/-- Pure source key generation retains raw S0 in the secret key. -/
@[expose] def keys (H : Hash) (rawSeed : Seed) : SecretKey × PublicKey :=
  let prf := derivedResponse H (schemeSeed H rawSeed)
  let pp := publicParam prf
  (⟨rawSeed⟩, ⟨node H pp prf .top LAYER_HEIGHT 0, pp⟩)

/-- The selected returned-failure observation of complete source signing. -/
@[expose] def sign (H : Hash) (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    Option Signature :=
  let prf := derivedResponse H (schemeSeed H sk.seed)
  (signDerived H prf (publicParam prf) idx msg).toOption

end Pure

/-- Identity evaluation of the randomizer base retains the selected full response's first half. -/
theorem randomizerBase_run (pp : PublicParam) (prf : Pure.Derivation) (layer : Layer)
    (e : UInt32) (msg : ByteArray) :
    (randomizerBase pp (Pure.derivation prf) layer e msg).run =
      Pure.randomizerBase pp prf layer e msg := rfl

/-- The pure source OTS signer agrees on success and exhaustion. -/
theorem otsSign_run (H : Pure.Hash) (pp : PublicParam) (prf : Pure.Derivation)
    (layer : Layer) (e : UInt32) (msg : ByteArray) :
    (otsSign (pureHash H) pp (Pure.derivation prf) layer e msg).run =
      Pure.otsSign H pp prf layer e msg := by
  rw [otsSign, Id.run_bind, randomizerBase_run, Id.run_bind, Pure.otsSign]
  simp only [Pure.search]
  generalize (Internal.findCodeword (pureHash H) pp layer e msg
    (Pure.randomizerBase pp prf layer e msg) 0 MAX_RANDOMIZER_TRIALS).run = result
  cases result with
  | none => rfl
  | some pair =>
    rcases pair with ⟨rho, x⟩
    simp only [Id.run_bind, Id.run_pure, chainStarts_run, HashSig.ofFnInOrder_run, chain_run]

/-- The pure source OTS recovery agrees for every claimed signature, including rejection. -/
theorem otsLeaf_run (H : Pure.Hash) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (rho : Randomizer) (y : Vector Digest V) :
    (otsLeaf (pureHash H) pp layer e msg rho y).run = Pure.otsLeaf H pp layer e msg rho y := by
  rw [otsLeaf, Id.run_bind]
  rw [show (messageDigest (pureHash H) pp layer e msg rho).run =
    Pure.messageHash H pp layer e msg rho from rfl, Pure.otsLeaf]
  generalize codeword? (Pure.messageHash H pp layer e msg rho) = result
  cases result with
  | none => rfl
  | some x =>
    simp only [Id.run_bind, Id.run_pure, HashSig.ofFnInOrder_run, chain_run,
      otsLeafHash, th_run, Pure.leafHash]

/-- The pure layer signer preserves the source error constructor as well as successful fields. -/
theorem signLayer_run (H : Pure.Hash) (pp : PublicParam) (prf : Pure.Derivation)
    (layer : Layer) (e : Nat) (msg : ByteArray) :
    (signLayer (pureHash H) pp (Pure.derivation prf) layer e msg).run =
      Pure.signLayer H pp prf layer e msg := by
  rw [signLayer, Id.run_bind, otsSign_run, Pure.signLayer]
  generalize Pure.otsSign H pp prf layer (UInt32.ofNat e) msg = result
  cases result with
  | none => rfl
  | some pair =>
    rcases pair with ⟨rho, y⟩
    simp only [Id.run_bind, Id.run_pure, path_run]

/-- The pure layer verifier preserves a returned failure and the recovered root. -/
theorem layerRoot_run (H : Pure.Hash) (pp : PublicParam) (layer : Layer) (e : Nat)
    (msg : ByteArray) (sig : LayerSignature) :
    (layerRoot (pureHash H) pp layer e msg sig).run = Pure.layerRoot H pp layer e msg sig := by
  rw [layerRoot, Id.run_bind, otsLeaf_run, Pure.layerRoot]
  generalize Pure.otsLeaf H pp layer (UInt32.ofNat e) msg sig.randomizer sig.chainValues = result
  cases result with
  | none => rfl
  | some leaf => simp only [Id.run_bind, Id.run_pure, fold, climb_run]

/-- Both source signing layers return the same complete error or signature in the pure evaluator. -/
theorem signDerived_run (H : Pure.Hash) (prf : Pure.Derivation) (pp : PublicParam)
    (idx : LeafIndex) (msg : Message) :
    (signDerived (pureHash H) (Pure.derivation prf) pp idx msg).run =
      Pure.signDerived H prf pp idx msg := by
  rw [signDerived, Id.run_bind, signLayer_run, Pure.signDerived]
  generalize Pure.signLayer H pp prf .bottom idx.toNat (packBytes msg) = bottomResult
  cases bottomResult with
  | error err => rfl
  | ok bottom =>
    simp only [Id.run_bind, Id.run_pure, node_run, signLayer_run]
    generalize Pure.signLayer H pp prf .top (bottomTree idx)
      (packBytes (Pure.node H pp prf .bottom LAYER_HEIGHT (bottomTree idx))) = topResult
    cases topResult <;> rfl

/-- The source monadic verifier under fixed H equals its complete pure Boolean observation. -/
theorem verifyWith_run (H : Pure.Hash) (pk : PublicKey) (msg : Message) (sig : Signature) :
    (verifyWith (pureHash H) pk msg sig).run = Pure.verify H pk msg sig := by
  rw [verifyWith, Id.run_bind, layerRoot_run, Pure.verify]
  generalize Pure.layerRoot H pk.publicParam .bottom sig.leafIndex.toNat (packBytes msg)
    sig.bottom = bottomResult
  cases bottomResult with
  | none => rfl
  | some bottomRoot =>
    rw [Id.run_bind, layerRoot_run]
    generalize htop : Pure.layerRoot H pk.publicParam .top (bottomTree sig.leafIndex)
      (packBytes bottomRoot) sig.top = topResult
    cases topResult <;> simp only [htop, Id.run_pure]

/-- Lifting the deterministic derived response is exactly the source seed derivation. -/
theorem seedPrf_eq_derivation (H : Pure.Hash) (seed : Seed) :
    seedPrf (pureHash H) seed = Pure.derivation (Pure.derivedResponse H seed) := rfl

/-- Raw-key key generation agrees without executing the concrete tree. -/
theorem keyGenWith_run (H : Pure.Hash) (rawSeed : Seed) :
    (keyGenWith (pureHash H) rawSeed).run = Pure.keys H rawSeed := by
  rw [keyGenWith, Id.run_bind]
  rw [show (schemeSeed (pureHash H) rawSeed).run = Pure.schemeSeed H rawSeed from rfl]
  rw [seedPrf_eq_derivation, Id.run_bind, publicKeyOf, Id.run_bind]
  rw [show (publicParamOf (Pure.derivation (Pure.derivedResponse H (Pure.schemeSeed H rawSeed)))).run =
    Pure.publicParam (Pure.derivedResponse H (Pure.schemeSeed H rawSeed)) from rfl]
  rw [Id.run_bind, node_run, Id.run_pure, Id.run_pure]
  rfl

/-- Complete source signing agrees under the explicitly selected Except.toOption observation. -/
theorem signWith_toOption (H : Pure.Hash) (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    ((signWith (pureHash H) sk idx msg).run).toOption = Pure.sign H sk idx msg := by
  rw [signWith, Id.run_bind]
  rw [show (schemeSeed (pureHash H) sk.seed).run = Pure.schemeSeed H sk.seed from rfl]
  rw [seedPrf_eq_derivation, Id.run_bind]
  rw [show (publicParamOf (Pure.derivation (Pure.derivedResponse H (Pure.schemeSeed H sk.seed)))).run =
    Pure.publicParam (Pure.derivedResponse H (Pure.schemeSeed H sk.seed)) from rfl]
  rw [signDerived_run]
  rfl

namespace Pure

/-- Every successful derived signature stores the exact requested outer leaf index. -/
theorem signDerived_leafIndex (H : Hash) (prf : Derivation) (pp : PublicParam)
    (idx : LeafIndex) (msg : Message) {sig : Signature}
    (h : (signDerived H prf pp idx msg).toOption = some sig) : sig.leafIndex = idx := by
  rw [signDerived] at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · have hsig := Option.some.inj h
      exact (congrArg Signature.leafIndex hsig).symm

/-- Every successful complete pure signature stores the requested outer leaf index. -/
theorem sign_leafIndex (H : Hash) (sk : SecretKey) (idx : LeafIndex) (msg : Message)
    {sig : Signature} (h : sign H sk idx msg = some sig) : sig.leafIndex = idx :=
  signDerived_leafIndex H (derivedResponse H (schemeSeed H sk.seed))
    (publicParam (derivedResponse H (schemeSeed H sk.seed))) idx msg h

end Pure

/-- Successful source signing preserves the requested index under the selected observation. -/
theorem signWith_leafIndex (H : Pure.Hash) (sk : SecretKey) (idx : LeafIndex) (msg : Message)
    {sig : Signature} (h : ((signWith (pureHash H) sk idx msg).run).toOption = some sig) :
    sig.leafIndex = idx := by
  rw [signWith_toOption] at h
  exact Pure.sign_leafIndex H sk idx msg h

end EthereumXMSSHypertree
