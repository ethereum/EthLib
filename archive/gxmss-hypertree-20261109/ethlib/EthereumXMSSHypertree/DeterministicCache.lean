/-
Copyright (c) 2026 Matthias Meijers.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.Functional
public import EthereumXMSSHypertree.QueryCache
public import EthereumXMSSHypertree.Retry
public import EthereumXMSSHypertree.Reachability

/-!
# Persistent full-byte caches for deterministic source evaluation

A cache stores complete 32-byte responses at actual source byte inputs. Agreement with a fixed
hash is preserved while interpreting source programs and determines their returned values.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography Xmss Xmss.Constants OracleComp OracleSpec

namespace DeterministicCache

/-- The complete byte-input/full-response oracle used by every source hash invocation. -/
abbrev HashSpec := ByteArray →ₒ FullResponse

/-- One free source hash request, retaining all response bytes. -/
@[expose] def queryHash (input : ByteArray) : OracleComp HashSpec FullResponse :=
  HashSpec.query input

/-- The actual persistent cache run under a fixed full-response hash. -/
@[expose] def runCached {α : Type} (H : Pure.Hash) (program : OracleComp HashSpec α)
    (cache : ByteCache) : α × ByteCache :=
  ((simulateQ (show QueryImpl HashSpec Id from pureHash H).withCaching program).run cache).run

/-- A deterministic complete-byte cache preserves its fixed-hash agreement through every run. -/
theorem runCached_consistent {α : Type} (H : Pure.Hash) (program : OracleComp HashSpec α)
    (cache : ByteCache) (hcache : cache.AgreesWithFn (pureHash H)) :
    (runCached H program cache).1 = (simulateQ (pureHash H) program).run ∧
      (runCached H program cache).2.AgreesWithFn (pureHash H) := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simpa [runCached] using hcache
  | query_bind input next ih =>
    cases hit : cache input with
    | none =>
      have hnext : (cache.cacheQuery input (H input)).AgreesWithFn (pureHash H) :=
        (QueryCache.agreesWithFn_cacheQuery_iff cache input (H input) (pureHash H) hit).2
          ⟨hcache, rfl⟩
      simpa [runCached, hit, StateT.run_bind, pureHash] using
        ih (H input) (cache.cacheQuery input (H input)) hnext
    | some response =>
      have hresponse : H input = response := hcache hit
      subst response
      simpa [runCached, hit, StateT.run_bind, pureHash] using ih (H input) cache hcache

/-- The existing counted source interpreter satisfies the ordinary monad equations. -/
instance : LawfulMonad Reachability.Counted := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  · intro α x
    cases x
    simp [Functor.map, Reachability.Counted.bind]
  · intros
    simp [bind, pure, Reachability.Counted.bind]
  · intros
    simp [bind, Reachability.Counted.bind, Nat.add_assoc, List.append_assoc]

/-- The uncached source oracle program's actual ordered input log and invocation count. -/
@[expose] def runCounted {α : Type} (H : Pure.Hash) (program : OracleComp HashSpec α) :
    Reachability.Counted α :=
  simulateQ (Reachability.countedHash H) program

/-- Install the fixed full response at every logged input, in the exact uncached source order. -/
@[expose] def foldCache (H : Pure.Hash) (cache : ByteCache) (inputs : List ByteArray) : ByteCache :=
  inputs.foldl (fun state input => state.cacheQuery input (H input)) cache

/-- Reinserting the response already stored at a complete input leaves the cache unchanged. -/
theorem cacheQuery_of_hit (H : Pure.Hash) (cache : ByteCache) (input : ByteArray)
    (hit : cache input = some (H input)) : cache.cacheQuery input (H input) = cache := by
  apply QueryCache.ext
  intro other
  by_cases h : other = input
  · subst other
    simpa using hit.symm
  · simp [QueryCache.cacheQuery_of_ne, h]

/-- Counting one actual query prepends exactly its input and adds exactly one invocation. -/
theorem runCounted_query_bind {α : Type} (H : Pure.Hash) (input : ByteArray)
    (next : FullResponse → OracleComp HashSpec α) :
    runCounted H (liftM (HashSpec.query input) >>= next) =
      ⟨(runCounted H (next (H input))).result,
        1 + (runCounted H (next (H input))).calls,
        input :: (runCounted H (next (H input))).inputs⟩ := by
  rw [runCounted, simulateQ_bind]
  rw [simulateQ_spec_query]
  rfl

/-- The uncached source oracle log contains exactly one entry per counted invocation. -/
theorem runCounted_length {α : Type} (H : Pure.Hash) (program : OracleComp HashSpec α) :
    (runCounted H program).inputs.length = (runCounted H program).calls := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
    rw [runCounted_query_bind]
    simpa only [List.length_cons, Nat.add_comm 1] using congrArg Nat.succ (ih (H input))

/-- The final actual cache is exactly the fold of full responses over the uncached source log. -/
theorem runCached_final_eq_fold {α : Type} (H : Pure.Hash) (program : OracleComp HashSpec α)
    (cache : ByteCache) (hcache : cache.AgreesWithFn (pureHash H)) :
    (runCached H program cache).2 = foldCache H cache (runCounted H program).inputs := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => rfl
  | query_bind input next ih =>
    rw [runCounted_query_bind]
    cases hit : cache input with
    | none =>
      have hnext : (cache.cacheQuery input (H input)).AgreesWithFn (pureHash H) :=
        (QueryCache.agreesWithFn_cacheQuery_iff cache input (H input) (pureHash H) hit).2
          ⟨hcache, rfl⟩
      simpa [runCached, foldCache, hit, StateT.run_bind, pureHash] using
        ih (H input) (cache.cacheQuery input (H input)) hnext
    | some response =>
      have hresponse : H input = response := hcache hit
      subst response
      simpa [runCached, foldCache, hit, StateT.run_bind, pureHash,
        cacheQuery_of_hit H cache input hit] using ih (H input) cache hcache

/-- Exact answer and related final cache of the actual deterministic cached run. -/
theorem runCached_exact {α : Type} (H : Pure.Hash) (program : OracleComp HashSpec α)
    (cache : ByteCache) (hcache : cache.AgreesWithFn (pureHash H)) :
    runCached H program cache =
      ((simulateQ (pureHash H) program).run, foldCache H cache (runCounted H program).inputs) := by
  exact Prod.ext (runCached_consistent H program cache hcache).1
    (runCached_final_eq_fold H program cache hcache)

/-- A folded cache contains exactly its previous inputs together with the logged inputs. -/
theorem foldCache_isSome_iff (H : Pure.Hash) (cache : ByteCache) (inputs : List ByteArray)
    (input : ByteArray) :
    ((foldCache H cache inputs) input).isSome ↔ (cache input).isSome ∨ input ∈ inputs := by
  induction inputs generalizing cache with
  | nil => simp [foldCache]
  | cons head rest ih =>
    change ((foldCache H (cache.cacheQuery head (H head)) rest) input).isSome ↔ _
    rw [ih, QueryCache.isSome_cacheQuery_apply_iff]
    simp only [List.mem_cons]
    tauto

/-- Cached inputs are exactly the initial inputs together with the uncached source query log. -/
theorem runCached_isSome_iff {α : Type} (H : Pure.Hash) (program : OracleComp HashSpec α)
    (cache : ByteCache) (hcache : cache.AgreesWithFn (pureHash H)) (input : ByteArray) :
    ((runCached H program cache).2 input).isSome ↔
      (cache input).isSome ∨ input ∈ (runCounted H program).inputs := by
  rw [runCached_final_eq_fold H program cache hcache]
  exact foldCache_isSome_iff H cache _ input

/-- Every newly cached input occurs in the actual uncached source query log. -/
theorem runCached_new_input_mem {α : Type} (H : Pure.Hash) (program : OracleComp HashSpec α)
    (cache : ByteCache) (hcache : cache.AgreesWithFn (pureHash H)) (input : ByteArray)
    (initial : cache input = none) (final : ((runCached H program cache).2 input).isSome) :
    input ∈ (runCounted H program).inputs := by
  simpa [initial] using
    (runCached_isSome_iff H program cache hcache input).1 final

/-- Starting empty, a full input is cached if and only if the source queried it. -/
theorem runCached_empty_isSome_iff {α : Type} (H : Pure.Hash)
    (program : OracleComp HashSpec α) (input : ByteArray) :
    ((runCached H program ∅).2 input).isSome ↔ input ∈ (runCounted H program).inputs := by
  have hempty : (∅ : ByteCache).AgreesWithFn (pureHash H) := by
    intro query response hit
    simp at hit
  simpa using runCached_isSome_iff H program ∅ hempty input

/-- Distinct queried full-byte inputs never exceed the actual uncached source invocation count. -/
theorem distinct_inputs_le_calls {α : Type} (H : Pure.Hash) (program : OracleComp HashSpec α) :
    (runCounted H program).inputs.toFinset.card ≤ (runCounted H program).calls := by
  exact (List.toFinset_card_le _).trans_eq (runCounted_length H program)

/-- The finite set of logged inputs that were absent from the initial cache. -/
@[expose] def newlyCachedInputs {α : Type} (H : Pure.Hash) (program : OracleComp HashSpec α)
    (cache : ByteCache) : Finset ByteArray :=
  (runCounted H program).inputs.toFinset.filter (fun input => (cache input).isNone)

/-- This finite set is exactly the inputs newly present in the actual final cache. -/
theorem mem_newlyCachedInputs_iff {α : Type} (H : Pure.Hash) (program : OracleComp HashSpec α)
    (cache : ByteCache) (hcache : cache.AgreesWithFn (pureHash H)) (input : ByteArray) :
    input ∈ newlyCachedInputs H program cache ↔
      cache input = none ∧ ((runCached H program cache).2 input).isSome := by
  rw [runCached_isSome_iff H program cache hcache input]
  cases hinit : cache input with
  | none => simp [newlyCachedInputs, hinit]
  | some response => simp [newlyCachedInputs, hinit]

/-- The number of newly cached complete inputs is bounded by actual uncached source calls. -/
theorem newlyCachedInputs_card_le_calls {α : Type} (H : Pure.Hash)
    (program : OracleComp HashSpec α) (cache : ByteCache) :
    (newlyCachedInputs H program cache).card ≤ (runCounted H program).calls :=
  (Finset.card_filter_le _ _).trans (distinct_inputs_le_calls H program)

section Interpretation

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Interpretation commutes with the source's ordered-vector loop. -/
theorem interpret_ordered {α : Type} (H : QueryImpl HashSpec m) (n : Nat)
    (f : Fin n → OracleComp HashSpec α) :
    simulateQ H (HashSig.ofFnInOrder n f) =
      HashSig.ofFnInOrder n (fun i => simulateQ H (f i)) :=
  HashSig.ofFnInOrder_map_monad (fun {_} => simulateQ H)
    (fun _ => simulateQ_pure _ _) (fun _ _ => simulateQ_bind _ _ _) n f

/-- Oracle interpretation preserves a complete source seed-derivation call. -/
theorem interpret_seedPrf (H : QueryImpl HashSpec m) (seed : Seed) (pp : PublicParam)
    (address : Address) (suffix : ByteArray) :
    simulateQ H (seedPrf queryHash seed pp address suffix) =
      seedPrf H seed pp address suffix := by
  simp [seedPrf, queryHash]

/-- Oracle interpretation preserves the source addressed hash. -/
theorem interpret_th (H : QueryImpl HashSpec m) (pp : PublicParam) (address : Address)
    (payload : ByteArray) :
    simulateQ H (th queryHash pp address payload) =
      th H pp address payload := by
  simp [th, queryHash]

/-- Oracle interpretation preserves source chains at every legal length. -/
theorem interpret_chain (H : QueryImpl HashSpec m) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (i : Fin V) (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    simulateQ H (Xmss.chain queryHash pp layer e i start steps h value) =
      Xmss.chain H pp layer e i start steps h value := by
  induction steps with
  | zero => simp [Xmss.chain, Wots.chain]
  | succ steps ih =>
    simp only [Xmss.chain, Wots.chain, simulateQ_bind, chainStep, interpret_th]
    simp only [Xmss.chain] at ih
    rw [ih (by omega)]

/-- Oracle interpretation preserves the 29 full paired derivation responses. -/
theorem interpret_starts (H : QueryImpl HashSpec m) (seed : Seed) (pp : PublicParam) (layer : Layer)
    (e : UInt32) :
    simulateQ H (chainStarts pp (seedPrf queryHash seed) layer e) =
      chainStarts pp (seedPrf H seed) layer e := by
  simp [chainStarts, interpret_ordered, interpret_seedPrf]

/-- Oracle interpretation preserves every source public leaf. -/
theorem interpret_publicLeaf (H : QueryImpl HashSpec m) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : UInt32) :
    simulateQ H (otsPublicLeaf queryHash pp (seedPrf queryHash seed) layer e) =
      otsPublicLeaf H pp (seedPrf H seed) layer e := by
  simp [otsPublicLeaf, interpret_starts, interpret_ordered, interpret_chain,
    otsLeafHash, interpret_th]

/-- Oracle interpretation preserves source node hashing. -/
theorem interpret_nodeHash (H : QueryImpl HashSpec m) (pp : PublicParam) (layer : Layer)
    (level j : Nat) (left right : Digest) :
    simulateQ H (nodeHash queryHash pp layer level j left right) =
      nodeHash H pp layer level j left right := by
  simp only [nodeHash, interpret_th]

/-- Oracle interpretation preserves the source tree at every height. -/
theorem interpret_node (H : QueryImpl HashSpec m) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (level j : Nat) :
    simulateQ H (node queryHash pp (seedPrf queryHash seed) layer level j) =
      node H pp (seedPrf H seed) layer level j := by
  induction level generalizing j with
  | zero => exact interpret_publicLeaf H seed pp layer (UInt32.ofNat j)
  | succ level ih =>
    simp only [node, Merkle.node, simulateQ_bind, interpret_nodeHash]
    simp only [node] at ih
    rw [ih]
    rw [ih]

/-- Oracle interpretation preserves source sibling vectors in their exact order. -/
theorem interpret_siblings (H : QueryImpl HashSpec m) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (level j n : Nat) :
    simulateQ H (Merkle.siblings (nodeHash queryHash pp layer)
      (leaves queryHash pp (seedPrf queryHash seed) layer) level j n) =
    Merkle.siblings (nodeHash H pp layer)
      (leaves H pp (seedPrf H seed) layer) level j n := by
  induction n generalizing level j with
  | zero => simp [Merkle.siblings]
  | succ n ih =>
    simp only [Merkle.siblings, simulateQ_bind, simulateQ_pure]
    rw [show simulateQ H (Merkle.node (nodeHash queryHash pp layer)
      (leaves queryHash pp (seedPrf queryHash seed) layer) level (j ^^^ 1)) =
      node H pp (seedPrf H seed) layer level (j ^^^ 1)
      from interpret_node H seed pp layer level (j ^^^ 1)]
    rw [ih]
    simp only [node]

/-- Oracle interpretation preserves the full source authentication path. -/
theorem interpret_path (H : QueryImpl HashSpec m) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : Nat) :
    simulateQ H (path queryHash pp (seedPrf queryHash seed) layer e) =
      path H pp (seedPrf H seed) layer e :=
  interpret_siblings H seed pp layer 0 e LAYER_HEIGHT

/-- Oracle interpretation preserves source path recovery and child orientation. -/
theorem interpret_climb (H : QueryImpl HashSpec m) (pp : PublicParam) (layer : Layer)
    (level j : Nat) (current : Digest) (siblings : List Digest) :
    simulateQ H (Merkle.climb (nodeHash queryHash pp layer) level j current siblings) =
      Merkle.climb (nodeHash H pp layer) level j current siblings := by
  induction siblings generalizing level j current with
  | nil => simp [Merkle.climb]
  | cons sibling rest ih =>
    simp [Merkle.climb, interpret_nodeHash, ih]

/-- Oracle interpretation preserves the source ordered finite counter search. -/
theorem interpret_search (H : QueryImpl HashSpec m) (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (base : Randomizer) (c fuel : Nat) :
    simulateQ H (Internal.findCodeword queryHash pp layer e msg base c fuel) =
      Internal.findCodeword H pp layer e msg base c fuel := by
  induction fuel generalizing c with
  | zero => simp [Internal.findCodeword, Wots.findFirst]
  | succ fuel ih =>
    rw [findCodeword_step, findCodeword_step, simulateQ_bind]
    simp only [simulateQ_map, messageDigest, interpret_th]
    apply bind_congr
    intro result
    cases result with
    | none => exact ih (c + 1)
    | some x => simp

/-- Oracle interpretation preserves the complete source randomizer base. -/
theorem interpret_randomizerBase (H : QueryImpl HashSpec m) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) :
    simulateQ H (randomizerBase pp (seedPrf queryHash seed) layer e msg) =
      randomizerBase pp (seedPrf H seed) layer e msg := by
  change simulateQ H (do
    let response ← seedPrf queryHash seed pp (addrRnd layer e) msg
    pure (halfOf 0 response) : OracleComp HashSpec Digest) = (do
      let response ← seedPrf H seed pp (addrRnd layer e) msg
      pure (halfOf 0 response) : m Digest)
  rw [simulateQ_bind, interpret_seedPrf]
  apply bind_congr
  intro response
  simp only [simulateQ_pure]

/-- Oracle interpretation preserves source message hashing. -/
theorem interpret_messageDigest (H : QueryImpl HashSpec m) (pp : PublicParam) (layer : Layer)
    (e : UInt32) (msg : ByteArray) (rho : Randomizer) :
    simulateQ H (messageDigest queryHash pp layer e msg rho) =
      messageDigest H pp layer e msg rho := by
  simp only [messageDigest, interpret_th]

/-- Oracle interpretation preserves source OTS success and exhaustion. -/
theorem interpret_otsSign (H : QueryImpl HashSpec m) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) :
    simulateQ H (otsSign queryHash pp (seedPrf queryHash seed) layer e msg) =
      otsSign H pp (seedPrf H seed) layer e msg := by
  rw [otsSign, otsSign, simulateQ_bind, interpret_randomizerBase]
  apply bind_congr
  intro base
  rw [simulateQ_bind, interpret_search]
  apply bind_congr
  intro result
  cases result with
  | none => simp
  | some pair =>
    rcases pair with ⟨rho, x⟩
    simp [interpret_starts, interpret_ordered, interpret_chain]

/-- Oracle interpretation preserves source OTS recovery and rejection. -/
theorem interpret_otsLeaf (H : QueryImpl HashSpec m) (pp : PublicParam) (layer : Layer)
    (e : UInt32) (msg : ByteArray) (rho : Randomizer) (y : Vector Digest V) :
    simulateQ H (otsLeaf queryHash pp layer e msg rho y) =
      otsLeaf H pp layer e msg rho y := by
  rw [otsLeaf, otsLeaf, simulateQ_bind, interpret_messageDigest]
  apply bind_congr
  intro digest
  cases codeword? digest with
  | none => simp
  | some x => simp [interpret_ordered, interpret_chain, otsLeafHash, interpret_th]

/-- Oracle interpretation preserves both exact layer-signing results. -/
theorem interpret_signLayer (H : QueryImpl HashSpec m) (seed : Seed) (pp : PublicParam)
    (layer : Layer) (e : Nat) (msg : ByteArray) :
    simulateQ H (signLayer queryHash pp (seedPrf queryHash seed) layer e msg) =
      signLayer H pp (seedPrf H seed) layer e msg := by
  rw [signLayer, signLayer, simulateQ_bind, interpret_otsSign]
  apply bind_congr
  intro result
  cases result with
  | none => simp
  | some pair =>
    rcases pair with ⟨rho, y⟩
    simp [interpret_path]

/-- Oracle interpretation preserves optional source layer roots. -/
theorem interpret_layerRoot (H : QueryImpl HashSpec m) (pp : PublicParam) (layer : Layer)
    (e : Nat) (msg : ByteArray) (sig : LayerSignature) :
    simulateQ H (layerRoot queryHash pp layer e msg sig) =
      layerRoot H pp layer e msg sig := by
  rw [layerRoot, layerRoot, simulateQ_bind, interpret_otsLeaf]
  apply bind_congr
  intro result
  cases result with
  | none => simp
  | some leaf => simp [fold, interpret_climb]

/-- Oracle interpretation preserves both signing layers and their exact errors. -/
theorem interpret_signDerived (H : QueryImpl HashSpec m) (seed : Seed) (pp : PublicParam)
    (idx : LeafIndex) (msg : Message) :
    simulateQ H (signDerived queryHash (seedPrf queryHash seed) pp idx msg) =
      signDerived H (seedPrf H seed) pp idx msg := by
  rw [signDerived, signDerived, simulateQ_bind, interpret_signLayer]
  apply bind_congr
  intro bottomResult
  cases bottomResult with
  | error err => simp
  | ok bottom =>
    simp only [pure_bind, simulateQ_bind, interpret_node, interpret_signLayer]
    apply bind_congr
    intro bottomRoot
    apply bind_congr
    intro topResult
    cases topResult <;> simp

/-- Oracle interpretation preserves complete source verification. -/
theorem interpret_verifyWith (H : QueryImpl HashSpec m) (pk : PublicKey) (msg : Message)
    (sig : Signature) :
    simulateQ H (verifyWith queryHash pk msg sig) =
      verifyWith H pk msg sig := by
  rw [verifyWith, verifyWith, simulateQ_bind, interpret_layerRoot]
  apply bind_congr
  intro bottomResult
  cases bottomResult with
  | none => simp
  | some bottomRoot =>
    rw [simulateQ_bind, interpret_layerRoot]
    apply bind_congr
    intro topResult
    cases topResult <;> simp

/-- Oracle interpretation preserves raw-key scheme-seed derivation. -/
theorem interpret_schemeSeed (H : QueryImpl HashSpec m) (rawSeed : Seed) :
    simulateQ H (schemeSeed queryHash rawSeed) =
      schemeSeed H rawSeed := by
  rw [schemeSeed, schemeSeed]
  exact simulateQ_spec_query H _

/-- Oracle interpretation preserves the source distinguished parameter response. -/
theorem interpret_publicParamOf (H : QueryImpl HashSpec m) (seed : Seed) :
    simulateQ H (publicParamOf (seedPrf queryHash seed)) =
      publicParamOf (seedPrf H seed) := by
  change simulateQ H (do
    let response ← seedPrf queryHash seed (Vector.replicate PUBLIC_PARAM_LEN 0) addrParam .empty
    pure (halfOf 0 response) : OracleComp HashSpec Digest) = (do
      let response ← seedPrf H seed
        (Vector.replicate PUBLIC_PARAM_LEN 0) addrParam .empty
      pure (halfOf 0 response) : m Digest)
  rw [simulateQ_bind, interpret_seedPrf]
  apply bind_congr
  intro response
  simp only [simulateQ_pure]

/-- Oracle interpretation preserves source public-key construction. -/
theorem interpret_publicKeyOf (H : QueryImpl HashSpec m) (seed : Seed) :
    simulateQ H (publicKeyOf queryHash (seedPrf queryHash seed)) =
      publicKeyOf H (seedPrf H seed) := by
  simp [publicKeyOf, interpret_publicParamOf, interpret_node]

/-- Oracle interpretation preserves the actual source raw-key key generation. -/
theorem interpret_keyGenWith (H : QueryImpl HashSpec m) (rawSeed : Seed) :
    simulateQ H (keyGenWith queryHash rawSeed) =
      keyGenWith H rawSeed := by
  simp [keyGenWith, interpret_schemeSeed, interpret_publicKeyOf]

/-- Oracle interpretation preserves complete source signing. -/
theorem interpret_signWith (H : QueryImpl HashSpec m) (sk : SecretKey) (idx : LeafIndex)
    (msg : Message) :
    simulateQ H (signWith queryHash sk idx msg) =
      signWith H sk idx msg := by
  simp [signWith, interpret_schemeSeed, interpret_publicParamOf, interpret_signDerived]

end Interpretation

/-- Cached source key generation equals fixed-H evaluation and keeps full-cache agreement. -/
theorem cached_keyGenWith (H : Pure.Hash) (rawSeed : Seed) (cache : ByteCache)
    (hcache : cache.AgreesWithFn (pureHash H)) :
    (runCached H (keyGenWith queryHash rawSeed) cache).1 =
        (keyGenWith (pureHash H) rawSeed).run ∧
      (runCached H (keyGenWith queryHash rawSeed) cache).2.AgreesWithFn (pureHash H) := by
  simpa only [interpret_keyGenWith] using
    runCached_consistent H (keyGenWith queryHash rawSeed) cache hcache

/-- Cached complete source signing preserves the exact successful signature or source error. -/
theorem cached_signWith (H : Pure.Hash) (sk : SecretKey) (idx : LeafIndex) (msg : Message)
    (cache : ByteCache) (hcache : cache.AgreesWithFn (pureHash H)) :
    (runCached H (signWith queryHash sk idx msg) cache).1 =
        (signWith (pureHash H) sk idx msg).run ∧
      (runCached H (signWith queryHash sk idx msg) cache).2.AgreesWithFn (pureHash H) := by
  simpa only [interpret_signWith] using
    runCached_consistent H (signWith queryHash sk idx msg) cache hcache

/-- Cached source signing retains the explicitly chosen returned-failure observation. -/
theorem cached_signWith_toOption (H : Pure.Hash) (sk : SecretKey) (idx : LeafIndex)
    (msg : Message) (cache : ByteCache) (hcache : cache.AgreesWithFn (pureHash H)) :
    (runCached H (signWith queryHash sk idx msg) cache).1.toOption = Pure.sign H sk idx msg ∧
      (runCached H (signWith queryHash sk idx msg) cache).2.AgreesWithFn (pureHash H) := by
  obtain ⟨hresult, hfinal⟩ := cached_signWith H sk idx msg cache hcache
  exact ⟨(congrArg Except.toOption hresult).trans (signWith_toOption H sk idx msg), hfinal⟩

/-- Cached source verification preserves every Boolean result and full-cache agreement. -/
theorem cached_verifyWith (H : Pure.Hash) (pk : PublicKey) (msg : Message) (sig : Signature)
    (cache : ByteCache) (hcache : cache.AgreesWithFn (pureHash H)) :
    (runCached H (verifyWith queryHash pk msg sig) cache).1 =
        (verifyWith (pureHash H) pk msg sig).run ∧
      (runCached H (verifyWith queryHash pk msg sig) cache).2.AgreesWithFn (pureHash H) := by
  simpa only [interpret_verifyWith] using
    runCached_consistent H (verifyWith queryHash pk msg sig) cache hcache

/-- The free source key-generation log is exactly its direct counted-source interpretation. -/
theorem runCounted_keyGenWith (H : Pure.Hash) (rawSeed : Seed) :
    runCounted H (keyGenWith queryHash rawSeed) =
      keyGenWith (Reachability.countedHash H) rawSeed :=
  interpret_keyGenWith (Reachability.countedHash H) rawSeed

/-- The free complete signing log is exactly its direct counted-source interpretation. -/
theorem runCounted_signWith (H : Pure.Hash) (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    runCounted H (signWith queryHash sk idx msg) =
      signWith (Reachability.countedHash H) sk idx msg :=
  interpret_signWith (Reachability.countedHash H) sk idx msg

/-- The free source verification log is exactly its direct counted-source interpretation. -/
theorem runCounted_verifyWith (H : Pure.Hash) (pk : PublicKey) (msg : Message) (sig : Signature) :
    runCounted H (verifyWith queryHash pk msg sig) =
      verifyWith (Reachability.countedHash H) pk msg sig :=
  interpret_verifyWith (Reachability.countedHash H) pk msg sig

/-- Source key generation returns its exact answer and the fold of its actual source input log. -/
theorem cached_keyGenWith_exact (H : Pure.Hash) (rawSeed : Seed) (cache : ByteCache)
    (hcache : cache.AgreesWithFn (pureHash H)) :
    runCached H (keyGenWith queryHash rawSeed) cache =
      ((keyGenWith (pureHash H) rawSeed).run,
        foldCache H cache (keyGenWith (Reachability.countedHash H) rawSeed).inputs) := by
  simpa only [interpret_keyGenWith, runCounted_keyGenWith] using
    runCached_exact H (keyGenWith queryHash rawSeed) cache hcache

/-- Complete source signing returns its exact error or answer and its exact related final cache. -/
theorem cached_signWith_exact (H : Pure.Hash) (sk : SecretKey) (idx : LeafIndex) (msg : Message)
    (cache : ByteCache) (hcache : cache.AgreesWithFn (pureHash H)) :
    runCached H (signWith queryHash sk idx msg) cache =
      ((signWith (pureHash H) sk idx msg).run,
        foldCache H cache (signWith (Reachability.countedHash H) sk idx msg).inputs) := by
  simpa only [interpret_signWith, runCounted_signWith] using
    runCached_exact H (signWith queryHash sk idx msg) cache hcache

/-- Source verification returns its exact Boolean and the fold of its actual source input log. -/
theorem cached_verifyWith_exact (H : Pure.Hash) (pk : PublicKey) (msg : Message) (sig : Signature)
    (cache : ByteCache) (hcache : cache.AgreesWithFn (pureHash H)) :
    runCached H (verifyWith queryHash pk msg sig) cache =
      ((verifyWith (pureHash H) pk msg sig).run,
        foldCache H cache (verifyWith (Reachability.countedHash H) pk msg sig).inputs) := by
  simpa only [interpret_verifyWith, runCounted_verifyWith] using
    runCached_exact H (verifyWith queryHash pk msg sig) cache hcache

/-- Distinct complete source signing inputs are bounded by its actual source invocation count. -/
theorem signWith_distinct_inputs_le_calls (H : Pure.Hash) (sk : SecretKey) (idx : LeafIndex)
    (msg : Message) :
    (signWith (Reachability.countedHash H) sk idx msg).inputs.toFinset.card ≤
      (signWith (Reachability.countedHash H) sk idx msg).calls := by
  simpa only [runCounted_signWith] using distinct_inputs_le_calls H (signWith queryHash sk idx msg)

/-- Distinct source key-generation inputs are bounded by its actual source invocation count. -/
theorem keyGenWith_distinct_inputs_le_calls (H : Pure.Hash) (rawSeed : Seed) :
    (keyGenWith (Reachability.countedHash H) rawSeed).inputs.toFinset.card ≤
      (keyGenWith (Reachability.countedHash H) rawSeed).calls := by
  simpa only [runCounted_keyGenWith] using distinct_inputs_le_calls H (keyGenWith queryHash rawSeed)

/-- Distinct source verification inputs are bounded by its actual source invocation count. -/
theorem verifyWith_distinct_inputs_le_calls (H : Pure.Hash) (pk : PublicKey) (msg : Message)
    (sig : Signature) :
    (verifyWith (Reachability.countedHash H) pk msg sig).inputs.toFinset.card ≤
      (verifyWith (Reachability.countedHash H) pk msg sig).calls := by
  simpa only [runCounted_verifyWith] using
    distinct_inputs_le_calls H (verifyWith queryHash pk msg sig)

end DeterministicCache
end EthereumXMSSHypertree
