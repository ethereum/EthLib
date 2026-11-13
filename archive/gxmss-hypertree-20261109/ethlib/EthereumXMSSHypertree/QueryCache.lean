/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.PairedResponses
public import EthLib.Cryptography.Xmss.KeyGen
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash
public import VCVio.CryptoFoundations.PRF

/-!
# Full-response derivation queries and persistent caches

The derivation domain consists of the actual public parameter, address and suffix.
There is one request per pair of chain starts. Restricting a byte-input cache to
this domain preserves the complete response and final cache of every adaptive
client. The concrete keyed evaluator samples the raw seed and includes scheme-seed
derivation in evaluation; no uniformity of that derived seed is assumed.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants
open OracleComp OracleSpec

/-- One actual source seed-derivation request, before its fixed seed is inserted. -/
structure DerivationQuery where
  /-- Public parameter prefix of the source hash input. -/
  publicParam : PublicParam
  /-- Complete source address, including its family and layer fields. -/
  address : Address
  /-- The source suffix: empty for starts and parameters, the message for a base. -/
  suffix : ByteArray
  deriving DecidableEq

/-- Insert the fixed scheme seed into the exact source hash input. -/
@[expose]
def derivationInput (seed : Seed) (query : DerivationQuery) : ByteArray :=
  thInput query.publicParam query.address (packBytes seed ++ query.suffix)

/-- The complete source query is recoverable from its hash input for every fixed seed. -/
theorem derivationInput_injective (seed : Seed) : Function.Injective (derivationInput seed) := by
  intro first second h
  obtain ⟨hpp, haddress, hpayload⟩ := thInput_inj h
  have hsuffix := (EthLib.Cryptography.HashSig.byteArray_append_inj hpayload rfl).2
  cases first
  cases second
  simp_all

/-- A pair's source query contains one address and an empty suffix, with no half index. -/
@[expose]
def startQuery (pp : PublicParam) (layer : Layer) (epoch : UInt32)
    (pair : Fin (V / 2)) : DerivationQuery :=
  ⟨pp, addrPrf layer epoch pair, .empty⟩

/-- The 29 pair requests are distinct complete-response inputs. -/
theorem startQuery_injective (pp : PublicParam) (layer : Layer) (epoch : UInt32) :
    Function.Injective (startQuery pp layer epoch) := by
  intro first second h
  exact chain_start_address_injective layer epoch (congrArg DerivationQuery.address h)

/-- Source `SeedPrf` with one oracle request for each complete derivation response. -/
@[expose]
def derivationOracle : SeedPrf (OracleComp (DerivationQuery →ₒ FullResponse)) :=
  fun pp address suffix => (DerivationQuery →ₒ FullResponse).query ⟨pp, address, suffix⟩

/-- The concrete source PRF uses the uniform raw key and derives the scheme seed inside `eval`. -/
@[expose]
def rawSeedPRF (hash : ByteArray → FullResponse) : PRFScheme Seed DerivationQuery FullResponse where
  keygen := $ᵗ Seed
  eval raw query :=
    (seedPrf (pureHash hash) ((schemeSeed (pureHash hash) raw).run)
      query.publicParam query.address query.suffix).run

/-- Uniformity is required only of the raw source key. -/
theorem rawSeedPRF_uniformKey (hash : ByteArray → FullResponse) :
    (rawSeedPRF hash).UniformKey := rfl

/-- Concrete evaluation hashes the exact request after scheme-seed derivation. -/
theorem rawSeedPRF_eval (hash : ByteArray → FullResponse) (raw : Seed)
    (query : DerivationQuery) :
    (rawSeedPRF hash).eval raw query =
      hash (derivationInput ((schemeSeed (pureHash hash) raw).run) query) := rfl

/-- Persistent cache of complete source hash responses. -/
abbrev ByteCache := (ByteArray →ₒ FullResponse).QueryCache

/-- Persistent cache of complete seed-derivation responses. -/
abbrev DerivationCache := (DerivationQuery →ₒ FullResponse).QueryCache

/-- Read the complete source response at every encoded derivation coordinate. -/
@[expose]
def restrictDerivationCache (seed : Seed) (cache : ByteCache) : DerivationCache :=
  QueryCache.ofFn fun query => cache (derivationInput seed query)

/-- Restriction retains the entire 32-byte response at each query. -/
@[simp]
theorem restrictDerivationCache_apply (seed : Seed) (cache : ByteCache)
    (query : DerivationQuery) :
    restrictDerivationCache seed cache query = cache (derivationInput seed query) := rfl

/-- Empty source caches restrict to empty derivation caches. -/
@[simp]
theorem restrictDerivationCache_empty (seed : Seed) :
    restrictDerivationCache seed ∅ = ∅ := by
  ext query
  simp

/-- Inserting a complete response commutes with restriction because source inputs are injective. -/
theorem restrictDerivationCache_insert (seed : Seed) (cache : ByteCache)
    (query : DerivationQuery) (response : FullResponse) :
    restrictDerivationCache seed
        (cache.cacheQuery (derivationInput seed query) response) =
      (restrictDerivationCache seed cache).cacheQuery query response := by
  ext other
  by_cases h : other = query
  · subst other
    simp
  · have hinput := (derivationInput_injective seed).ne h
    simp [QueryCache.cacheQuery_of_ne, h, hinput]

/-- Route source derivation requests into one persistent byte-input cache. -/
@[expose]
def routedCachedDerivations {m : Type → Type} [Monad m]
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed) :
    QueryImpl (DerivationQuery →ₒ FullResponse) (StateT ByteCache m) :=
  fun query => draw.withCaching (derivationInput seed query)

/-- Answer a complete derivation request by inserting the fixed source seed. -/
@[expose]
def derivationAnswers {m : Type → Type}
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed) :
    QueryImpl (DerivationQuery →ₒ FullResponse) m :=
  fun query => draw (derivationInput seed query)

/-- Interpreting the derivation oracle reproduces the actual source `seedPrf` call. -/
theorem derivationOracle_interpret {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed)
    (pp : PublicParam) (address : Address) (suffix : ByteArray) :
    simulateQ (derivationAnswers draw seed) (derivationOracle pp address suffix) =
      seedPrf draw seed pp address suffix := by
  simp [derivationOracle, derivationAnswers, derivationInput, seedPrf]

/-- Cache restriction commutes with one complete-response request, including its final state. -/
theorem routedCachedDerivations_projection {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed)
    (query : DerivationQuery) (cache : ByteCache) :
    Prod.map id (restrictDerivationCache seed) <$>
        (routedCachedDerivations draw seed query).run cache =
      ((derivationAnswers draw seed).withCaching query).run
        (restrictDerivationCache seed cache) := by
  change Prod.map id (restrictDerivationCache seed) <$>
    (draw.withCaching (derivationInput seed query)).run cache = _
  cases h : cache (derivationInput seed query) with
  | none =>
    rw [QueryImpl.withCaching_run_none draw h,
      QueryImpl.withCaching_run_none _ (show restrictDerivationCache seed cache query = none
        from h)]
    simp only [Functor.map_map, Prod.map_apply, id_eq,
      restrictDerivationCache_insert, derivationAnswers]
  | some response =>
    rw [QueryImpl.withCaching_run_some draw h,
      QueryImpl.withCaching_run_some _ (show restrictDerivationCache seed cache query =
        some response from h)]
    simp

/-- Every adaptive run retains its output and the restricted complete-response final cache. -/
theorem routedCachedDerivations_adaptive_projection {m : Type → Type}
    [Monad m] [LawfulMonad m] (draw : QueryImpl (ByteArray →ₒ FullResponse) m)
    (seed : Seed) {A : Type} (program : OracleComp (DerivationQuery →ₒ FullResponse) A)
    (cache : ByteCache) :
    Prod.map id (restrictDerivationCache seed) <$>
        (simulateQ (routedCachedDerivations draw seed) program).run cache =
      (simulateQ (derivationAnswers draw seed).withCaching program).run
        (restrictDerivationCache seed cache) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (restrictDerivationCache seed)
    (routedCachedDerivations_projection draw seed) program cache

/-- A repeated derivation retains both original halves and leaves the complete cache unchanged. -/
theorem cachedDerivation_halves_of_hit {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed)
    (query : DerivationQuery) (cache : ByteCache) (response : FullResponse)
    (hit : cache (derivationInput seed query) = some response) :
    (fun result => (splitResponse result.1, result.2)) <$>
        (routedCachedDerivations draw seed query).run cache =
      pure (splitResponse response, cache) := by
  change (fun result => (splitResponse result.1, result.2)) <$>
    (draw.withCaching (derivationInput seed query)).run cache = _
  rw [QueryImpl.withCaching_run_some draw hit, map_pure]

/-- A miss installs all 32 bytes; the repeated request draws nothing and reads both halves. -/
theorem cachedDerivation_repeated_of_miss {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : QueryImpl (ByteArray →ₒ FullResponse) m) (seed : Seed)
    (query : DerivationQuery) (cache : ByteCache)
    (miss : cache (derivationInput seed query) = none) :
    (do
      let first ← routedCachedDerivations draw seed query
      let second ← routedCachedDerivations draw seed query
      pure (splitResponse first, splitResponse second) :
        StateT ByteCache m ((Digest × Digest) × (Digest × Digest))).run cache =
      (fun response => ((splitResponse response, splitResponse response),
        cache.cacheQuery (derivationInput seed query) response)) <$>
          draw (derivationInput seed query) := by
  simp only [StateT.run_bind, StateT.run_pure, routedCachedDerivations,
    QueryImpl.withCaching_run_none draw miss, bind_map_left]
  simp only [QueryImpl.withCaching_run_some draw (QueryCache.cacheQuery_self _ _ _),
    map_pure, bind_pure_comp]

end EthereumXMSSHypertree
