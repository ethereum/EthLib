module

public import EthLib.Cryptography.Proofs.QueryAvoidance
public import EthLib.Cryptography.Proofs.Sphincs.CodewordSearch
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.HonestQueries

/-!
# Proofs: a whole signature rarely fails, in the random-oracle model

A signature signs on three layers, and each layer's key searches for a counter.

Signing fails when any search finds none.

A key's search hashes at the key's encoding address, with a 20-byte payload.

So every trial input has `48 + 20 = 68` bytes.

Before a search, the signer hashes no trial input of that layer.

- Its addressed calls are derivations, encodings on lower layers and hashes of other address types.
- Its calls without an address have other lengths.
  The key expansion hashes 44 bytes, `PRF_msg` 93 and `H_msg` 84.

So a cache that holds no trial input of any key keeps none of a layer until its search starts.

Each search then fails with probability at most `exp(-2^18)`, and signing at most thrice that.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open OracleSpec OracleComp ENNReal

/-! ## Trial inputs -/

/-- The payload of a search trial: the 16-byte digest the key signs, then the 4-byte counter.

Every key signs a 16-byte digest, so the size is the same on every layer. -/
def trialSize : Nat :=
  N + COUNTER_LEN

/-- A query of a trial input of a key on a layer that `S` selects.

It is an input at the key's encoding address, with a payload of the trial size. -/
def IsTrialQuery (S : Layer → Prop) : HashSig.OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr x => ∃ pkSeed key payload, S key.layer ∧ payload.size = trialSize ∧
      x = (thInput pkSeed (adrsEnc key) payload).data.toList

noncomputable instance (S : Layer → Prop) : DecidablePred (IsTrialQuery S) :=
  Classical.decPred _

/-- A trial input of a layer that `S` selects is one of a layer that a weaker `S'` selects. -/
theorem IsTrialQuery.mono {S S' : Layer → Prop} (h : ∀ l, S l → S' l)
    {x : HashSig.OracleWorld.Domain} (hx : IsTrialQuery S x) : IsTrialQuery S' x := by
  rcases x with _ | x
  · exact hx.elim
  · obtain ⟨pkSeed, key, payload, hS, hsize, rfl⟩ := hx
    exact ⟨pkSeed, key, payload, h _ hS, hsize, rfl⟩

/-- A cache with no trial input of the layers `S'` selects has none of the layers `S` selects. -/
theorem cacheAvoids_isTrialQuery_mono {S S' : Layer → Prop} (h : ∀ l, S l → S' l)
    {cache : HashSig.HashSpec.QueryCache} (hcache : CacheAvoids (IsTrialQuery S') cache) :
    CacheAvoids (IsTrialQuery S) cache :=
  fun x hx => hcache x (hx.mono h)

/-- Two keys with the same encoding address are on the same layer. -/
theorem layer_eq_of_adrsEnc_eq {key key' : OtsKey} (h : adrsEnc key = adrsEnc key') :
    key.layer = key'.layer := by
  rw [adrsEnc, adrsEnc, keyAdrs, keyAdrs] at h
  exact (adrs_inj h).2.1

/-- A hash at an address that is no encoding address is not a trial query. -/
theorem H_isQueryBoundP_trial_of_ne {S : Layer → Prop} {pkSeed : PkSeed} {A : Adrs}
    (payload : ByteArray) (hA : ∀ key, A ≠ adrsEnc key) :
    IsQueryBoundP (H (thInput pkSeed A payload)) (IsTrialQuery S) 0 := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
  obtain ⟨_, key, _, _, _, heq⟩ := h
  exact (hA key (thInput_inj (ByteArray.ext (Array.toList_inj.mp heq))).2.1).elim

/-- A hash at the encoding address of a key whose layer `S` leaves out is not a trial query. -/
theorem H_isQueryBoundP_trial_of_layer {S : Layer → Prop} {key : OtsKey} (hS : ¬S key.layer)
    (pkSeed : PkSeed) (payload : ByteArray) :
    IsQueryBoundP (H (thInput pkSeed (adrsEnc key) payload)) (IsTrialQuery S) 0 := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
  obtain ⟨_, key', _, hS', _, heq⟩ := h
  have hA := (thInput_inj (ByteArray.ext (Array.toList_inj.mp heq))).2.1
  exact (hS (layer_eq_of_adrsEnc_eq hA ▸ hS')).elim

/-- A hash of an input of another length than 68 bytes is not a trial query.

A trial input has the 48 bytes of `PK.seed | ADRS`, then a payload of 20. -/
theorem H_isQueryBoundP_trial_of_size {S : Layer → Prop} {x : ByteArray} (hx : x.size ≠ 68) :
    IsQueryBoundP (H x) (IsTrialQuery S) 0 := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
  obtain ⟨pkSeed, key, payload, -, hsize, heq⟩ := h
  change x.data.toList = _ at heq
  have hlen : x.size = (thInput pkSeed (adrsEnc key) payload).size := by
    have := congrArg List.length heq
    rw [Array.length_toList, Array.length_toList] at this
    exact this
  rw [size_thInput, hsize] at hlen
  exact absurd hlen hx

/-- The encodings of a key whose layer `S` leaves out query no trial input. -/
theorem encodingAvoids_isTrialQuery {S : Layer → Prop} {key : OtsKey} (hS : ¬S key.layer) :
    EncodingAvoids (IsTrialQuery S) H key :=
  fun pkSeed payload _ => H_isQueryBoundP_trial_of_layer hS pkSeed payload

/-- No hash at an address other than an encoding address is a trial query.

The two unused hypotheses give the lemma the shape that the query lemmas ask of the hash. -/
theorem H_thInput_isQueryBoundP_trial (S : Layer → Prop) (pkSeed : PkSeed) (A : Adrs)
    (payload : ByteArray) (_ : ¬IsDerivationAddress A) (hA : ∀ key, A ≠ adrsEnc key)
    (_ : 16 ≤ payload.size) : IsQueryBoundP (H (thInput pkSeed A payload)) (IsTrialQuery S) 0 :=
  H_isQueryBoundP_trial_of_ne payload hA

/-- No derivation from `SK.seed` is a trial query: it hashes at a derivation address. -/
theorem prf_isQueryBoundP_trial (S : Layer → Prop) (pkSeed : PkSeed) (seed : Seed) (A : Adrs)
    (hA : IsDerivationAddress A) : IsQueryBoundP (prf H pkSeed seed A) (IsTrialQuery S) 0 :=
  th_isQueryBoundP_zero_of_hash H
    (H_isQueryBoundP_trial_of_ne _ fun key h => not_isDerivationAddress_adrsEnc key (h ▸ hA))

/-- No call of the message digest is a trial query: it hashes 84 bytes. -/
theorem H_digestInput_isQueryBoundP_trial (S : Layer → Prop) (rho : Randomizer)
    (pkSeed : PkSeed) (pkRoot : Digest) (msg : Message) (i : Nat) :
    IsQueryBoundP (H (digestInput rho pkSeed pkRoot msg i)) (IsTrialQuery S) 0 :=
  H_isQueryBoundP_trial_of_size (by rw [size_digestInput]; decide)

/-! ## One layer fails rarely

From here on, the signer's secrets come from a source that queries no trial input. -/

/-- **A key's one-time signature finds no counter with probability at most `exp(-2^18)`.**

The cache holds no trial input of the key's layer. -/
theorem prEvent_otsSign_none_le (pkSeed : PkSeed) (prf : Prf (OracleComp HashSig.OracleWorld))
    (key : OtsKey) (msg : Digest) (cache : HashSig.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery (· = key.layer)) cache) :
    Pr{let z ← (simulateQ HashSig.HashSpec.romImpl
      (otsSign H pkSeed prf key msg)).run' cache}[z = none]
      ≤ ENNReal.ofReal (Real.exp (-(2 ^ 18))) := by
  unfold otsSign
  rw [run'_simulateQ_romImpl_bind]
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun z => z.1 = none) _ fun z _ hz => ?_).trans ?_
  · rcases z with ⟨_ | ⟨counter, x⟩, c'⟩
    · exact absurd rfl hz
    · dsimp only
      rw [← bind_assoc]
      exact prEvent_run'_romImpl_bind_pure_some _ (fun y => (counter, y)) _
  · rw [prEvent_run_romImpl_fst _ _ fun r => r = none]
    refine prEvent_findCounter_none_le pkSeed key msg cache fun j _ =>
      hcache _ ⟨pkSeed, key, _, rfl, ?_, rfl⟩
    simp only [ByteArray.size_append, Base.size_packBytes, trialSize]

/-- **A layer's signature fails with probability at most `exp(-2^18)`.**

The cache holds no trial input of the layer. -/
theorem prEvent_signLayer_error_le (pkSeed : PkSeed) (prf : Prf (OracleComp HashSig.OracleWorld))
    (layer : Layer) (idx : Nat) (msg : Digest) (cache : HashSig.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery (· = layer)) cache) :
    Pr{let z ← (simulateQ HashSig.HashSpec.romImpl
      (signLayer H pkSeed prf layer idx msg)).run' cache}[z.isOk = false]
      ≤ ENNReal.ofReal (Real.exp (-(2 ^ 18))) := by
  unfold signLayer
  rw [run'_simulateQ_romImpl_bind]
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun z => z.1 = none) _ fun z _ hz => ?_).trans ?_
  · rcases z with ⟨_ | ⟨counter, y⟩, c'⟩
    · exact absurd rfl hz
    · dsimp only
      exact prEvent_run'_romImpl_bind_pure_ok _ _ _
  · rw [prEvent_run_romImpl_fst _ _ fun r => r = none]
    exact prEvent_otsSign_none_le pkSeed prf _ msg cache hcache

/-- **A layer signs what its layer message gives, then signing goes on.**

The cache holds no trial input of the layer or of a layer above it.

After a success, the rest's event has probability at most `δ`.

That holds from every cache with no trial input above the layer.

Then the event has probability at most `exp(-2^18) + δ`. -/
theorem prEvent_layerMessage_bind_signLayer_le {β : Type} (pkSeed : PkSeed)
    (prf : Prf (OracleComp HashSig.OracleWorld))
    (hprf : ∀ S A, IsDerivationAddress A → IsQueryBoundP (prf A) (IsTrialQuery S) 0)
    (layer : Layer) (idx : Nat)
    (k : Except SphincsError (LayerSignature layer) → OracleComp HashSig.OracleWorld β)
    (E : β → Prop) {δ : ℝ≥0∞} (cache : HashSig.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery (layer.toNat ≤ ·.toNat)) cache)
    (hk : ∀ sig c, CacheAvoids (IsTrialQuery (layer.toNat < ·.toNat)) c →
      Pr{let y ← (simulateQ HashSig.HashSpec.romImpl (k (.ok sig))).run' c}[E y] ≤ δ) :
    Pr{let y ← (simulateQ HashSig.HashSpec.romImpl
      (layerMessage H pkSeed prf layer idx >>= fun msg =>
        signLayer H pkSeed prf layer idx msg >>= k)).run' cache}[E y]
      ≤ ENNReal.ofReal (Real.exp (-(2 ^ 18))) + δ := by
  rw [run'_simulateQ_romImpl_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
  -- What the layer signs queries no trial input.
  have hc : CacheAvoids (IsTrialQuery (layer.toNat ≤ ·.toNat)) z.2 :=
    cache_eq_none_of_mem_support_run_romImpl (layerMessage_isQueryBoundP_zero H prf
      (H_thInput_isQueryBoundP_trial _) (hprf _) pkSeed layer idx) hcache hz
  rw [run'_simulateQ_romImpl_bind]
  refine (prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support _ _
    (fun w => w.1.isOk = false) E (ε := δ) fun w hw hok => ?_).trans ?_
  · -- The layer signed; no trial input above it is cached yet.
    rcases w with ⟨_ | sig, c'⟩
    · exact absurd rfl hok
    refine hk sig c' (cache_eq_none_of_mem_support_run_romImpl
      (signLayer_isQueryBoundP_zero H prf (H_thInput_isQueryBoundP_trial _) (hprf _) pkSeed layer
        idx (encodingAvoids_isTrialQuery (Nat.lt_irrefl _)) z.1)
      (cacheAvoids_isTrialQuery_mono (fun _ => Nat.le_of_lt) hc) hw)
  · -- The layer's own search fails rarely.
    rw [prEvent_run_romImpl_fst _ _ fun r : Except SphincsError (LayerSignature layer) =>
      r.isOk = false]
    exact add_le_add (prEvent_signLayer_error_le pkSeed prf layer idx _ _
        (cacheAvoids_isTrialQuery_mono (fun _ h => h ▸ le_refl _) hc))
      (mul_le_of_le_one_right' (prEvent_le_one _))

/-! ## A whole signature fails rarely -/

/-- **Signing from a source of secrets fails with probability at most `3 exp(-2^18)`.**

The source queries no trial input, and the cache holds no trial input of any key. -/
theorem prEvent_signDerived_error_le (prf : Prf (OracleComp HashSig.OracleWorld))
    (hprf : ∀ S A, IsDerivationAddress A → IsQueryBoundP (prf A) (IsTrialQuery S) 0)
    (pk : PublicKey) (rho : Randomizer) (msg : Message) (cache : HashSig.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery fun _ => True) cache) :
    Pr{let z ← (simulateQ HashSig.HashSpec.romImpl
      (signDerived H prf pk rho msg)).run' cache}[z.isOk = false]
      ≤ 3 * ENNReal.ofReal (Real.exp (-(2 ^ 18))) := by
  have hinv : ∀ {α : Type} {oa : OracleComp HashSig.OracleWorld α},
      IsQueryBoundP oa (IsTrialQuery fun _ => True) 0 → ∀ c,
      CacheAvoids (IsTrialQuery fun _ => True) c →
      ∀ z ∈ support ((simulateQ HashSig.HashSpec.romImpl oa).run c),
        CacheAvoids (IsTrialQuery fun _ => True) z.2 :=
    fun h c hc z hz => cache_eq_none_of_mem_support_run_romImpl h hc hz
  unfold signDerived
  refine prEvent_run'_romImpl_bind_le _ _ _ _
    (hinv (hMsg_isQueryBoundP_zero H _ _ _ _ fun i =>
      H_digestInput_isQueryBoundP_trial _ _ _ _ _ _) _ hcache) fun d c hc => ?_
  refine prEvent_run'_romImpl_bind_le _ _ _ _
    (hinv (forsSign_isQueryBoundP_zero H prf (H_thInput_isQueryBoundP_trial _) (hprf _) _ _ _) _
      hc) fun fors c hc => ?_
  set ε := ENNReal.ofReal (Real.exp (-(2 ^ 18)))
  refine (prEvent_layerMessage_bind_signLayer_le _ prf hprf .bottom _ _ _ (δ := ε + (ε + 0)) c
    (cacheAvoids_isTrialQuery_mono (fun _ _ => trivial) hc) fun sig c hc => ?_).trans
    (le_of_eq (by ring))
  dsimp only
  rw [pure_bind]
  refine prEvent_layerMessage_bind_signLayer_le _ prf hprf .middle _ _ _ (δ := ε + 0) c hc
    fun sig c hc => ?_
  dsimp only
  rw [pure_bind]
  refine prEvent_layerMessage_bind_signLayer_le _ prf hprf .top _ _ _ (δ := 0) c hc
    fun sig c hc => ?_
  dsimp only
  rw [pure_bind]
  simp [Except.isOk, Except.toBool]

/-- **Building the top tree first keeps a bound that holds from every cache without trials.**

The secrets come from a source that queries no trial input of the layers `S` selects. -/
theorem prEvent_publicKeyOf_bind_le {β : Type} {S : Layer → Prop} (pkSeed : PkSeed)
    (prf : Prf (OracleComp HashSig.OracleWorld))
    (hprf : ∀ A, IsDerivationAddress A → IsQueryBoundP (prf A) (IsTrialQuery S) 0)
    (f : PublicKey → OracleComp HashSig.OracleWorld β) (E : β → Prop) {ε : ℝ≥0∞}
    {cache : HashSig.HashSpec.QueryCache} (hcache : CacheAvoids (IsTrialQuery S) cache)
    (hf : ∀ pk c, CacheAvoids (IsTrialQuery S) c →
      Pr{let y ← (simulateQ HashSig.HashSpec.romImpl (f pk)).run' c}[E y] ≤ ε) :
    Pr{let y ← (simulateQ HashSig.HashSpec.romImpl
      (publicKeyOf H pkSeed prf >>= f)).run' cache}[E y] ≤ ε :=
  prEvent_run'_romImpl_bind_le _ _ _ _ (fun _ hz => cache_eq_none_of_mem_support_run_romImpl
    (publicKeyOf_isQueryBoundP_zero H prf (H_thInput_isQueryBoundP_trial S) hprf pkSeed) hcache hz)
    hf

/-- **A leanSPHINCS signature fails with probability at most `3 exp(-2^18)`.**

The hash is a lazily sampled random oracle, and signing starts from any cache.

The cache must hold no trial input of any key.

A trial input is at a key's encoding address, with a 20-byte payload: a digest and a counter.

Each layer's search then fails with probability at most `exp(-2^18)`. -/
theorem prEvent_signWith_error_le (sk : SecretKey) (msg : Message)
    (cache : HashSig.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery fun _ => True) cache) :
    Pr{let z ← (simulateQ HashSig.HashSpec.romImpl
      (signWith H sk msg)).run' cache}[z.isOk = false]
      ≤ 3 * ENNReal.ofReal (Real.exp (-(2 ^ 18))) := by
  unfold signWith
  -- The key expansion hashes 44 bytes, too short to be a trial input.
  refine prEvent_run'_romImpl_bind_le _ _ _ _ (fun z hz =>
    cache_eq_none_of_mem_support_run_romImpl (expandKey_isQueryBoundP_zero H sk.seed fun _ =>
      H_isQueryBoundP_trial_of_size (by rw [size_expandInput]; decide)) hcache hz)
    fun key c hc => ?_
  -- The top tree hashes at addresses of other types, and its secrets are derivations.
  refine prEvent_publicKeyOf_bind_le _ _ (prf_isQueryBoundP_trial _ key.pkSeed sk.seed) _ _ hc
    fun pk c hc => ?_
  -- `PRF_msg` hashes 93 bytes.
  refine prEvent_run'_romImpl_bind_le _ _ _ _ (fun z hz =>
    cache_eq_none_of_mem_support_run_romImpl (prfMsg_isQueryBoundP_zero H _ _ _
      (H_isQueryBoundP_trial_of_size (by rw [size_randomizerInput]; decide))) hc hz)
    fun rho c hc => ?_
  exact prEvent_signDerived_error_le _ (fun S => prf_isQueryBoundP_trial S key.pkSeed sk.seed)
    pk rho msg c hc

/-- From an empty cache, a leanSPHINCS signature fails with probability at most `3 exp(-2^18)`. -/
theorem prEvent_signWith_error_le_empty (sk : SecretKey) (msg : Message) :
    Pr{let z ← (simulateQ HashSig.HashSpec.romImpl
      (signWith H sk msg)).run' ∅}[z.isOk = false]
      ≤ 3 * ENNReal.ofReal (Real.exp (-(2 ^ 18))) :=
  prEvent_signWith_error_le sk msg ∅ fun _ _ => rfl

end EthLib.Cryptography.Sphincs.Unforgeability
