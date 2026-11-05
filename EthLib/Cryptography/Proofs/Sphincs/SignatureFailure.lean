module

public import EthLib.Cryptography.Proofs.QueryAvoidance
public import EthLib.Cryptography.Proofs.Sphincs.CodewordSearch
public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.HonestQueries

/-!
# Proofs: a whole signature rarely fails, in the random-oracle model

A signature signs on three layers, and each layer's key searches for a counter.

Signing fails when any search finds none.

A key's search hashes at the key's encoding address, with a payload of one fixed length.

Before a search, the signer hashes no such input of that layer.

The calls before it are derivations, encodings on lower layers and hashes at other addresses.

The 43-byte input that grows the scheme seed is too short to be a trial input.

So a cache that holds no trial input of any key keeps none of a layer until its search starts.

Each search then fails with probability at most `exp(-2^18)`, and signing at most thrice that.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open OracleSpec OracleComp ENNReal

/-! ## Trial inputs -/

/-- The payload of a search trial on the layer: what its key signs, then the 4-byte counter.

A bottom key signs a 768-byte FORS key, and a higher key a 16-byte root. -/
def trialSize : Layer → Nat
  | .bottom => 772
  | .middle => 20
  | .top => 20

/-- A query of a trial input of a key on a layer that `S` selects.

It is an input at the key's encoding address, with a payload of the layer's trial size. -/
def IsTrialQuery (S : Layer → Prop) : XmssSecurity.OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr x => ∃ pp key payload, S key.layer ∧ payload.size = trialSize key.layer ∧
      x = (thInput pp (addrEncoding key) payload).data.toList

noncomputable instance (S : Layer → Prop) : DecidablePred (IsTrialQuery S) :=
  Classical.decPred _

/-- A trial input of a layer that `S` selects is one of a layer that a weaker `S'` selects. -/
theorem IsTrialQuery.mono {S S' : Layer → Prop} (h : ∀ l, S l → S' l)
    {x : XmssSecurity.OracleWorld.Domain} (hx : IsTrialQuery S x) : IsTrialQuery S' x := by
  rcases x with _ | x
  · exact hx.elim
  · obtain ⟨pp, key, payload, hS, hsize, rfl⟩ := hx
    exact ⟨pp, key, payload, h _ hS, hsize, rfl⟩

/-- A cache with no trial input of the layers `S'` selects has none of the layers `S` selects. -/
theorem cacheAvoids_isTrialQuery_mono {S S' : Layer → Prop} (h : ∀ l, S l → S' l)
    {cache : XmssSecurity.HashSpec.QueryCache} (hcache : CacheAvoids (IsTrialQuery S') cache) :
    CacheAvoids (IsTrialQuery S) cache :=
  fun x hx => hcache x (hx.mono h)

/-- Two keys with the same encoding address are on the same layer. -/
theorem layer_eq_of_addrEncoding_eq {key key' : OtsKey}
    (h : addrEncoding key = addrEncoding key') : key.layer = key'.layer := by
  rw [addrEncoding, addrEncoding, keyAddress, keyAddress] at h
  exact Layer.toNat_injective (congrArg Fin.val (encodeAddress_inj.mp h).2.2.1)

/-- A hash at an address that is no encoding address is not a trial query. -/
theorem H_isQueryBoundP_trial_of_ne {S : Layer → Prop} {pp : PublicParam} {A : Address}
    (payload : ByteArray) (hA : ∀ key, A ≠ addrEncoding key) :
    IsQueryBoundP (H (thInput pp A payload)) (IsTrialQuery S) 0 := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
  obtain ⟨_, key, _, _, _, heq⟩ := h
  exact (hA key (thInput_inj (ByteArray.ext (Array.toList_inj.mp heq))).2.1).elim

/-- A hash at the encoding address of a key whose layer `S` leaves out is not a trial query. -/
theorem H_isQueryBoundP_trial_of_layer {S : Layer → Prop} {key : OtsKey} (hS : ¬S key.layer)
    (pp : PublicParam) (payload : ByteArray) :
    IsQueryBoundP (H (thInput pp (addrEncoding key) payload)) (IsTrialQuery S) 0 := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
  obtain ⟨_, key', _, hS', _, heq⟩ := h
  have hA := (thInput_inj (ByteArray.ext (Array.toList_inj.mp heq))).2.1
  exact (hS (layer_eq_of_addrEncoding_eq hA ▸ hS')).elim

/-- A hash of an input of fewer than 52 bytes is not a trial query.

A trial input has 32 bytes before a payload of at least 20. -/
theorem H_isQueryBoundP_trial_of_size {S : Layer → Prop} {x : ByteArray} (hx : x.size < 52) :
    IsQueryBoundP (H x) (IsTrialQuery S) 0 := by
  refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => ?_)
  obtain ⟨pp, key, payload, -, hsize, heq⟩ := h
  change x.data.toList = _ at heq
  have hlen : x.size = (thInput pp (addrEncoding key) payload).size := by
    have := congrArg List.length heq
    rw [Array.length_toList, Array.length_toList] at this
    exact this
  have hmin : 20 ≤ trialSize key.layer := by cases key.layer <;> decide
  rw [size_thInput, hsize] at hlen
  omega

/-- The encodings of a key whose layer `S` leaves out query no trial input. -/
theorem encodingAvoids_isTrialQuery {S : Layer → Prop} {key : OtsKey} (hS : ¬S key.layer) :
    EncodingAvoids (IsTrialQuery S) H key :=
  fun pp payload _ => H_isQueryBoundP_trial_of_layer hS pp payload

/-- No hash at an address other than an encoding address is a trial query.

The two unused hypotheses give the lemma the shape that the query lemmas ask of the hash. -/
theorem H_thInput_isQueryBoundP_trial (S : Layer → Prop) (pp : PublicParam) (A : Address)
    (payload : ByteArray) (_ : ¬IsDerivationAddress A) (hA : ∀ key, A ≠ addrEncoding key)
    (_ : 16 ≤ payload.size) : IsQueryBoundP (H (thInput pp A payload)) (IsTrialQuery S) 0 :=
  H_isQueryBoundP_trial_of_ne payload hA

/-- No derivation from a scheme seed is a trial query: it hashes at a derivation address. -/
theorem seedPrf_isQueryBoundP_trial (S : Layer → Prop) (s : Seed) (pp : PublicParam)
    (A : Address) (suffix : ByteArray) (hA : IsDerivationAddress A) :
    IsQueryBoundP (seedPrf H s pp A suffix) (IsTrialQuery S) 0 :=
  H_isQueryBoundP_trial_of_ne _ fun key h => not_isDerivationAddress_addrEncoding key (h ▸ hA)

/-! ## One layer fails rarely -/

/-- What a layer's key signs, with the counter, fills the layer's trial payload. -/
theorem size_add_of_mem_support_layerMessage {pp : PublicParam} {prf : SeedPrf (OracleComp
    XmssSecurity.OracleWorld)} {layer : Layer} {idx : Nat} {msg : ByteArray}
    (hmsg : msg ∈ support (layerMessage H pp prf layer idx)) :
    msg.size + 4 = trialSize layer := by
  cases layer <;> simp only [layerMessage, bind_pure_comp, support_map, Set.mem_image] at hmsg <;>
    obtain ⟨x, -, rfl⟩ := hmsg
  · rw [size_forsKeyBytes]
    rfl
  all_goals
    rw [size_packBytes_digest]
    rfl

/-- **A key's one-time signature finds no counter with probability at most `exp(-2^18)`.**

The message with its counter fills the trial payload of the key's layer.

The cache holds no trial input of that layer. -/
theorem prEvent_otsSign_none_le (pp : PublicParam) (prf : SeedPrf (OracleComp
    XmssSecurity.OracleWorld)) (key : OtsKey) (msg : ByteArray)
    (hsize : msg.size + 4 = trialSize key.layer) (cache : XmssSecurity.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery (· = key.layer)) cache) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (otsSign H pp prf key msg)).run' cache}[z = none]
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
    refine prEvent_findCounter_none_le pp key msg cache fun j _ =>
      hcache _ ⟨pp, key, _, rfl, ?_, rfl⟩
    rw [ByteArray.size_append, Base.size_packBytes, ← hsize]
    rfl

/-- **A layer's signature fails with probability at most `exp(-2^18)`.**

The message with its counter fills the layer's trial payload.

The cache holds no trial input of the layer. -/
theorem prEvent_signLayer_error_le (pp : PublicParam) (prf : SeedPrf (OracleComp
    XmssSecurity.OracleWorld)) (layer : Layer) (idx : Nat) (msg : ByteArray)
    (hsize : msg.size + 4 = trialSize layer) (cache : XmssSecurity.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery (· = layer)) cache) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (signLayer H pp prf layer idx msg)).run' cache}[z.isOk = false]
      ≤ ENNReal.ofReal (Real.exp (-(2 ^ 18))) := by
  unfold signLayer
  rw [run'_simulateQ_romImpl_bind]
  refine (prEvent_bind_le_prEvent_of_support _ _ (fun z => z.1 = none) _ fun z _ hz => ?_).trans ?_
  · rcases z with ⟨_ | ⟨counter, y⟩, c'⟩
    · exact absurd rfl hz
    · dsimp only
      exact prEvent_run'_romImpl_bind_pure_ok _ _ _
  · rw [prEvent_run_romImpl_fst _ _ fun r => r = none]
    exact prEvent_otsSign_none_le pp prf _ msg hsize cache hcache

/-- **A layer signs what its layer message gives, then signing goes on.**

The cache holds no trial input of the layer or of a layer above it.

After a success, the rest's event has probability at most `δ`.

That holds from every cache with no trial input above the layer.

Then the event has probability at most `exp(-2^18) + δ`. -/
theorem prEvent_layerMessage_bind_signLayer_le {β : Type} (s : Seed) (pp : PublicParam)
    (layer : Layer) (idx : Nat)
    (k : Except SphincsError (LayerSignature layer) → OracleComp XmssSecurity.OracleWorld β)
    (E : β → Prop) {δ : ℝ≥0∞} (cache : XmssSecurity.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery (layer.toNat ≤ ·.toNat)) cache)
    (hk : ∀ sig c, CacheAvoids (IsTrialQuery (layer.toNat < ·.toNat)) c →
      Pr{let y ← (simulateQ XmssSecurity.HashSpec.romImpl (k (.ok sig))).run' c}[E y] ≤ δ) :
    Pr{let y ← (simulateQ XmssSecurity.HashSpec.romImpl
      (layerMessage H pp (seedPrf H s) layer idx >>= fun msg =>
        signLayer H pp (seedPrf H s) layer idx msg >>= k)).run' cache}[E y]
      ≤ ENNReal.ofReal (Real.exp (-(2 ^ 18))) + δ := by
  rw [run'_simulateQ_romImpl_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
  -- What the layer signs queries no trial input, and has the layer's message size.
  have hc : CacheAvoids (IsTrialQuery (layer.toNat ≤ ·.toNat)) z.2 :=
    cache_eq_none_of_mem_support_run_romImpl (layerMessage_isQueryBoundP_zero H _
      (H_thInput_isQueryBoundP_trial _) (seedPrf_isQueryBoundP_trial _ s) pp layer idx) hcache hz
  have hmsg : z.1 ∈ support (layerMessage H pp (seedPrf H s) layer idx) :=
    support_simulateQ_run'_subset XmssSecurity.HashSpec.romImpl _ cache (by
      rw [StateT.run'_eq, support_map]
      exact ⟨z, hz, rfl⟩)
  rw [run'_simulateQ_romImpl_bind]
  refine (prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support _ _
    (fun w => w.1.isOk = false) E (ε := δ) fun w hw hok => ?_).trans ?_
  · -- The layer signed; no trial input above it is cached yet.
    rcases w with ⟨_ | sig, c'⟩
    · exact absurd rfl hok
    refine hk sig c' (cache_eq_none_of_mem_support_run_romImpl
      (signLayer_isQueryBoundP_zero H _ (H_thInput_isQueryBoundP_trial _)
        (seedPrf_isQueryBoundP_trial _ s) pp layer idx
        (encodingAvoids_isTrialQuery (Nat.lt_irrefl _))
        (by have := size_add_of_mem_support_layerMessage hmsg; cases layer <;>
          simp only [trialSize] at this <;> omega))
      (cacheAvoids_isTrialQuery_mono (fun _ => Nat.le_of_lt) hc) hw)
  · -- The layer's own search fails rarely.
    rw [prEvent_run_romImpl_fst _ _ fun r : Except SphincsError (LayerSignature layer) =>
      r.isOk = false]
    exact add_le_add (prEvent_signLayer_error_le pp _ layer idx _
        (size_add_of_mem_support_layerMessage hmsg) _
        (cacheAvoids_isTrialQuery_mono (fun _ h => h ▸ le_refl _) hc))
      (mul_le_of_le_one_right' (prEvent_le_one _))

/-! ## A whole signature fails rarely -/

/-- **Signing from the derivations fails with probability at most `3 exp(-2^18)`.**

The cache holds no trial input of any key. -/
theorem prEvent_signDerived_error_le (s : Seed) (pp : PublicParam) (msg : Message)
    (cache : XmssSecurity.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery fun _ => True) cache) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (signDerived H (seedPrf H s) pp msg)).run' cache}[z.isOk = false]
      ≤ 3 * ENNReal.ofReal (Real.exp (-(2 ^ 18))) := by
  have hH := H_thInput_isQueryBoundP_trial (fun _ => True)
  have hprf := seedPrf_isQueryBoundP_trial (fun _ => True) s
  have hinv : ∀ {α : Type} {oa : OracleComp XmssSecurity.OracleWorld α},
      IsQueryBoundP oa (IsTrialQuery fun _ => True) 0 → ∀ c,
      CacheAvoids (IsTrialQuery fun _ => True) c →
      ∀ z ∈ support ((simulateQ XmssSecurity.HashSpec.romImpl oa).run c),
        CacheAvoids (IsTrialQuery fun _ => True) z.2 :=
    fun h c hc z hz => cache_eq_none_of_mem_support_run_romImpl h hc hz
  unfold signDerived
  refine prEvent_run'_romImpl_bind_le _ _ _ _
    (hinv (randomizer_isQueryBoundP_zero _ hprf pp msg) _ hcache) fun rho c hc => ?_
  refine prEvent_run'_romImpl_bind_le _ _ _ _
    (hinv (messageDigest_isQueryBoundP_zero H hH pp msg rho) _ hc) fun d c hc => ?_
  refine prEvent_run'_romImpl_bind_le _ _ _ _
    (hinv (forsSign_isQueryBoundP_zero H _ hH hprf _ _ _) _ hc) fun fors c hc => ?_
  set ε := ENNReal.ofReal (Real.exp (-(2 ^ 18)))
  refine (prEvent_layerMessage_bind_signLayer_le s pp .bottom _ _ _ (δ := ε + (ε + 0)) c
    (cacheAvoids_isTrialQuery_mono (fun _ _ => trivial) hc) fun sig c hc => ?_).trans
    (le_of_eq (by ring))
  dsimp only
  rw [pure_bind]
  refine prEvent_layerMessage_bind_signLayer_le s pp .middle _ _ _ (δ := ε + 0) c hc
    fun sig c hc => ?_
  dsimp only
  rw [pure_bind]
  refine prEvent_layerMessage_bind_signLayer_le s pp .top _ _ _ (δ := 0) c hc
    fun sig c hc => ?_
  dsimp only
  rw [pure_bind]
  simp [Except.isOk, Except.toBool]

/-- **A leanSPHINCS signature fails with probability at most `3 exp(-2^18)`.**

The hash is a lazily sampled random oracle, and signing starts from any cache.

The cache must hold no trial input of any key.

A trial input is at a key's encoding address, with a payload of the trial size of its layer.

That size is 772 bytes on the bottom layer and 20 above it.

Each layer's search then fails with probability at most `exp(-2^18)`. -/
theorem prEvent_signWith_error_le (sk : SecretKey) (msg : Message)
    (cache : XmssSecurity.HashSpec.QueryCache)
    (hcache : CacheAvoids (IsTrialQuery fun _ => True) cache) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (signWith H sk msg)).run' cache}[z.isOk = false]
      ≤ 3 * ENNReal.ofReal (Real.exp (-(2 ^ 18))) := by
  unfold signWith
  refine prEvent_run'_romImpl_bind_le _ _ _ _ (fun z hz =>
    cache_eq_none_of_mem_support_run_romImpl (H_isQueryBoundP_trial_of_size
      (x := seedInput sk.seed) (by rw [size_seedInput]; decide)) hcache hz) fun s c hc => ?_
  refine prEvent_run'_romImpl_bind_le _ _ _ _ (fun z hz =>
    cache_eq_none_of_mem_support_run_romImpl (isQueryBoundP_bind_zero _ _
      (seedPrf_isQueryBoundP_trial _ s _ _ _ isDerivationAddress_addrParam)
      fun _ => isQueryBoundP_pure _ _ _) hc hz)
    fun pp c' hc' => prEvent_signDerived_error_le s pp msg c' hc'

/-- From an empty cache, a leanSPHINCS signature fails with probability at most `3 exp(-2^18)`. -/
theorem prEvent_signWith_error_le_empty (sk : SecretKey) (msg : Message) :
    Pr{let z ← (simulateQ XmssSecurity.HashSpec.romImpl
      (signWith H sk msg)).run' ∅}[z.isOk = false]
      ≤ 3 * ENNReal.ofReal (Real.exp (-(2 ^ 18))) :=
  prEvent_signWith_error_le sk msg ∅ fun _ _ => rfl

end EthLib.Cryptography.Sphincs.Unforgeability
