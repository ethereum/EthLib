module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SigningTargets
import EthLib.Cryptography.Proofs.Wots

/-!
# The cached words selected by both layers of a signature

The leanXMSS draft in "WOTS+C", paragraph "Signing", returns the randomizer of a valid trial.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.PostSigning

open Constants HashSig OracleSpec OracleComp CachedCodeword

/-- The actual serialized trial holds a word that decodes to a codeword. -/
def Selected (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer)
    (cache : HashSpec.QueryCache) : Prop :=
  ∃ w, cache (trialInput pp l e msg rho) = some w ∧ (digits w).isSome

private theorem selected_mono {pp l e msg rho} {C D : HashSpec.QueryCache}
    (seen : Selected pp l e msg rho C) (extends_ : C ≤ D) : Selected pp l e msg rho D := by
  obtain ⟨w, cached, valid⟩ := seen
  exact ⟨w, extends_ cached, valid⟩

local notation "hashWorld" => queryH (m := OracleComp OracleWorld)

private theorem selected_find (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (C : HashSpec.QueryCache) {z} (hz : z ∈ support
      ((simulateQ HashSpec.romImpl (Internal.findCodeword hashWorld pp l e msg base 0
        MAX_RANDOMIZER_TRIALS)).run C)) {rho x} (found : z.1 = some (rho, x)) :
    Selected pp l e msg rho z.2 := by
  rw [Internal.findCodeword_eq] at hz
  have trial (r : Randomizer) : codeword? <$> messageDigest hashWorld pp l e msg r =
      digits <$> liftM (HashSpec.query (trialInput pp l e msg r)) := by
    simp only [messageDigest, th, queryH, oracleHash]
    rfl
  obtain ⟨_, _, _, _, w, cached, valid⟩ := Wots.exists_cached_of_mem_support_findFirst_romImpl
    (trialRandomizer base) _ _ _ trial _ _ C z hz rho x found
  exact ⟨w, cached, by simp [valid]⟩

/-- A successful one-time signature retains the word at the randomizer it returns. -/
theorem selected_otsSign (pp : PublicParam) (prf : SeedPrf (OracleComp OracleWorld))
    (l : Layer) (e : UInt32) (msg : ByteArray) (C : HashSpec.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl (otsSign hashWorld pp prf l e msg)).run C))
    {rho chains} (found : z.1 = some (rho, chains)) : Selected pp l e msg rho z.2 := by
  unfold otsSign at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨b, _, f, hf, tail⟩ := hz
  cases res : f.1 with
  | none =>
    simp [res] at tail
    subst z
    cases found
  | some pair =>
    obtain ⟨r, x⟩ := pair
    have seen := selected_find pp l e msg b.1 b.2 hf res
    simp only [res, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at tail
    obtain ⟨s, hs, y, hy, last⟩ := tail
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at last
    subst z
    cases found
    exact selected_mono seen ((le_snd_of_mem_support_run_unifFwdImpl_add_withCaching
      uniformSampleImpl _ (z := s) hs).trans (le_snd_of_mem_support_run_unifFwdImpl_add_withCaching
        uniformSampleImpl _ (z := y) hy))

private theorem selected_layer (pp : PublicParam) (prf : SeedPrf (OracleComp OracleWorld))
    (l : Layer) (e : Nat) (msg : ByteArray) (C : HashSpec.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl (signLayer hashWorld pp prf l e msg)).run C))
    {sig : LayerSignature} (found : z.1 = .ok sig) :
    Selected pp l (UInt32.ofNat e) msg sig.randomizer z.2 := by
  unfold signLayer at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨f, hf, tail⟩ := hz
  cases res : f.1 with
  | none =>
    simp [res] at tail
    subst z
    cases found
  | some pair =>
    obtain ⟨rho, chains⟩ := pair
    have seen := selected_otsSign pp prf l (UInt32.ofNat e) msg C hf res
    simp only [res, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at tail
    obtain ⟨path, hp, last⟩ := tail
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at last
    subst z
    cases found
    exact selected_mono seen (le_snd_of_mem_support_run_unifFwdImpl_add_withCaching
      uniformSampleImpl _ (z := path) hp)

private theorem cache_grows {α : Type} {p : OracleComp OracleWorld α}
    {c : HashSpec.QueryCache} {z : α × HashSpec.QueryCache}
    (h : z ∈ support ((simulateQ HashSpec.romImpl p).run c)) : c ≤ z.2 :=
  le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl p h

private theorem pure_result {α : Type} (v : α) (cache : HashSpec.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl
      (pure v : OracleComp OracleWorld α)).run cache)) :
    z = (v, cache) := by
  simpa only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] using hz

private theorem ok_of_map {ε α β : Type} (f : α → β) (r : Except ε α) {y : β}
    (h : r.map f = .ok y) : ∃ x, r = .ok x ∧ f x = y := by
  cases r with
  | error err => cases h
  | ok x => exact ⟨x, rfl, Except.ok.inj h⟩

/-- Both selected message words remain in the final cache of each successful signing run.

The root used here is the one the actual top signature signs. -/
theorem selected_signWithRoot (pp : PublicParam) (prf : SeedPrf (OracleComp OracleWorld))
    (idx : LeafIndex) (msg : Message) (C : HashSpec.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl (signWithRoot hashWorld prf pp idx msg)).run C))
    {sig : Signature} {root : Digest} (found : z.1 = .ok (sig, root)) :
    Selected pp .bottom (UInt32.ofNat sig.leafIndex.toNat) (packBytes msg)
      sig.bottom.randomizer z.2 ∧
    Selected pp .top (UInt32.ofNat (bottomTree sig.leafIndex)) (packBytes root)
      sig.top.randomizer z.2 := by
  unfold signWithRoot at hz
  -- Cache monotonicity applies to any tree builder, without expanding its 65536 leaves.
  generalize build hashWorld pp prf .bottom LAYER_HEIGHT (bottomTree idx) = grow at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨b, hb, tail⟩ := hz
  cases res : b.1 with
  | none =>
    simp [res] at tail
    subst z
    cases found
  | some pair =>
    obtain ⟨rho, chains⟩ := pair
    have bot := selected_otsSign pp prf .bottom _ _ C hb res
    simp only [res, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at tail
    obtain ⟨tree, ht, t, hs, last⟩ := tail
    have builtCache : b.2 ≤ tree.2 := cache_grows (p := grow) (z := tree) ht
    have signedCache : tree.2 ≤ t.2 := cache_grows hs
    have bottomStored := selected_mono bot (builtCache.trans signedCache)
    have closed := pure_result _ t.2 last
    have returned := (congrArg Prod.fst closed).symm.trans found
    have cache : z.2 = t.2 := congrArg Prod.snd closed
    rw [cache]
    obtain ⟨sigTop, top, eq⟩ := ok_of_map _ _ returned
    have high := selected_layer pp prf .top (bottomTree idx) (packBytes tree.1.value) tree.2 hs top
    obtain ⟨sigEq, rootEq⟩ := Prod.mk.inj eq
    rw [← sigEq, ← rootEq]
    exact ⟨bottomStored, high⟩

/-- The two successful notices read their stored words and activate the corresponding digests. -/
theorem active_after_signing (pp : PublicParam) (prf : SeedPrf (OracleComp OracleWorld))
    (idx : LeafIndex) (msg : Message) (C : HashSpec.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HashSpec.romImpl (signWithRoot hashWorld prf pp idx msg)).run C))
    {sig : Signature} {root : Digest} (found : z.1 = .ok (sig, root))
    (old : (Layer × UInt32) → Option Digest) :
    let bottom := trialInput pp .bottom (UInt32.ofNat sig.leafIndex.toNat)
      (packBytes msg) sig.bottom.randomizer
    let top := trialInput pp .top (UInt32.ofNat (bottomTree sig.leafIndex))
      (packBytes root) sig.top.randomizer
    let targets := record pp top z.2 (record pp bottom z.2 old)
    ∃ wb wt, z.2 bottom = some wb ∧ z.2 top = some wt ∧
      targets (.bottom, UInt32.ofNat sig.leafIndex.toNat) = some (low bottom wb) ∧
      targets (.top, UInt32.ofNat (bottomTree sig.leafIndex)) = some (low top wt) := by
  obtain ⟨⟨wb, hb, vb⟩, ⟨wt, ht, vt⟩⟩ := selected_signWithRoot pp prf idx msg C hz found
  refine ⟨wb, wt, hb, ht, ?_, ?_⟩ <;>
    simp [record, messageKey_trial, hb, ht, vb, vt, Function.update]

/-- Both registrations update only the targets, in the order the signer reports them. -/
theorem notify_ok_run (pp : PublicParam) (msg : Message) (sig : Signature) (root : Digest)
    (s : WatchState) :
    let bottom := trialInput pp .bottom (UInt32.ofNat sig.leafIndex.toNat)
      (packBytes msg) sig.bottom.randomizer
    let top := trialInput pp .top (UInt32.ofNat (bottomTree sig.leafIndex))
      (packBytes root) sig.top.randomizer
    (simulateQ (randomOracle.Targets.impl (record pp) (messageKey pp) low)
      (notify pp msg (.ok (sig, root)))).run s =
      pure (.ok sig, {s with target :=
        record pp top s.cache (record pp bottom s.cache s.target)}) := by
  simp only [notify, simulateQ_bind, simulateQ_HasQuery_query, StateT.run_bind, simulateQ_pure,
    StateT.run_pure]
  simp [randomOracle.Targets.impl, StateT.run]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.PostSigning
