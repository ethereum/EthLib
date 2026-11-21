module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifiedPositions
import VCVio.OracleComp.QueryTracking.RandomOracle.Settled
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifierConflict

/-!
# The candidate's two message-hash queries

The leanXMSS draft verifies the signed message at the bottom layer.

The top layer verifies the recovered bottom root.

See sections "WOTS+C" and "The scheme".

Both full-word calls occur before any remaining graph cells are filled.

The message address keeps their replies in the ordinary public table.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe

open EthLib.Cryptography OracleSpec OracleComp Constants HashSig TwoLayerGraph
open ChainGraph (Word Public)

/-- The byte string hashed to decode this submitted signature's chain positions. -/
@[expose] def messageInput (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature) : ByteArray :=
  thInput pp (addrMsg l (UInt32.ofNat e)) (msg ++ packBytes sig.randomizer)

private theorem first_hash (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature) :
    ∃ rest : Vector UInt8 32 → OracleComp Honest.SharedSpec (Option Digest),
      layerRoot Honest.hash pp l e msg sig = Honest.hash (messageInput pp l e msg sig)
        >>= rest := by
  simp only [layerRoot, otsLeaf, messageDigest, th, bind_assoc, pure_bind]
  exact ⟨_, rfl⟩

private theorem input_ne (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature)
    (r : Role) (vs : List Word) : input pp r vs ≠ (messageInput pp l e msg sig).data.toList := by
  intro eq
  have addr := (thInput_inj (ByteArray.ext (Array.toList_inj.mp eq))).2.1
  obtain ⟨layer, role⟩ := r
  cases role <;> exact encodeAddress_ne_of_type_ne _ _ _ _ _ _ (by decide) addr

/-- The layer's first full hash call returned these two words.

The ordinary table still holds both answers at the stated observation point.
-/
def ReadTrial (pp : PublicParam) (b : ByteArray) (start : Honest.SharedState × List Cell)
    (later : Honest.SharedState) : Prop :=
  ∃ (lo hi : Word) (middle after : Honest.SharedState × List Cell),
    (lo, middle) ∈ support (((graph pp).deferredImpl (.inl (.inl (.inr
      (.inl b.data.toList))))).run start) ∧
    (hi, after) ∈ support (((graph pp).deferredImpl (.inl (.inl (.inr
      (.inr b.data.toList))))).run middle) ∧
    after.1 ≤ later ∧ later.1 (.inl b.data.toList) = some lo ∧
      later.1 (.inr b.data.toList) = some hi

private theorem layer_trial (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature)
    {result : Option Digest} {start finish : Honest.SharedState × List Cell}
      {later : Honest.SharedState}
    (run : (result, finish) ∈ support ((simulateQ (graph pp).deferredImpl
      (layerRoot Honest.hash pp l e msg sig)).run start))
    (ext : finish.1 ≤ later) : ReadTrial pp (messageInput pp l e msg sig) start later := by
  obtain ⟨rest, begins⟩ := first_hash pp l e msg sig
  rw [begins, Honest.hash] at run
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_HasQuery_query, StateT.run_bind,
    mem_support_bind_iff] at run
  obtain ⟨⟨lo, mid⟩, low, ⟨hi, after⟩, high, tail⟩ := run
  have after_le := ((graph pp).le_of_mem_support_simulateQ_deferredImpl _ tail).trans ext
  have mid_le := ((graph pp).le_of_mem_support_deferredImpl high).trans after_le
  have disjoint := input_ne pp l e msg sig
  refine ⟨lo, hi, mid, after, low, high, after_le, mid_le.1 ?_, after_le.1 ?_⟩
  · apply (graph pp).fst_apply_of_mem_support_deferredImpl_pub _ low
    rintro (r | r) vs
    · exact fun h => disjoint r vs (Sum.inl.inj h)
    · intro h
      cases h
  · apply (graph pp).fst_apply_of_mem_support_deferredImpl_pub _ high
    rintro (r | r) vs
    · intro h
      cases h
    · exact fun h => disjoint r vs (Sum.inr.inj h)


/-- The signed digest is exactly the low 16 bytes of the ordinary public reply at the trial.

This reads the physical row even if an unrelated graph point conflicted.
-/
theorem digest_of_trial (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature)
    {start : Honest.SharedState × List Cell} {later : Honest.SharedState}
    (read : ReadTrial pp (messageInput pp l e msg sig) start later) :
    ∃ lo : Word, later.1 (.inl (messageInput pp l e msg sig).data.toList) = some lo ∧
      messageDigest (hashAt pp later) pp l (UInt32.ofNat e) msg sig.randomizer
        = some (ofBV 16 lo) := by
  obtain ⟨lo, hi, _, _, _, _, _, low, high⟩ := read
  refine ⟨lo, low, ?_⟩
  let b := (messageInput pp l e msg sig).data.toList
  have ordinary (row : Public.Domain) (outside : ∀ k vs, (graph pp).pt k vs ≠ row) :
      (graph pp).merge later row = later.1 row :=
    (graph pp).merge_apply_of_not_exists (fun ⟨k, vs, _, eq⟩ => outside k vs eq)
  have lo_read : (graph pp).merge later (.inl b) = some lo := by
    apply Eq.trans (ordinary _ _) low
    rintro (r | r) vs h
    · exact input_ne pp l e msg sig r vs (Sum.inl.inj h)
    · cases h
  have hi_read : (graph pp).merge later (.inr b) = some hi := by
    apply Eq.trans (ordinary _ _) high
    rintro (r | r) vs h
    · cases h
    · exact input_ne pp l e msg sig r vs (Sum.inr.inj h)
  simp only [messageDigest, th, hashAt, halvesHash, simulateQ_bind, simulateQ_HasQuery_query,
    simulateQ_pure, QueryCache.toPartialImpl_apply]
  change (Option.bind ((graph pp).merge later (.inl b)) (fun x =>
      Option.bind ((graph pp).merge later (.inr b)) (fun y =>
        some (ofOutput (PairedHashWord.halves.symm (x,y)))))
    >>= fun w => some (halfOf 0 w)) = some _
  rw [lo_read, hi_read]
  simp [PairedHashWord.first_half_bytes]

/-- Recover the complete physical word used by the verifier from the ordinary public table. -/
theorem word_of_trial (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature)
    {start : Honest.SharedState × List Cell} {later : Honest.SharedState}
    (read : ReadTrial pp (messageInput pp l e msg sig) start later) :
    ∃ w : HashOutput, PairedHashWord.joinCache later.1 (messageInput pp l e msg sig).data.toList
      = some w ∧
      messageDigest (hashAt pp later) pp l (UInt32.ofNat e) msg sig.randomizer
        = some (halfOf 0 (ofOutput w)) := by
  obtain ⟨d, hd, digest⟩ := digest_of_trial pp l e msg sig read
  obtain ⟨lo, hi, _, _, _, _, _, low, high⟩ := read
  obtain rfl := Option.some.inj (low.symm.trans hd)
  refine ⟨PairedHashWord.halves.symm (lo, hi), ?_, ?_⟩
  · simp [PairedHashWord.joinCache, RandomOraclePairedValue.joinCache, low, high]
  · rw [PairedHashWord.first_half_bytes, Equiv.apply_symm_apply]
    exact digest

/-- The accepting verifier calls the bottom hash on the submitted message.

It then calls the top hash on the bottom root from that same run.

A cache hit still counts as a query.
-/
theorem accepted_trials (pk : PublicKey) (msg : Message) (sig : Xmss.Signature)
    (start finish : Honest.SharedState × List Cell)
    (run : (true, finish) ∈ support ((simulateQ (graph pk.publicParam).deferredImpl
      (verifyWith Honest.hash pk msg sig)).run start)) :
    ∃ (b : Digest) (middle : Honest.SharedState × List Cell),
      (some b, middle) ∈ support ((simulateQ (graph pk.publicParam).deferredImpl
        (layerRoot Honest.hash pk.publicParam .bottom sig.leafIndex.toNat
          (packBytes msg) sig.bottom)).run start) ∧
      ReadTrial pk.publicParam (messageInput pk.publicParam .bottom sig.leafIndex.toNat
        (packBytes msg) sig.bottom)
        start finish.1 ∧
      ReadTrial pk.publicParam (messageInput pk.publicParam .top (bottomTree sig.leafIndex)
        (packBytes b) sig.top)
        middle finish.1 := by
  obtain ⟨b, middle, bot, top, ext⟩ := verifier_layers pk msg sig start finish run
  exact ⟨b, middle, bot, layer_trial _ _ _ _ _ bot ext, layer_trial _ _ _ _ _ top le_rfl⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe
