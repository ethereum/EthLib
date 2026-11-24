module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.ConcreteStatement
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.RandomizedStatement

/-!
# Proofs: EthLib's adversary is one of the model's

An adversary of EthLib's game speaks bytes, and the model speaks bit vectors.

So its requests, the answers it gets and its forgery are translated.

```text
    request (idx, m)          ->  model request (idx, m as a 256-bit vector)
    model answer sigma        ->  EthLib signature at idx
    forgery (m*, sigma*)      ->  model forgery (idx of sigma*, m*, sigma*)
```

A value from the adversary goes to the model through its integer, and comes back as its bytes.

The round trips hold in both directions.

So the translated transcripts and forgeries win exactly when the originals do.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-! ## From bytes to bit vectors -/

/-- A leaf index as the model writes it. -/
def toLeafIndex (idx : LeafIndex) : XmssSecurity.LeafIndex :=
  ⟨idx.toNat, by simpa [XmssSecurity.lifetime, XmssSecurity.treeHeight] using idx.toNat_lt⟩

/-- A message as the model writes it: the integer of its four lanes, the first least significant. -/
def toMessage (msg : Message) : XmssSecurity.Message :=
  BitVec.ofNat _ (msg.w0.toNat + 2 ^ 64 * msg.w1.toNat + 2 ^ 128 * msg.w2.toNat
    + 2 ^ 192 * msg.w3.toNat)

/-- A randomizer as the model writes it: the integer of its two lanes. -/
def toRandomness (r : Randomizer) : XmssSecurity.Randomness :=
  BitVec.ofNat _ (r.toNat)

/-- One layer's signature as the model writes it. -/
def toLayerSig (s : LayerSignature) : XmssSecurity.LayerSignature where
  randomness := toRandomness s.randomizer
  chainValue i := toDigest s.chainValues[i.val]
  authPath l := toDigest s.path[l.val]

/-- A signature as the model writes it, its leaf index left out. -/
def toSignature (σ : Signature) : XmssSecurity.Signature where
  randomness := toRandomness σ.bottom.randomizer
  chainValue i := toDigest σ.bottom.chainValues[i.val]
  authPath l := toDigest σ.bottom.path[l.val]
  top := toLayerSig σ.top

@[simp] theorem ofLeafIndex_toLeafIndex (idx : LeafIndex) :
    ofLeafIndex (toLeafIndex idx) = idx := by
  apply UInt32.toNat.inj
  simp [toLeafIndex]

@[simp] theorem toLeafIndex_ofLeafIndex (idx : XmssSecurity.LeafIndex) :
    toLeafIndex (ofLeafIndex idx) = idx := by
  apply Fin.ext
  simp [toLeafIndex]

@[simp] theorem ofMessage_toMessage (msg : Message) : ofMessage (toMessage msg) = msg := by
  obtain ⟨w0, w1, w2, w3⟩ := msg
  have := w0.toNat_lt
  have := w1.toNat_lt
  have := w2.toNat_lt
  have := w3.toNat_lt
  simp only [ofMessage, HashSig.ofOutputLanes, toMessage, XmssSecurity.messageBits,
    EthLib.Cryptography.Hash.Keccak.Lanes4.mk.injEq]
  -- Lane `k` is bits `64k` to `64k + 63` of the integer, which is that lane's own value.
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt64.toNat_inj.mp <;>
    simp only [UInt64.toNat_ofBitVec, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] <;> omega

/-- The four 64-bit pieces of a 256-bit vector are the base-`2^64` digits of its integer. -/
private theorem toNat_pieces (x : BitVec 256) :
    (x.extractLsb' 0 64).toNat + 2 ^ 64 * (x.extractLsb' 64 64).toNat
      + 2 ^ 128 * (x.extractLsb' 128 64).toNat + 2 ^ 192 * (x.extractLsb' 192 64).toNat
      = x.toNat := by
  have := x.isLt
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

@[simp] theorem toMessage_ofMessage (msg : XmssSecurity.Message) :
    toMessage (ofMessage msg) = msg := by
  apply BitVec.eq_of_toNat_eq
  simp only [toMessage, ofMessage, HashSig.ofOutputLanes, UInt64.toNat_ofBitVec,
    BitVec.toNat_ofNat]
  exact (congrArg (· % 2 ^ XmssSecurity.messageBits) (toNat_pieces msg)).trans
    (Nat.mod_eq_of_lt msg.isLt)

@[simp] theorem ofRandomizer_toRandomness (r : Randomizer) :
    ofRandomizer (toRandomness r) = r := by
  apply Hash.Keccak.Lanes2.bytes_injective
  rw [HashSig.bytes_ofDigestLanes, toRandomness, Hash.Keccak.Lanes2.bytes_eq_toLE,
    ← ofBV_ofNat_ofLE (Base.ByteOrder.toLE 16 (r.toNat)) (w := XmssSecurity.randomnessBits)
      (by simp [XmssSecurity.randomnessBits]),
    Base.ByteOrder.ofLE_toLE, Nat.mod_eq_of_lt (by simpa using Hash.Keccak.Lanes2.toNat_lt r)]

@[simp] theorem toRandomness_ofRandomizer (r : XmssSecurity.Randomness) :
    toRandomness (ofRandomizer r) = r :=
  HashSig.ofDigestLanes_injective (ofRandomizer_toRandomness _)

@[simp] theorem ofLayerSig_toLayerSig (s : LayerSignature) : ofLayerSig (toLayerSig s) = s := by
  obtain ⟨rho, y, pi⟩ := s
  simp only [ofLayerSig, toLayerSig, ofRandomizer_toRandomness, LayerSignature.mk.injEq, true_and]
  refine ⟨Vector.ext fun i hi => ?_, Vector.ext fun i hi => ?_⟩
  · simp [ofChains, chainOf]
  · simp [ofPath]

@[simp] theorem toLayerSig_ofLayerSig (s : XmssSecurity.LayerSignature) :
    toLayerSig (ofLayerSig s) = s := by
  obtain ⟨rho, y, pi⟩ := s
  simp only [ofLayerSig, toLayerSig, toRandomness_ofRandomizer,
    XmssSecurity.LayerSignature.mk.injEq, true_and]
  refine ⟨funext fun i => ?_, funext fun l => ?_⟩
  · simp [ofChains, chainOf]
  · simp [ofPath]

/-- A signature is EthLib's translation of its model signature, at its own leaf index. -/
@[simp] theorem ofSignature_toSignature (σ : Signature) :
    ofSignature (toLeafIndex σ.leafIndex) (toSignature σ) = σ := by
  obtain ⟨idx, bottom, top⟩ := σ
  simp only [ofSignature, toSignature, ofLeafIndex_toLeafIndex, ofLayerSig_toLayerSig,
    Signature.mk.injEq, true_and, and_true]
  exact ofLayerSig_toLayerSig bottom

@[simp] theorem toSignature_ofSignature (idx : XmssSecurity.LeafIndex)
    (σ : XmssSecurity.Signature) : toSignature (ofSignature idx σ) = σ := by
  obtain ⟨rho, y, pi, top⟩ := σ
  have h := toLayerSig_ofLayerSig ⟨rho, y, pi⟩
  simp only [toLayerSig, XmssSecurity.LayerSignature.mk.injEq] at h
  simp only [toSignature, ofSignature, toLayerSig_ofLayerSig, XmssSecurity.Signature.mk.injEq,
    and_true]
  exact h

theorem ofLeafIndex_injective : Function.Injective ofLeafIndex := fun a b h => by
  rw [← toLeafIndex_ofLeafIndex a, h, toLeafIndex_ofLeafIndex]

theorem ofMessage_eq_iff (x : XmssSecurity.Message) (msg : Message) :
    ofMessage x = msg ↔ x = toMessage msg :=
  ⟨fun h => by rw [← h, toMessage_ofMessage], fun h => by rw [h, ofMessage_toMessage]⟩

/-- A model signature at `idx` is an EthLib signature exactly when both its parts agree. -/
theorem ofSignature_eq_iff (idx : XmssSecurity.LeafIndex) (σ : XmssSecurity.Signature)
    (τ : Signature) :
    ofSignature idx σ = τ ↔ idx = toLeafIndex τ.leafIndex ∧ σ = toSignature τ := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨rfl, rfl⟩
    exact ofSignature_toSignature τ

/-! ## The adversary -/

/-- A request as the model writes it. -/
def toModelRequest (request : SignRequest) : XmssSecurity.SignRequest :=
  ⟨toLeafIndex request.leafIndex, toMessage request.message⟩

/-- A forgery as the model writes it: the signature's leaf index moves to the claim. -/
def toModelForgery (forgery : Forgery) : XmssSecurity.Forgery :=
  ⟨toLeafIndex forgery.signature.leafIndex, toMessage forgery.message,
    toSignature forgery.signature⟩

/-- The adversary's oracles, answered by the model's.

Hash queries and coins pass through.

Each request is translated, and so is each signature it returns. -/
def adversaryImpl :
    QueryImpl (XmssSecurity.OracleWorld + SigningSpec)
      (OracleComp (XmssSecurity.OracleWorld + XmssSecurity.SigningSpec))
  | .inl input => liftM ((XmssSecurity.OracleWorld + XmssSecurity.SigningSpec).query (.inl input))
  | .inr request => Option.map (ofSignature (toLeafIndex request.leafIndex)) <$>
      liftM ((XmssSecurity.OracleWorld + XmssSecurity.SigningSpec).query
        (.inr (toModelRequest request)))

/-- EthLib's adversary as one of the model's games. -/
noncomputable def toModelAdversary (adversary : Adversary) : XmssSecurity.Adversary where
  main pk := toModelForgery <$> simulateQ adversaryImpl (adversary.main (ofPublicKey pk))

/-- A transcript entry of the model's game as EthLib's. -/
def ofEntry (entry : (_ : XmssSecurity.SignRequest) × Option XmssSecurity.Signature) :
    (_ : SignRequest) × Option Signature :=
  ⟨⟨ofLeafIndex entry.1.leafIndex, ofMessage entry.1.message⟩,
    entry.2.map (ofSignature entry.1.leafIndex)⟩

/-- The translated transcript repeats a leaf index exactly when the model's does. -/
theorem valid_map (log : QueryLog XmssSecurity.SigningSpec) :
    Valid (log.map ofEntry) ↔ XmssSecurity.SigningTranscript.Valid log := by
  -- The translated leaf indices are the model's, each through an injective conversion.
  have hmap : (log.map ofEntry).map (fun entry => entry.1.leafIndex)
      = (log.map fun entry => entry.1.leafIndex).map ofLeafIndex := by
    simp only [List.map_map]
    rfl
  rw [Valid, hmap, List.nodup_map_iff ofLeafIndex_injective]
  rfl

/-- The translated transcript holds the forgery exactly when the model's holds its translation. -/
theorem contains_map (log : QueryLog XmssSecurity.SigningSpec) (forgery : Forgery) :
    Contains (log.map ofEntry) forgery ↔
      XmssSecurity.SigningTranscript.Contains log (toModelForgery forgery) := by
  simp only [Contains, XmssSecurity.SigningTranscript.Contains, List.mem_map, toModelForgery,
    XmssSecurity.Forgery.request]
  constructor
  · rintro ⟨_, ⟨entry, hentry, rfl⟩, hmessage, hsignature⟩
    obtain ⟨request, answer⟩ := entry
    cases answer with
    | none => simp [ofEntry] at hsignature
    | some signature =>
      simp only [ofEntry, Option.map_some, Option.some.injEq] at hmessage hsignature
      obtain ⟨hidx, hsig⟩ := (ofSignature_eq_iff _ _ _).mp hsignature
      refine ⟨⟨request, some signature⟩, hentry, ?_, congrArg some hsig⟩
      obtain ⟨idx, msg⟩ := request
      simp only at hidx hmessage
      rw [hidx, (ofMessage_eq_iff _ _).mp hmessage]
  · rintro ⟨entry, hentry, hrequest, hsignature⟩
    refine ⟨ofEntry entry, ⟨entry, hentry, rfl⟩, ?_, ?_⟩
    · simp only [ofEntry, hrequest, ofMessage_toMessage]
    · simp only [ofEntry, hsignature, hrequest, Option.map_some, ofSignature_toSignature]

end EthLib.Cryptography.Xmss.Unforgeability
