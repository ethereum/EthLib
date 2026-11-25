module

public import EthLib.Networking.ReqResp.Bounds
public import EthLib.Networking.Proofs.ReqResp.Encoding
public import EthLib.Serialization.Proofs.Ssz.Codec.Bounds

/-!
# `Networking.Proofs.ReqResp.Bounds`

The length bounds of a payload of an SSZ type hold the encodings of that type.

- A payload that decodes at the bounds of a type has a length within the type's bounds.
- An encoding of a value that fits the type, within the payload cap, decodes at those bounds.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.ReqResp.Bounds

open EthLib.Networking.ReqResp
open EthLib.Networking.Proofs.ReqResp.Encoding
open EthLib.Serialization.Ssz

/-- The smallest length of a type, held to one byte past a cap below 2^63. -/
theorem toNat_payloadBounds_fst {maxPayloadSize : UInt64} (hcap : maxPayloadSize.toNat < 2 ^ 63)
    (shape : Desc) :
    (payloadBounds maxPayloadSize shape).1.toNat =
      min shape.minSize (maxPayloadSize.toNat + 1) := by
  simp only [payloadBounds]
  rw [UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]

/-- The largest length of a type, held to the cap. -/
theorem toNat_payloadBounds_snd (maxPayloadSize : UInt64) (shape : Desc) :
    (payloadBounds maxPayloadSize shape).2.toNat =
      min (shape.maxSize.getD maxPayloadSize.toNat) maxPayloadSize.toNat := by
  simp only [payloadBounds]
  rw [UInt64.toNat_ofNat_of_lt' (by have := maxPayloadSize.toNat_lt; unfold UInt64.size; omega)]

/-- A payload that decodes at the bounds of a type has a length within the type's bounds. -/
theorem withinBounds_of_decodePayload {maxPayloadSize : UInt64} {shape : Desc} {bs d : ByteArray}
    (hcap : maxPayloadSize.toNat < 2 ^ 63)
    (h : decodePayload maxPayloadSize (payloadBounds maxPayloadSize shape).1
      (payloadBounds maxPayloadSize shape).2 bs = .ok d) :
    shape.minSize ≤ d.size ∧ ∀ bound, shape.maxSize = some bound → d.size ≤ bound := by
  obtain ⟨hhigh, hlow, -⟩ := (decodePayload_eq_ok_iff hcap).mp h
  have hmin : (min (payloadBounds maxPayloadSize shape).2 maxPayloadSize).toNat ≤
      (payloadBounds maxPayloadSize shape).2.toNat := by
    rw [UInt64.min_def]
    split
    · exact Nat.le_refl _
    · rename_i hle
      exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle))
  rw [toNat_payloadBounds_fst hcap] at hlow
  rw [toNat_payloadBounds_snd] at hmin
  refine ⟨?_, fun bound hb => ?_⟩
  · -- A smallest size past the cap would leave no length, so the bound is the smallest size.
    omega
  · rw [hb, Option.getD_some] at hmin
    omega

/-- An encoding of a value that fits its type, within the payload cap, decodes at its bounds. -/
theorem decodePayload_encodePayload_of_serialize {maxPayloadSize : UInt64} {shape : Desc}
    {value : Value} {bytes : Bytes} (hcap : maxPayloadSize.toNat < 2 ^ 63)
    (fits : Fits shape value) (wrote : serialize shape value = .ok bytes)
    (within : bytes.size ≤ maxPayloadSize.toNat) :
    decodePayload maxPayloadSize (payloadBounds maxPayloadSize shape).1
      (payloadBounds maxPayloadSize shape).2 (encodePayload bytes) = .ok bytes := by
  obtain ⟨hlow, hhigh⟩ := withinBounds_of_serialize fits wrote
  apply decodePayload_encodePayload hcap
  · exact within
  · rw [toNat_payloadBounds_snd]
    show bytes.size ≤ _
    cases hm : shape.maxSize with
    | none => simp only [Option.getD_none, Nat.min_self]; exact within
    | some m =>
      have := hhigh m hm
      simp only [Option.getD_some]
      omega
  · rw [toNat_payloadBounds_fst hcap]
    show _ ≤ bytes.size
    omega

end EthLib.Networking.Proofs.ReqResp.Bounds
