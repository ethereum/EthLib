module

public import EthLib.Networking.ReqResp.Bounds
public import EthLib.Networking.Proofs.ReqResp.Encoding
public import EthLib.Serialization.Proofs.Ssz.Type.Bounds

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

/-- The payload cap is 10 MiB. -/
theorem toNat_MAX_PAYLOAD_SIZE : MAX_PAYLOAD_SIZE.toNat = 10485760 := rfl

/-- The smallest length of a type, held to one byte past the cap. -/
theorem toNat_payloadBounds_fst (shape : Desc) :
    (payloadBounds shape).1.toNat = min shape.minSize (MAX_PAYLOAD_SIZE.toNat + 1) := by
  simp only [payloadBounds]
  rw [UInt64.toNat_ofNat_of_lt' (by rw [toNat_MAX_PAYLOAD_SIZE]; unfold UInt64.size; omega)]

/-- The largest length of a type, held to the cap. -/
theorem toNat_payloadBounds_snd (shape : Desc) :
    (payloadBounds shape).2.toNat = min (shape.maxSize.getD MAX_PAYLOAD_SIZE.toNat)
      MAX_PAYLOAD_SIZE.toNat := by
  simp only [payloadBounds]
  rw [UInt64.toNat_ofNat_of_lt' (by rw [toNat_MAX_PAYLOAD_SIZE]; unfold UInt64.size; omega)]

/-- A payload that decodes at the bounds of a type has a length within the type's bounds. -/
theorem withinBounds_of_decodePayload {shape : Desc} {bs d : ByteArray}
    (h : decodePayload (payloadBounds shape).1 (payloadBounds shape).2 bs = .ok d) :
    shape.minSize ≤ d.size ∧ ∀ bound, shape.maxSize = some bound → d.size ≤ bound := by
  obtain ⟨hhigh, hlow, -⟩ := decodePayload_eq_ok_iff.mp h
  have hcap : (min (payloadBounds shape).2 MAX_PAYLOAD_SIZE).toNat ≤
      (payloadBounds shape).2.toNat := by
    rw [UInt64.min_def]
    split
    · exact Nat.le_refl _
    · rename_i hle
      exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle))
  rw [toNat_payloadBounds_fst] at hlow
  rw [toNat_payloadBounds_snd] at hcap
  refine ⟨?_, fun bound hb => ?_⟩
  · -- A smallest size past the cap would leave no length, so the bound is the smallest size.
    omega
  · rw [hb, Option.getD_some] at hcap
    omega

/-- An encoding of a value that fits its type, within the payload cap, decodes at its bounds. -/
theorem decodePayload_encodePayload_of_serialize {shape : Desc} {value : Value} {bytes : Bytes}
    (fits : Fits shape value) (wrote : serialize shape value = .ok bytes)
    (hcap : bytes.size ≤ MAX_PAYLOAD_SIZE.toNat) :
    decodePayload (payloadBounds shape).1 (payloadBounds shape).2 (encodePayload ⟨bytes⟩) =
      .ok ⟨bytes⟩ := by
  obtain ⟨hlow, hhigh⟩ := withinBounds_of_serialize fits wrote
  apply decodePayload_encodePayload
  · exact hcap
  · rw [toNat_payloadBounds_snd]
    show bytes.size ≤ _
    cases hm : shape.maxSize with
    | none => simp only [Option.getD_none, Nat.min_self]; exact hcap
    | some m =>
      have := hhigh m hm
      simp only [Option.getD_some]
      omega
  · rw [toNat_payloadBounds_fst]
    show _ ≤ bytes.size
    omega

end EthLib.Networking.Proofs.ReqResp.Bounds
