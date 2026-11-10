module

public import EthLib.Networking.Libp2p.Mplex
public import EthLib.Networking.Proofs.Encoding.Uvarint

/-!
# Proofs: mplex frames

- Decoding reads back a valid frame from its encoding, whatever bytes follow it.
- The decoder accepts only these encodings, and only valid frames.
- Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.Mplex

open EthLib.Networking.Encoding
open EthLib.Networking.Libp2p.Mplex

/-- Reading back the value of a flag gives the flag. -/
theorem Flag.ofNat?_toNat (flag : Flag) : Flag.ofNat? flag.toNat = some flag := by
  cases flag <;> rfl

/-- A value that names a flag is that flag's value. -/
theorem Flag.toNat_of_ofNat? {n : Nat} {flag : Flag} (h : Flag.ofNat? n = some flag) :
    flag.toNat = n := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> simp [Flag.ofNat?] at h <;> subst h <;> rfl

/-- The value of a flag is below 7. -/
private theorem Flag.toNat_lt (flag : Flag) : flag.toNat < 7 := by
  cases flag <;> decide

/-- The header of a stream ID below the bound and a flag is below the unsigned varint bound. -/
private theorem header_lt {streamId : Nat} (h : streamId < streamIdBound) (flag : Flag) :
    8 * streamId + flag.toNat < Uvarint.bound := by
  have := Flag.toNat_lt flag
  simp only [streamIdBound] at h
  simp only [Uvarint.bound]
  omega

/-- A header splits back into its stream ID and its flag. -/
private theorem header_split (streamId : Nat) (flag : Flag) :
    (8 * streamId + flag.toNat) % 8 = flag.toNat ∧ (8 * streamId + flag.toNat) / 8 = streamId := by
  have := Flag.toNat_lt flag
  omega

/-- Decoding the encoding of a valid frame, then any bytes, returns the frame and those bytes. -/
theorem decode_encode {frame : Frame} (h : frame.Valid) (rest : List UInt8) :
    decode (encode frame ++ rest) = .ok (frame, rest) := by
  obtain ⟨hs, hd, he⟩ := h
  have hhb := header_lt hs frame.flag
  obtain ⟨hm, hq⟩ := header_split frame.streamId frame.flag
  have hsz : frame.data.size < Uvarint.bound := by
    have : maxData < Uvarint.bound := by decide
    omega
  have hl : frame.data.data.toList.length = frame.data.size :=
    Array.length_toList
  have hass : encode frame ++ rest = Uvarint.encode (8 * frame.streamId + frame.flag.toNat) ++
      (Uvarint.encode frame.data.size ++ (frame.data.data.toList ++ rest)) := by
    simp [encode]
  have hnd : ¬ (frame.flag.ends ∧ frame.data.size ≠ 0) := fun ⟨h1, h2⟩ => h2 (he h1)
  have hnt : ¬ maxData < frame.data.size := Nat.not_lt.mpr hd
  have hnr : ¬ frame.data.data.toList.length < frame.data.size := by omega
  have hr : (frame.data.data.toList ++ rest).take frame.data.size = frame.data.data.toList := by
    rw [← hl]; simp
  have hdr : (frame.data.data.toList ++ rest).drop frame.data.size = rest := by
    rw [← hl]; simp
  have hba : (⟨frame.data.data.toList.toArray⟩ : ByteArray) = frame.data := by
    cases frame.data
    rfl
  rw [hass]
  simp only [decode]
  rw [EthLib.Networking.Proofs.Encoding.Uvarint.decode_encode hhb]
  simp only [bind, Except.bind, Except.mapError, hm, Flag.ofNat?_toNat]
  rw [EthLib.Networking.Proofs.Encoding.Uvarint.decode_encode hsz]
  simp only [hnt, hnd, hnr, hr, hdr, hq, hba, ite_false, pure, Except.pure]

/-- A decoded frame is valid, and the input is its encoding followed by the rest. -/
theorem encode_decode {bytes rest : List UInt8} {frame : Frame}
    (h : decode bytes = .ok (frame, rest)) : frame.Valid ∧ encode frame ++ rest = bytes := by
  simp only [decode] at h
  cases hd : Uvarint.decode bytes with
  | error e => simp [hd, bind, Except.bind, Except.mapError] at h
  | ok p =>
    obtain ⟨hdr, r0⟩ := p
    obtain ⟨hH, hb⟩ := EthLib.Networking.Proofs.Encoding.Uvarint.encode_decode hd
    simp only [hd, bind, Except.bind, Except.mapError] at h
    cases hf : Flag.ofNat? (hdr % 8) with
    | none => simp [hf, throw, throwThe, MonadExceptOf.throw] at h
    | some flag =>
      simp only [hf] at h
      cases hd2 : Uvarint.decode r0 with
      | error e => simp [hd2] at h
      | ok q =>
        obtain ⟨L, r1⟩ := q
        obtain ⟨hL, hb2⟩ := EthLib.Networking.Proofs.Encoding.Uvarint.encode_decode hd2
        simp only [hd2] at h
        by_cases h1 : maxData < L
        · simp [h1, throw, throwThe, MonadExceptOf.throw] at h
        by_cases h2 : flag.ends = true ∧ L ≠ 0
        · simp [h1, h2, throw, throwThe, MonadExceptOf.throw] at h
        by_cases h3 : (r1.take L).length < L
        · simp only [h1, h2, h3, ↓reduceIte] at h; cases h
        simp only [h1, h2, h3, ite_false, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hn := Flag.toNat_of_ofNat? hf
        have hl : (List.take L r1).length = L := by
          have := List.length_take_le L r1; omega
        have hba : (⟨(List.take L r1).toArray⟩ : ByteArray).size = L := by
          show (List.take L r1).toArray.size = L
          rw [List.size_toArray]; exact hl
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · simp only [streamIdBound]; simp only [Uvarint.bound] at hH; omega
        · simp only [hba]; omega
        · intro he; simp only [hba]; exact Decidable.byContradiction fun hne => h2 ⟨he, hne⟩
        · simp only [encode, hba, hn]
          have hh : 8 * (hdr / 8) + hdr % 8 = hdr := by omega
          rw [hh, ← hb, ← hb2]
          simp [List.append_assoc]

/-- The decoder accepts exactly the encodings of valid frames, then any bytes. -/
theorem decode_eq_ok_iff {bytes rest : List UInt8} {frame : Frame} :
    decode bytes = .ok (frame, rest) ↔ frame.Valid ∧ encode frame ++ rest = bytes :=
  ⟨encode_decode, fun ⟨hv, he⟩ => he ▸ decode_encode hv rest⟩

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Libp2p.Mplex.MplexError.code_injective
    (e₁ e₂ : MplexError) (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [MplexError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Libp2p.Mplex
