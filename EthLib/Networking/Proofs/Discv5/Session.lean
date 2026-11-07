module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Networking.Discv5.Session
public import EthLib.Networking.Proofs.Discv5.Packet

/-!
# `Networking.Proofs.Discv5.Session`

The WHOAREYOU challenge and the ordinary message packet read back.

- A WHOAREYOU packet has 63 bytes, the smallest packet.
- Node A reads the challenge of node B back, with the challenge data that node B keeps.
- Node B reads an ordinary message packet of node A back, under its key.
- Two errors with one code come from one constructor.

The theorems say nothing about the freshness of a nonce, an ID nonce or an `enr-seq`.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Discv5.Session

open EthLib.Networking.Discv5
open EthLib.Networking.Proofs.Discv5.Packet
open EthLib.Cryptography

/-! ## Sizes -/

/-- The unmasked header is the 23 bytes of the static header, then the authdata. -/
theorem length_of_header_encode {h : Header} {bytes : List UInt8} (he : h.encode = .ok bytes) :
    bytes.length = 23 + h.authdata.encode.length := by
  unfold Header.encode at he
  dsimp only at he
  split at he
  · cases he
    simp [PROTOCOL_ID, VERSION, Base.natToBytes_length]
    omega
  · cases he

/-- A packet is the masking IV, the unmasked header and the message, in size. -/
theorem size_of_encode {destId : NodeId} {p : Packet} {bytes : ByteArray} {header : List UInt8}
    (he : p.encode destId = .ok bytes) (hh : p.header.encode = .ok header) :
    bytes.size = 16 + header.length + p.message.size := by
  obtain ⟨header', hh', rfl, -⟩ := Packet.encode_eq_ok he
  obtain ⟨iv, h, msg⟩ := p
  obtain rfl : header' = header := Except.ok.inj (hh'.symm.trans hh)
  simp only [ByteArray.size, List.size_toArray, List.length_append, Vector.length_toList,
    length_mask, Array.length_toList]

/-! ## The WHOAREYOU challenge -/

/-- Node A reads node B's WHOAREYOU packet back, with the challenge data that node B keeps.

A WHOAREYOU packet has exactly 63 bytes, within the size limits of a packet. -/
theorem readWhoareyou_makeWhoareyou {nodeIdA : NodeId} {maskingIv : Vector UInt8 16}
    {nonce : Vector UInt8 12} {idNonce : Vector UInt8 16} {enrSeq : UInt64}
    {bytes challengeData : ByteArray}
    (h : makeWhoareyou nodeIdA maskingIv nonce idNonce enrSeq = .ok (bytes, challengeData)) :
    bytes.size = 63 ∧
      readWhoareyou nodeIdA bytes = .ok ⟨nonce, idNonce, enrSeq, challengeData⟩ := by
  unfold makeWhoareyou at h
  generalize hp : (⟨maskingIv, ⟨nonce, .whoareyou idNonce enrSeq⟩, .empty⟩ : Packet) = p at h
  cases ha : p.messageAd with
  | error err => simp [ha, Except.mapError, bind, Except.bind] at h
  | ok ad =>
    cases hb : p.encode nodeIdA with
    | error err => simp [ha, hb, Except.mapError, bind, Except.bind] at h
    | ok packetBytes =>
      simp only [ha, hb, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      -- The header has 23 + 24 bytes, and the message is empty.
      cases hh : p.header.encode with
      | error err => simp [Packet.encode, hh, bind, Except.bind] at hb
      | ok header =>
        have hlen := length_of_header_encode hh
        have hsize := size_of_encode hb hh
        subst hp
        simp only [Authdata.encode, List.length_append, Vector.length_toList,
          Base.natToBytes_length] at hlen
        have h63 : packetBytes.size = 63 := by
          rw [hsize, hlen]
          rfl
        refine ⟨h63, ?_⟩
        have hdec := Packet.decode_encode hb (fun _ => rfl)
        simp only [readWhoareyou, hdec, ha, Except.mapError, bind, Except.bind, pure,
          Except.pure]

/-! ## Ordinary message packets -/

/-- Node B reads node A's ordinary message packet back, under the session key of node A.

Node B must hold the same key for the ID of node A. -/
theorem openMessage_sealMessage {key : Aes.Key .aes128} {nodeIdA nodeIdB : NodeId}
    {maskingIv : Vector UInt8 16} {nonce : Vector UInt8 12} {plaintext bytes : ByteArray}
    {keyOf : NodeId → Option (Aes.Key .aes128)}
    (h : sealMessage key nodeIdA nodeIdB maskingIv nonce plaintext = .ok bytes)
    (hkey : keyOf nodeIdA = some key) :
    openMessage keyOf nodeIdB bytes = .ok (nodeIdA, plaintext) := by
  unfold sealMessage at h
  generalize hheader : (⟨nonce, .message nodeIdA⟩ : Header) = header at h
  cases ha : Packet.messageAd ⟨maskingIv, header, .empty⟩ with
  | error err => simp [ha, Except.mapError, bind, Except.bind] at h
  | ok ad =>
    cases hm : encryptMessage key nonce plaintext ad with
    | error err => simp [ha, hm, Except.mapError, bind, Except.bind] at h
    | ok message =>
      simp only [ha, hm, Except.mapError, bind, Except.bind] at h
      cases hb : Packet.encode nodeIdB ⟨maskingIv, header, message⟩ with
      | error err => simp [hb] at h
      | ok packetBytes =>
        simp only [hb, Except.ok.injEq] at h
        subst h
        have hdec := Packet.decode_encode hb (by
          intro hflag
          rw [← hheader] at hflag
          simp [Authdata.flag] at hflag)
        -- The additional data depends only on the masking IV and the header.
        have had : Packet.messageAd ⟨maskingIv, header, message⟩ = .ok ad := by
          simpa [Packet.messageAd] using ha
        subst hheader
        simp only [openMessage, hdec, hkey, had, decryptMessage_encryptMessage hm,
          Except.mapError, bind, Except.bind, pure, Except.pure]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Discv5.SessionError.code_injective
    (e₁ e₂ : SessionError) (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [SessionError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Discv5.Session
