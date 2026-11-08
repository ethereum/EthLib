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
      -- The additional data is 16 + 23 + 24 bytes, and the message is empty.
      cases hh : p.header.encode with
      | error err => simp [Packet.encode, hh, bind, Except.bind] at hb
      | ok header =>
        have hlen := Header.length_encode hh
        have hsize := Packet.size_messageAd_add hb ha
        subst hp
        simp only [Authdata.encode, List.length_append, Vector.length_toList,
          Base.natToBytes_length] at hlen
        have hadSize := ha
        simp only [Packet.messageAd, hh, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at hadSize
        have h63 : packetBytes.size = 63 := by
          rw [← hsize, ← hadSize]
          simp only [ByteArray.size, List.size_toArray, List.length_append, Vector.length_toList,
            hlen]
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
  obtain ⟨message, hdec, hopen⟩ :=
    openPacket_sealPacket (decryptionError := SessionError.decryption) h (by simp [Authdata.flag])
  simp only [openMessage, hdec, hkey, hopen, Except.mapError, bind, Except.bind, pure, Except.pure]

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Discv5.SessionError.code_injective
    (e₁ e₂ : SessionError) (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [SessionError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Discv5.Session
