module

public import EthLib.Networking.Quic.Tls
public import EthLib.Cryptography.Proofs.Hash.Tls13
-- Checking a fixed label's byte length reduces the body of String.toUTF8.
import all Init.Data.String.Defs

/-!
# Proofs: the SHA-256 TLS key schedule

The no-PSK schedule succeeds for every shared secret and pair of transcripts.

Its result is exactly its seven derivations, each by Derive-Secret, Extract or both.

The schedule reads each transcript only through its SHA-256 hash.

These statements do not establish the authenticity of a transcript or a Diffie-Hellman agreement.

Conformance with the RFC rests on the RFC 8448 §3 trace of the Python suite.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open EthLib.Base
open EthLib.Cryptography.Hash
open Tls13 (Secret)

/-- Derive-Secret succeeds for every label within the bounds of RFC 8446 §7.1. -/
theorem deriveSecret_ok (secret : Secret) (label messages : ByteArray)
    (hlabel : 0 < label.size ∧ label.size ≤ 249) :
    ∃ output, deriveSecret secret label messages = .ok output :=
  Tls13.expandLabel_ok _ _ _ _ hlabel (by
    change (Sha256.hash32 messages).toArray.size ≤ 255
    rw [Vector.size_toArray]
    decide) (by decide)

/-- Mixing the shared secret into the no-PSK schedule always succeeds. -/
theorem handshakeSecret_ok (sharedSecret : ByteArray) :
    ∃ output, handshakeSecret sharedSecret = .ok output := by
  obtain ⟨derived, hd⟩ := deriveSecret_ok earlySecret "derived".toUTF8 .empty (by decide)
  refine ⟨Tls13.extract (packBytes derived) sharedSecret, ?_⟩
  simp only [handshakeSecret, hd, bind, Except.bind, pure, Except.pure]

/-- Deriving the master secret always succeeds. -/
theorem masterSecret_ok (handshake : Secret) :
    ∃ output, masterSecret handshake = .ok output := by
  obtain ⟨derived, hd⟩ := deriveSecret_ok handshake "derived".toUTF8 .empty (by decide)
  refine ⟨Tls13.extract (packBytes derived) (packBytes zeros), ?_⟩
  simp only [masterSecret, hd, bind, Except.bind, pure, Except.pure]

/-- The no-PSK schedule computes every secret for every shared secret and transcript pair. -/
theorem keySchedule_ok (sharedSecret helloTranscript serverTranscript : ByteArray) :
    ∃ output, keySchedule sharedSecret helloTranscript serverTranscript = .ok output := by
  obtain ⟨handshake, hh⟩ := handshakeSecret_ok sharedSecret
  obtain ⟨master, hm⟩ := masterSecret_ok handshake
  obtain ⟨ch, hch⟩ := deriveSecret_ok handshake "c hs traffic".toUTF8 helloTranscript (by decide)
  obtain ⟨sh, hsh⟩ := deriveSecret_ok handshake "s hs traffic".toUTF8 helloTranscript (by decide)
  obtain ⟨ca, hca⟩ := deriveSecret_ok master "c ap traffic".toUTF8 serverTranscript (by decide)
  obtain ⟨sa, hsa⟩ := deriveSecret_ok master "s ap traffic".toUTF8 serverTranscript (by decide)
  refine ⟨⟨earlySecret, handshake, master, ch, sh, ca, sa⟩, ?_⟩
  simp only [keySchedule, hh, hm, hch, hsh, hca, hsa, bind, Except.bind, pure, Except.pure]

/-- A schedule returns exactly the early, handshake, master and four labelled traffic secrets. -/
theorem keySchedule_eq_ok_iff (sharedSecret helloTranscript serverTranscript : ByteArray)
    (out : KeySchedule) :
    keySchedule sharedSecret helloTranscript serverTranscript = .ok out ↔
      out.early = earlySecret ∧
      handshakeSecret sharedSecret = .ok out.handshake ∧
      masterSecret out.handshake = .ok out.master ∧
      deriveSecret out.handshake "c hs traffic".toUTF8 helloTranscript =
        .ok out.clientHandshake ∧
      deriveSecret out.handshake "s hs traffic".toUTF8 helloTranscript =
        .ok out.serverHandshake ∧
      deriveSecret out.master "c ap traffic".toUTF8 serverTranscript =
        .ok out.clientApplication ∧
      deriveSecret out.master "s ap traffic".toUTF8 serverTranscript =
        .ok out.serverApplication := by
  simp only [keySchedule, bind_ok_iff, pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨hs, hh, ms, hm, ch, hch, sh, hsh, ca, hca, sa, hsa, rfl⟩
    exact ⟨rfl, hh, hm, hch, hsh, hca, hsa⟩
  · rintro ⟨he, hh, hm, hch, hsh, hca, hsa⟩
    refine ⟨out.handshake, hh, out.master, hm, out.clientHandshake, hch,
      out.serverHandshake, hsh, out.clientApplication, hca, out.serverApplication, hsa, ?_⟩
    cases out
    simp_all

/-- Transcripts with equal SHA-256 hashes give equal schedules. -/
theorem keySchedule_congr_hash (shared hello hello' server server' : ByteArray)
    (hhello : Sha256.hash32 hello = Sha256.hash32 hello')
    (hserver : Sha256.hash32 server = Sha256.hash32 server') :
    keySchedule shared hello server = keySchedule shared hello' server' := by
  simp only [keySchedule, deriveSecret, hhello, hserver]

/-- The Finished value of RFC 8446 §4.4.4 exists for every SHA-256 traffic secret and transcript. -/
theorem finished_ok (secret : Secret) (transcript : ByteArray) :
    ∃ output, finished secret transcript = .ok output := by
  obtain ⟨key, hk⟩ := Tls13.expandLabel_ok secret "finished".toUTF8 .empty 32
    (by decide) (by decide) (by decide)
  refine ⟨Hmac.hmac32 (packBytes key) (packBytes (Sha256.hash32 transcript)), ?_⟩
  simp only [finished, hk, bind, Except.bind, pure, Except.pure]

end EthLib.Networking.Quic.Tls
