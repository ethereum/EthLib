module

public import EthLib.Networking.Quic.Keys
public import EthLib.Cryptography.Proofs.Hash.Tls13
-- Checking a fixed label's byte length reduces the body of String.toUTF8.
import all Init.Data.String.Defs

/-!
# Proofs: QUIC v1 key derivation

Initial secrets and packet keys always derive successfully.

Each derivation uses exactly the labels and empty contexts of RFC 9001 §5.1 and §5.2.
-/

@[expose] public section

namespace EthLib.Networking.Quic

open EthLib.Base EthLib.Cryptography.Hash

/-- Initial derivation returns exactly the two labelled expansions of RFC 9001 §5.2. -/
theorem initialSecrets_ok_iff (dcid : ByteArray) (client server : Tls13.Secret) :
    initialSecrets dcid = .ok (client, server) ↔
      Tls13.expandLabel (Tls13.extract (packBytes INITIAL_SALT) dcid)
        "client in".toUTF8 .empty 32 = .ok client ∧
      Tls13.expandLabel (Tls13.extract (packBytes INITIAL_SALT) dcid)
        "server in".toUTF8 .empty 32 = .ok server := by
  simp only [initialSecrets, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨c, hc, s, hs, rfl, rfl⟩
    exact ⟨hc, hs⟩
  · rintro ⟨hc, hs⟩
    exact ⟨client, hc, server, hs, rfl, rfl⟩

/-- A destination connection ID always yields client and server Initial secrets. -/
theorem initialSecrets_ok (dcid : ByteArray) :
    ∃ client server, initialSecrets dcid = .ok (client, server) := by
  let initial := Tls13.extract (packBytes INITIAL_SALT) dcid
  obtain ⟨client, hc⟩ := Tls13.expandLabel_ok initial "client in".toUTF8 .empty 32
    (by decide) (by decide) (by decide)
  obtain ⟨server, hs⟩ := Tls13.expandLabel_ok initial "server in".toUTF8 .empty 32
    (by decide) (by decide) (by decide)
  exact ⟨client, server, (initialSecrets_ok_iff dcid client server).mpr ⟨hc, hs⟩⟩

/-- Packet derivation uses exactly the labels and empty contexts of RFC 9001 §5.1. -/
theorem packetKeys_ok_iff (suite : CipherSuite) (secret : Tls13.Secret)
    (keys : PacketKeys suite) : packetKeys suite secret = .ok keys ↔
      Tls13.expandLabel secret "quic key".toUTF8 .empty suite.keyLength = .ok keys.key ∧
      Tls13.expandLabel secret "quic iv".toUTF8 .empty 12 = .ok keys.iv ∧
      Tls13.expandLabel secret "quic hp".toUTF8 .empty suite.keyLength = .ok keys.hp := by
  cases keys with
  | mk key iv hp =>
    simp only [packetKeys, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
      PacketKeys.mk.injEq]
    constructor
    · rintro ⟨k, hk, i, hi, h, hh, rfl, rfl, rfl⟩
      exact ⟨hk, hi, hh⟩
    · rintro ⟨hk, hi, hh⟩
      exact ⟨key, hk, iv, hi, hp, hh, rfl, rfl, rfl⟩

/-- Both covered cipher suites always derive their three packet keys. -/
theorem packetKeys_ok (suite : CipherSuite) (secret : Tls13.Secret) :
    ∃ keys, packetKeys suite secret = .ok keys := by
  have hlength : suite.keyLength ≤ 8160 := by cases suite <;> decide
  obtain ⟨key, hk⟩ := Tls13.expandLabel_ok secret "quic key".toUTF8 .empty suite.keyLength
    (by decide) (by decide) hlength
  obtain ⟨iv, hi⟩ := Tls13.expandLabel_ok secret "quic iv".toUTF8 .empty 12
    (by decide) (by decide) (by decide)
  obtain ⟨hp, hh⟩ := Tls13.expandLabel_ok secret "quic hp".toUTF8 .empty suite.keyLength
    (by decide) (by decide) hlength
  exact ⟨⟨key, iv, hp⟩, (packetKeys_ok_iff suite secret _).mpr ⟨hk, hi, hh⟩⟩

end EthLib.Networking.Quic
