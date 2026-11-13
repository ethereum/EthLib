module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Quic.Keys

/-!
# Exports: TLS labelled HKDF and QUIC v1 packet keys

Secrets and keys cross the boundary with their fixed lengths checked in Lean.
-/

public section

namespace EthLib.Networking.Quic.KeysExports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Cryptography.Hash

def result {α : Type} (r : Except Tls13.Error α) : Result α :=
  r.mapError fun e => (e.code, reprStr e)

/-- Serialize the checked TLS 1.3 HKDF label, RFC 8446 §7.1. -/
@[export eth_tls13_hkdf_label]
def labelExport (args : PyValue) : Result PyValue :=
  pyExport (fun (label, context, length) => result (Tls13.hkdfLabel label context length)) args

/-- Expand a SHA-256 secret with a TLS 1.3 label and context, RFC 8446 §7.1. -/
@[export eth_tls13_expand_label]
def expandExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret, label, context, length) =>
    result ((Tls13.expandLabel secret label context length).map Base.packBytes)) args

/-- Derive the client and server Initial secrets for QUIC v1, RFC 9001 §5.2. -/
@[export eth_quic_initial_secrets]
def initialExport (args : PyValue) : Result PyValue :=
  pyExport (fun dcid => result (initialSecrets dcid)) args

/-- Read one of the two SHA-256 cipher suites covered by the key derivation. -/
def readSuite : String → Result CipherSuite
  | "TLS_AES_128_GCM_SHA256" => pure .aes128GcmSha256
  | "TLS_CHACHA20_POLY1305_SHA256" => pure .chacha20Poly1305Sha256
  | _ => .error (0, "unsupported QUIC key derivation suite")

/-- Derive the payload key, IV and header-protection key, in that order, RFC 9001 §5.1. -/
@[export eth_quic_packet_keys]
def packetExport (args : PyValue) : Result PyValue :=
  pyExport (fun (suite, secret) => do
    let suite ← readSuite suite
    let keys ← result (packetKeys suite secret)
    return (Base.packBytes keys.key, Base.packBytes keys.iv, Base.packBytes keys.hp)) args

end EthLib.Networking.Quic.KeysExports
