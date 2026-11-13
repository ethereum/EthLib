module

public import EthLib.Networking.Exports.QuicKeys
public import EthLib.Networking.Quic.Tls

/-!
# Exports: the SHA-256 TLS 1.3 key schedule

Callers supply the encoded transcripts; these operations do not authenticate them.
-/

public section

namespace EthLib.Networking.Quic.TlsExports

open EthLib.Exports (Result PyValue pyExport)

/-- Return early, handshake, master, client/server handshake and client/server application secrets.

The no-PSK schedule and transcript boundaries are those of RFC 8446 §7.1. -/
@[export eth_quic_tls_key_schedule]
def scheduleExport (args : PyValue) : Result PyValue :=
  pyExport (fun (shared, helloTranscript, serverTranscript) => do
    let s ← KeysExports.result (Tls.keySchedule shared helloTranscript serverTranscript)
    return (s.early, s.handshake, s.master, s.clientHandshake, s.serverHandshake,
      s.clientApplication, s.serverApplication)) args

/-- Derive a SHA-256 secret from encoded handshake messages, RFC 8446 §7.1. -/
@[export eth_quic_tls_derive_secret]
def deriveExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret, label, messages) =>
    KeysExports.result (Tls.deriveSecret secret label messages)) args

/-- Compute Finished verify_data over the transcript before that message, RFC 8446 §4.4.4. -/
@[export eth_quic_tls_finished]
def finishedExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret, transcript) => KeysExports.result (Tls.finished secret transcript)) args

end EthLib.Networking.Quic.TlsExports
