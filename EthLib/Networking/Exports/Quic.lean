module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Base.Exports.PyDerive
public import EthLib.Networking.Quic.Frame
public import EthLib.Cryptography.Exports.Tls13
public import EthLib.Networking.Quic.Keys
public import EthLib.Networking.Quic.Tls
public import EthLib.Networking.Quic.Varint

/-!
# Exports: QUIC wire encodings, packet keys and the TLS 1.3 key schedule

The encoder rejects a value of `2^62` or more with code 0.

The decoder accepts the longer forms of RFC 9000 §16.

The QUIC key exports reject a cipher suite outside the two they cover with code 0.

They reject a secret of the wrong size with code 0 too.

Traffic secrets are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

public section

namespace EthLib.Networking.Quic.Exports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Cryptography.Hash.Tls13.Exports (ofExcept)

/-- Encode a value below `2^62` with its shortest QUIC representation, RFC 9000 §16. -/
@[export eth_quic_varint_encode]
def encodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value : Nat) => do
    if h : value < 2 ^ 62 then
      return (⟨(Varint.encode ⟨value, h⟩).toArray⟩ : ByteArray)
    else throw (0, "value must be below 2^62")) args

/-- Read a QUIC integer and return its value and the trailing bytes, RFC 9000 §16. -/
@[export eth_quic_varint_decode]
def decodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (value, rest) ← (Varint.decode data.data.toList).mapError
      fun e => (e.code, s!"QUIC integer rejected: {reprStr e}")
    return (value.val, (⟨rest.toArray⟩ : ByteArray))) args

/-- Derive the client and server Initial secrets for QUIC v1, RFC 9001 §5.2. -/
@[export eth_quic_initial_secrets]
def initialExport (args : PyValue) : Result PyValue :=
  pyExport (fun dcid => ofExcept (initialSecrets dcid)) args

/-- Read one of the two SHA-256 cipher suites covered by the key derivation, or fail with code 0. -/
def readSuite : String → Result CipherSuite
  | "TLS_AES_128_GCM_SHA256" => pure .aes128GcmSha256
  | "TLS_CHACHA20_POLY1305_SHA256" => pure .chacha20Poly1305Sha256
  | s => .error (0, s!"expected TLS_AES_128_GCM_SHA256 or TLS_CHACHA20_POLY1305_SHA256, got {s}")

/-- Derive the payload key, IV and header-protection key, in that order, RFC 9001 §5.1. -/
@[export eth_quic_packet_keys]
def packetExport (args : PyValue) : Result PyValue :=
  pyExport (fun (suite, secret) => do
    let suite ← readSuite suite
    let keys ← ofExcept (packetKeys suite secret)
    return (Base.packBytes keys.key, Base.packBytes keys.iv, Base.packBytes keys.hp)) args

/-- Return the early, handshake, master, two handshake traffic and two application traffic secrets.

Each pair gives the client secret first.

The no-PSK schedule and transcript boundaries are those of RFC 8446 §7.1. -/
@[export eth_quic_tls_key_schedule]
def scheduleExport (args : PyValue) : Result PyValue :=
  pyExport (fun (sharedSecret, helloTranscript, serverTranscript) => do
    let s ← ofExcept (Tls.keySchedule sharedSecret helloTranscript serverTranscript)
    return (s.early, s.handshake, s.master, s.clientHandshake, s.serverHandshake,
      s.clientApplication, s.serverApplication)) args

/-- Derive a SHA-256 secret from encoded handshake messages, RFC 8446 §7.1.

The label excludes the `tls13 ` prefix. -/
@[export eth_quic_tls_derive_secret]
def deriveExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret, label, messages) => ofExcept (Tls.deriveSecret secret label messages)) args

/-- Compute the Finished `verify_data` over the transcript that precedes it, RFC 8446 §4.4.4.

During the handshake the secret is the sender's handshake traffic secret. -/
@[export eth_quic_tls_finished]
def finishedExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret, transcript) => ofExcept (Tls.finished secret transcript)) args

open EthLib.Exports (ToPy FromPy LawfulPy PlainPy toPy fromPy)

local instance (n : Nat) : ToPy (Fin n) := ⟨fun value => .int value.val⟩
local instance (n : Nat) : FromPy (Fin n) := ⟨fun value => do
  let bounded ← EthLib.Exports.fromPyBelow n value
  return ⟨bounded.val, bounded.property⟩⟩
local instance (n : Nat) : PlainPy (Fin n) := ⟨fun _ => rfl⟩
local instance (n : Nat) : LawfulPy (Fin n) where
  fromPy_toPy value := by
    show (do
      let bounded ← EthLib.Exports.fromPyBelow n (.int value.val)
      pure (⟨bounded.val, bounded.property⟩ : Fin n)) = .ok value
    simp [EthLib.Exports.fromPyBelow, fromPy, value.isLt, bind, Except.bind,
      pure, Except.pure]

derive_py Packet.PacketType
derive_py_laws Packet.PacketType
derive_py Packet.Header
derive_py_laws Packet.Header
derive_py Frame.Ack
derive_py_laws Frame.Ack
derive_py Frame.Frame
derive_py_laws Frame.Frame

/-- Encode a QUIC header, with checked lengths and packet-number bounds (RFC 9000 §17). -/
@[export eth_quic_header_encode]
def headerEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (header : Packet.Header) => do
    let encoded ← (Packet.encode header).mapError
      fun e => (e.code, s!"QUIC header rejected: {reprStr e}")
    return (⟨encoded.toArray⟩ : ByteArray)) args

/-- Read an authenticated header and return its fields and remaining bytes (RFC 9000 §17). -/
@[export eth_quic_header_decode]
def headerDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (input : Nat × ByteArray) => do
    let (shortConnectionIdLength, data) := input
    let (header, rest) ← (Packet.decode shortConnectionIdLength data.toList).mapError
      fun e => (e.code, s!"QUIC header rejected: {reprStr e}")
    return (header, (⟨rest.toArray⟩ : ByteArray))) args

/-- Encode one well-formed QUIC frame (RFC 9000 §19). -/
@[export eth_quic_frame_encode]
def frameEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (frame : Frame.Frame) => do
    let encoded ← (Frame.encode frame).mapError
      fun e => (e.code, s!"QUIC frame rejected: {reprStr e}")
    return (⟨encoded.toArray⟩ : ByteArray)) args

/-- Read one frame allowed in the given packet type (RFC 9000 §12.4). -/
@[export eth_quic_frame_decode]
def frameDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (input : Packet.PacketType × ByteArray) => do
    let (packet, data) := input
    let (frame, rest) ← (Frame.decode packet data.toList).mapError
      fun e => (e.code, s!"QUIC frame rejected: {reprStr e}")
    return (frame, (⟨rest.toArray⟩ : ByteArray))) args

/-- Write the low packet-number bytes (RFC 9000 §17.1). -/
@[export eth_quic_packet_number_encode]
def packetNumberEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (input : Fin 4 × Fin (2 ^ 62)) => do
    let (width, number) := input
    pure (⟨(Packet.encodePacketNumber width number).toArray⟩ : ByteArray)) args

/-- Reconstruct a packet number from its low bytes (RFC 9000 Appendix A.3). -/
@[export eth_quic_packet_number_decode]
def packetNumberDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (input : Fin 4 × Nat × Nat) => do
    let (width, truncated, expected) := input
    (Packet.decodePacketNumber width truncated expected).mapError
      fun e => (e.code, s!"QUIC packet number rejected: {reprStr e}")) args

end EthLib.Networking.Quic.Exports
