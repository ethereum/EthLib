module

public import EthLib.Base.Exports.PyValue
public import EthLib.Base.Exports.Fin
public import EthLib.Base.Exports.PyDerive
public import EthLib.Networking.Quic.Frame
public import EthLib.Cryptography.Exports.Tls13
public import EthLib.Networking.Quic.Keys
public import EthLib.Networking.Quic.Tls
public import EthLib.Networking.Quic.Tls.Extensions
public import EthLib.Networking.Quic.Tls.Transcript
public import EthLib.Networking.Quic.Varint

/-!
# Exports: QUIC wire encodings, packet keys and TLS 1.3 handshake data

The encoder rejects a value of `2^62` or more with code 0.

The decoder accepts the longer forms of RFC 9000 §16.

The QUIC key exports reject a cipher suite outside the two they cover with code 0.

They reject a secret of the wrong size with code 0 too.

Traffic secrets are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

public section

namespace EthLib.Networking.Quic.Exports

open EthLib.Exports (ExportError Result PyValue pyExport rejectArgument toResult)

/-- A rejected QUIC integer reaches Python with its code, and its message is the printed error. -/
instance : ExportError Varint.VarintError where
  code := Varint.VarintError.code
  message := reprStr

/-- A rejected header, frame or packet number reaches Python with its code and the printed error. -/
instance : ExportError Wire.Error where
  code := Wire.Error.code
  message := reprStr

/-- A packet number with no width reaches Python with its code, and the printed error. -/
instance : ExportError Packet.WidthError where
  code := Packet.WidthError.code
  message := reprStr

/-- A rejected handshake message, payload or transcript reaches Python with its code.

Its message is the printed error, and it carries no TLS alert. -/
instance : ExportError Tls.Wire.Error where
  code := Tls.Wire.Error.code
  message := reprStr

/-- Encode a value below `2^62` with its shortest QUIC representation, RFC 9000 §16. -/
@[export eth_quic_varint_encode]
def encodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value : Nat) => do
    if h : value < 2 ^ 62 then
      return Varint.encode ⟨value, h⟩
    else rejectArgument none "value must be below 2^62") args

/-- Read a QUIC integer and return its value and the trailing bytes, RFC 9000 §16. -/
@[export eth_quic_varint_decode]
def decodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (value, rest) ← toResult "QUIC integer rejected" (Varint.decode data)
    return (value.val, rest)) args

/-- Derive the client and server Initial secrets for QUIC v1, RFC 9001 §5.2. -/
@[export eth_quic_initial_secrets]
def initialExport (args : PyValue) : Result PyValue :=
  pyExport (fun dcid => toResult none (initialSecrets dcid)) args

/-- Read one of the two SHA-256 cipher suites covered by the key derivation, or fail with code 0. -/
def readSuite : String → Result CipherSuite
  | "TLS_AES_128_GCM_SHA256" => pure .aes128GcmSha256
  | "TLS_CHACHA20_POLY1305_SHA256" => pure .chacha20Poly1305Sha256
  | s => rejectArgument none
    s!"expected TLS_AES_128_GCM_SHA256 or TLS_CHACHA20_POLY1305_SHA256, got {s}"

/-- Derive the payload key, IV and header-protection key, in that order, RFC 9001 §5.1. -/
@[export eth_quic_packet_keys]
def packetExport (args : PyValue) : Result PyValue :=
  pyExport (fun (suite, secret) => do
    let suite ← readSuite suite
    let keys ← toResult none (packetKeys suite secret)
    return (Base.packBytes keys.key, Base.packBytes keys.iv, Base.packBytes keys.hp)) args

/-- Return the early, handshake, master, two handshake traffic and two application traffic secrets.

Each pair gives the client secret first.

The no-PSK schedule and transcript boundaries are those of RFC 8446 §7.1. -/
@[export eth_quic_tls_key_schedule]
def scheduleExport (args : PyValue) : Result PyValue :=
  pyExport (fun (sharedSecret, helloTranscript, serverTranscript) => do
    let s ← toResult none (Tls.keySchedule sharedSecret helloTranscript serverTranscript)
    return (s.early, s.handshake, s.master, s.clientHandshake, s.serverHandshake,
      s.clientApplication, s.serverApplication)) args

/-- Derive a SHA-256 secret from encoded handshake messages, RFC 8446 §7.1.

The label excludes the `tls13 ` prefix. -/
@[export eth_quic_tls_derive_secret]
def deriveExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret, label, messages) =>
    toResult none (Tls.deriveSecret secret label messages)) args

/-- Compute the Finished `verify_data` over the transcript that precedes it, RFC 8446 §4.4.4.

During the handshake the secret is the sender's handshake traffic secret. -/
@[export eth_quic_tls_finished]
def finishedExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret, transcript) => toResult none (Tls.finished secret transcript)) args

open EthLib.Exports (ToPy FromPy LawfulPy PlainPy toPy fromPy)
open scoped EthLib.Exports.FinAsInt

derive_py Packet.PacketType
derive_py_laws Packet.PacketType
derive_py Packet.Header
derive_py_laws Packet.Header
derive_py Frame.Ack
derive_py_laws Frame.Ack
derive_py Frame.Frame
derive_py_laws Frame.Frame

derive_py Tls.Extension
derive_py_laws Tls.Extension
derive_py Tls.ClientHello
derive_py_laws Tls.ClientHello
derive_py Tls.ServerHello
derive_py_laws Tls.ServerHello
derive_py Tls.CertificateEntry
derive_py_laws Tls.CertificateEntry
derive_py Tls.CertificateMessage
derive_py_laws Tls.CertificateMessage
derive_py Tls.CertificateRequest
derive_py_laws Tls.CertificateRequest
derive_py Tls.Message
derive_py_laws Tls.Message
derive_py Tls.KeyShareEntry
derive_py_laws Tls.KeyShareEntry
derive_py Tls.PayloadForm
derive_py_laws Tls.PayloadForm
derive_py Tls.Payload
derive_py_laws Tls.Payload

/-- Encode one handshake message with its header and the caller's hash length, RFC 8446 §4. -/
@[export eth_quic_tls_message_encode]
def messageEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (hashLength, message) => do
    let data ← toResult none (Tls.encode hashLength message)
    return data) args

/-- Decode one complete message and return its fields and trailing bytes, RFC 8446 §4. -/
@[export eth_quic_tls_message_decode]
def messageDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (input : Nat × ByteArray) => do
    let (hashLength, data) := input
    let (message, rest) ← toResult none (Tls.decode hashLength data)
    return (message, rest)) args

/-- Encode a structured extension payload without selecting an algorithm or protocol. -/
@[export eth_quic_tls_payload_encode]
def payloadEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun payload => toResult none (Tls.encodePayload payload)) args

/-- Decode an extension in the payload form that its message context requires. -/
@[export eth_quic_tls_payload_decode]
def payloadDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (form, extension) => toResult none (Tls.decodePayload form extension)) args

/-- Return the SHA-256 transcript of complete handshake messages and its hash, RFC 8446 §4.4.1.

A HelloRetryRequest replaces ClientHello1 with its synthetic `message_hash` message. -/
@[export eth_quic_tls_transcript]
def transcriptExport (args : PyValue) : Result PyValue :=
  pyExport (fun (messages : List ByteArray) => do
    let result ← toResult none (Tls.transcript messages)
    return (result.bytes, result.hash)) args

/-- Build the CertificateVerify signed content from a SHA-256 transcript hash, RFC 8446 §4.4.3. -/
@[export eth_quic_tls_certificate_verify_input]
def certificateVerifyInputExport (args : PyValue) : Result PyValue :=
  pyExport (fun (server, digest) =>
    pure (Tls.certificateVerifyInput server digest)) args

/-- Encode a QUIC header, with checked lengths and packet-number bounds (RFC 9000 §17). -/
@[export eth_quic_header_encode]
def headerEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (header : Packet.Header) => do
    let encoded ← toResult "QUIC header rejected" (Packet.encode header)
    return encoded) args

/-- Read an authenticated header and return its fields and remaining bytes (RFC 9000 §17). -/
@[export eth_quic_header_decode]
def headerDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (input : Nat × ByteArray) => do
    let (shortConnectionIdLength, data) := input
    let (header, rest) ←
      toResult "QUIC header rejected" (Packet.decode shortConnectionIdLength data)
    return (header, rest)) args

/-- Encode one well-formed QUIC frame (RFC 9000 §19). -/
@[export eth_quic_frame_encode]
def frameEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (frame : Frame.Frame) => do
    let encoded ← toResult "QUIC frame rejected" (Frame.encode frame)
    return encoded) args

/-- Read one frame allowed in the given packet type (RFC 9000 §12.4). -/
@[export eth_quic_frame_decode]
def frameDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (input : Packet.PacketType × ByteArray) => do
    let (packet, data) := input
    let (frame, rest) ← toResult "QUIC frame rejected" (Frame.decode packet data)
    return (frame, rest)) args

/-- Select the shortest packet-number length bits, zero through three, under RFC 9000 §17.1.

Any acknowledgement must be for this sender in the same connection and packet-number space.

With no acknowledgement, the selected bytes hold the full number.

Otherwise the byte window exceeds twice the gap from the largest acknowledged number.

An acknowledged number that is not earlier raises code 10.

A range needing more than four bytes raises code 11. -/
@[export eth_quic_packet_number_width]
def packetNumberWidthExport (args : PyValue) : Result PyValue :=
  pyExport (fun (input : Fin (2 ^ 62) × Option (Fin (2 ^ 62))) => do
    let (number, largestAcked) := input
    toResult "QUIC packet number rejected" (Packet.packetNumberWidth number largestAcked)) args

/-- Write the low packet-number bytes (RFC 9000 §17.1). -/
@[export eth_quic_packet_number_encode]
def packetNumberEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (input : Fin 4 × Fin (2 ^ 62)) => do
    let (width, number) := input
    pure (Packet.encodePacketNumber width number)) args

/-- Reconstruct a packet number from its low bytes (RFC 9000 Appendix A.3). -/
@[export eth_quic_packet_number_decode]
def packetNumberDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (input : Fin 4 × Nat × Nat) => do
    let (width, truncated, expected) := input
    toResult "QUIC packet number rejected"
      (Packet.decodePacketNumber width truncated expected)) args

end EthLib.Networking.Quic.Exports
