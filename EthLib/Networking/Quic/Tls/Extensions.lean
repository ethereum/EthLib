module

public import EthLib.Networking.Quic.Tls.Messages

/-!
# Payload codecs for handshake extensions

The caller chooses a payload form from its message context.

The forms follow [RFC 8446 §4.2][extensions] and [RFC 7301 §3.1][alpn].

QUIC transport parameters remain opaque, as [RFC 9001 §8.2][parameters] assigns them to QUIC.

Decoding a payload neither advertises support for an algorithm nor accepts its use.

The handshake steps must check placement, required extensions and the peer's selections.

[extensions]: https://www.rfc-editor.org/rfc/rfc8446#section-4.2
[alpn]: https://www.rfc-editor.org/rfc/rfc7301#section-3.1
[parameters]: https://www.rfc-editor.org/rfc/rfc9001#section-8.2
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open Wire

/-- A named group and its opaque key-exchange bytes, RFC 8446 §4.2.8. -/
structure KeyShareEntry where
  group : CodePoint
  keyExchange : List UInt8
  deriving Repr, DecidableEq

/-- The form of one extension payload, selected by the enclosing message. -/
inductive PayloadForm where
  | supportedVersions
  | selectedVersion
  | supportedGroups
  | signatureAlgorithms
  | clientKeyShare
  | serverKeyShare
  | retryKeyShare
  | alpn
  | quicTransportParameters
  deriving Repr, DecidableEq

/-- The extension type for each payload form, RFC 8446 §4.2 and RFC 9001 §8.2. -/
def PayloadForm.type : PayloadForm → CodePoint
  | .supportedVersions | .selectedVersion => 43
  | .supportedGroups => 10
  | .signatureAlgorithms => 13
  | .clientKeyShare | .serverKeyShare | .retryKeyShare => 51
  | .alpn => 16
  | .quicTransportParameters => 57

/-- Structured extension payloads, without a list of accepted algorithms.

ALPN holds the offered protocol list; a server selection must later be checked as a singleton. -/
inductive Payload where
  | supportedVersions (versions : List CodePoint)
  | selectedVersion (version : CodePoint)
  | supportedGroups (groups : List CodePoint)
  | signatureAlgorithms (algorithms : List CodePoint)
  | clientKeyShare (shares : List KeyShareEntry)
  | serverKeyShare (share : KeyShareEntry)
  | retryKeyShare (group : CodePoint)
  | alpn (protocols : List (List UInt8))
  | quicTransportParameters (data : List UInt8)
  deriving Repr, DecidableEq

/-- The presentation-language form of a structured payload. -/
def Payload.form : Payload → PayloadForm
  | .supportedVersions _ => .supportedVersions
  | .selectedVersion _ => .selectedVersion
  | .supportedGroups _ => .supportedGroups
  | .signatureAlgorithms _ => .signatureAlgorithms
  | .clientKeyShare _ => .clientKeyShare
  | .serverKeyShare _ => .serverKeyShare
  | .retryKeyShare _ => .retryKeyShare
  | .alpn _ => .alpn
  | .quicTransportParameters _ => .quicTransportParameters

/-- Read a key share, requiring nonempty exchange bytes, RFC 8446 §4.2.8. -/
def readKeyShare : Reader KeyShareEntry := do
  let group ← codePoint
  return ⟨group, ← blob 2 1 65535⟩

/-- Encode one key share without checking its group element (§4.2.8). -/
def encodeKeyShare (share : KeyShareEntry) : Except Error (List UInt8) := do
  return Base.natToBytes 2 share.group.val ++ (← encodeBlob 2 1 65535 share.keyExchange)

/-- Encode the selected presentation-language form with its specified length bounds. -/
def encodePayloadBody : Payload → Except Error (List UInt8)
  | .supportedVersions versions => encodeCodePoints 1 2 254 versions
  | .selectedVersion version => .ok (Base.natToBytes 2 version.val)
  | .supportedGroups groups => encodeCodePoints 2 2 65535 groups
  | .signatureAlgorithms algorithms => encodeCodePoints 2 2 65534 algorithms
  | .clientKeyShare shares => encodeItems 2 0 65535 encodeKeyShare shares
  | .serverKeyShare share => encodeKeyShare share
  | .retryKeyShare group => .ok (Base.natToBytes 2 group.val)
  | .alpn protocols => encodeItems 2 2 65535 (encodeBlob 1 1 255) protocols
  | .quicTransportParameters data => .ok data

/-- Read a payload form, without interpreting algorithm identifiers or QUIC parameters. -/
def readPayload : PayloadForm → Reader Payload
  | .supportedVersions => return .supportedVersions (← items 1 2 254 codePoint)
  | .selectedVersion => return .selectedVersion (← codePoint)
  | .supportedGroups => return .supportedGroups (← items 2 2 65535 codePoint)
  | .signatureAlgorithms => return .signatureAlgorithms (← items 2 2 65534 codePoint)
  | .clientKeyShare => return .clientKeyShare (← items 2 0 65535 readKeyShare)
  | .serverKeyShare => return .serverKeyShare (← readKeyShare)
  | .retryKeyShare => return .retryKeyShare (← codePoint)
  | .alpn => return .alpn (← items 2 2 65535 (blob 1 1 255))
  | .quicTransportParameters => fun input => .ok (.quicTransportParameters input, [])

/-- Encode a payload as an extension, checking the extension's own uint16 length too (§4.2). -/
def encodePayload (payload : Payload) : Except Error Extension := do
  let data ← encodePayloadBody payload
  Base.ensure (data.length ≤ 65535) .length
  return ⟨payload.form.type, data⟩

/-- Decode one extension in the form expected by its caller, consuming all its data.

Unknown extensions are retained by the message codec and need no payload decoder.

An incomplete field inside a complete extension is a length error, as more input cannot repair it.
-/
def decodePayload (form : PayloadForm) (extension : Extension) : Except Error Payload := do
  Base.ensure (extension.kind = form.type) .constant
  Base.ensure (extension.data.length ≤ 65535) .length
  (exact (readPayload form) extension.data).mapError fun
    | .truncated => .length
    | error => error

end EthLib.Networking.Quic.Tls
