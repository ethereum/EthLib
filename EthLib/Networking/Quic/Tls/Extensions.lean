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
  keyExchange : ByteArray
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
  -- RFC 8446 §4.2: the supported versions extension has type 43.
  | .supportedVersions | .selectedVersion => 43
  -- RFC 8446 §4.2: the supported groups extension has type 10.
  | .supportedGroups => 10
  -- RFC 8446 §4.2: the signature algorithms extension has type 13.
  | .signatureAlgorithms => 13
  -- RFC 8446 §4.2: the key share extension has type 51.
  | .clientKeyShare | .serverKeyShare | .retryKeyShare => 51
  -- RFC 8446 §4.2 and RFC 7301 §3.1: the ALPN extension has type 16.
  | .alpn => 16
  -- RFC 9001 §8.2: the QUIC transport parameters extension has type 0x39.
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
  | alpn (protocols : List ByteArray)
  | quicTransportParameters (data : ByteArray)
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
  -- `struct { NamedGroup group; opaque key_exchange<1..2^16-1>; } KeyShareEntry;`
  let group ← codePoint
  return ⟨group, (← blob 2 1 65535).toByteArray⟩

/-- Encode one key share without checking its group element (§4.2.8). -/
def encodeKeyShare (share : KeyShareEntry) : Except Error (List UInt8) := do
  -- `NamedGroup group;` in two bytes, then `opaque key_exchange<1..2^16-1>;`.
  return Base.natToBytes 2 share.group.val ++ (← encodeBlob 2 1 65535 share.keyExchange.data.toList)

/-- Encode the selected presentation-language form with its specified length bounds. -/
def encodePayloadBody : Payload → Except Error (List UInt8)
  -- RFC 8446 §4.2.1, in a ClientHello: `ProtocolVersion versions<2..254>;`.
  | .supportedVersions versions => encodeCodePoints 1 2 254 versions
  -- RFC 8446 §4.2.1, in a ServerHello or HelloRetryRequest: `ProtocolVersion selected_version;`.
  | .selectedVersion version => .ok (Base.natToBytes 2 version.val)
  -- RFC 8446 §4.2.7: `NamedGroup named_group_list<2..2^16-1>;`.
  | .supportedGroups groups => encodeCodePoints 2 2 65535 groups
  -- RFC 8446 §4.2.3: `SignatureScheme supported_signature_algorithms<2..2^16-2>;`.
  | .signatureAlgorithms algorithms => encodeCodePoints 2 2 65534 algorithms
  -- RFC 8446 §4.2.8, KeyShareClientHello: `KeyShareEntry client_shares<0..2^16-1>;`.
  | .clientKeyShare shares => encodeItems 2 0 65535 encodeKeyShare shares
  -- RFC 8446 §4.2.8, KeyShareServerHello: `KeyShareEntry server_share;`.
  | .serverKeyShare share => encodeKeyShare share
  -- RFC 8446 §4.2.8, KeyShareHelloRetryRequest: `NamedGroup selected_group;`.
  | .retryKeyShare group => .ok (Base.natToBytes 2 group.val)
  -- RFC 7301 §3.1: `ProtocolName protocol_name_list<2..2^16-1>`.
  --
  -- Each name is `opaque ProtocolName<1..2^8-1>;`.
  | .alpn protocols =>
    encodeItems 2 2 65535 (fun data => encodeBlob 1 1 255 data.data.toList) protocols
  -- RFC 9001 §8.2: the version of QUIC in use defines the value, so the bytes pass through.
  | .quicTransportParameters data => .ok data.data.toList

/-- Read one packed ALPN name, RFC 7301 §3.1. -/
def readAlpnName : Reader ByteArray := do
  -- `opaque ProtocolName<1..2^8-1>;`: empty strings MUST NOT be included.
  return (← blob 1 1 255).toByteArray

/-- Read a payload form, without interpreting algorithm identifiers or QUIC parameters. -/
def readPayload : PayloadForm → Reader Payload
  -- RFC 8446 §4.2.1: `ProtocolVersion versions<2..254>;`.
  | .supportedVersions => return .supportedVersions (← items 1 2 254 codePoint)
  -- RFC 8446 §4.2.1: `ProtocolVersion selected_version;`.
  | .selectedVersion => return .selectedVersion (← codePoint)
  -- RFC 8446 §4.2.7: `NamedGroup named_group_list<2..2^16-1>;`.
  --
  -- An odd length leaves a partial `NamedGroup`, which §3.4 makes illegal.
  | .supportedGroups => return .supportedGroups (← items 2 2 65535 codePoint)
  -- RFC 8446 §4.2.3: `SignatureScheme supported_signature_algorithms<2..2^16-2>;`.
  | .signatureAlgorithms => return .signatureAlgorithms (← items 2 2 65534 codePoint)
  -- RFC 8446 §4.2.8: `KeyShareEntry client_shares<0..2^16-1>;`.
  --
  -- It MAY be empty if the client is requesting a HelloRetryRequest; the codec accepts it always.
  | .clientKeyShare => return .clientKeyShare (← items 2 0 65535 readKeyShare)
  -- RFC 8446 §4.2.8: `KeyShareEntry server_share;`.
  | .serverKeyShare => return .serverKeyShare (← readKeyShare)
  -- RFC 8446 §4.2.8: `NamedGroup selected_group;`.
  | .retryKeyShare => return .retryKeyShare (← codePoint)
  -- RFC 7301 §3.1: `ProtocolName protocol_name_list<2..2^16-1>`.
  | .alpn => return .alpn (← items 2 2 65535 readAlpnName)
  -- RFC 9001 §8.2: the whole of the extension data, kept opaque.
  | .quicTransportParameters => fun input => .ok (.quicTransportParameters input.toByteArray, [])

/-- Encode a payload as an extension, checking the extension's own uint16 length too (§4.2). -/
def encodePayload (payload : Payload) : Except Error Extension := do
  let data ← encodePayloadBody payload
  -- §4.2: `opaque extension_data<0..2^16-1>;`.
  Base.ensure (data.length ≤ 65535) .length
  -- §4.2: the extension type is the type of the payload form.
  return ⟨payload.form.type, data.toByteArray⟩

/-- Decode one extension in the form expected by its caller, consuming all its data.

Unknown extensions are retained by the message codec and need no payload decoder.
-/
def decodePayload (form : PayloadForm) (extension : Extension) : Except Error Payload := do
  -- EthLib's check: the extension type is the code point of the expected form (§4.2).
  Base.ensure (extension.kind = form.type) .constant
  -- §4.2: `opaque extension_data<0..2^16-1>;`.
  Base.ensure (extension.data.size ≤ 65535) .length
  -- The structure of the form fills the extension data exactly.
  --
  -- A field cut short inside it is a length error, as more input cannot repair it.
  (exact (readPayload form) extension.data.data.toList).mapError fun
    | .truncated .. => .length
    | error => error

end EthLib.Networking.Quic.Tls
