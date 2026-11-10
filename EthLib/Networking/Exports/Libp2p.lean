module

public import EthLib.Base.Exports.PyDerive
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Libp2p.Mplex
public import EthLib.Networking.Libp2p.Multistream
public import EthLib.Networking.Libp2p.PeerId
public import EthLib.Networking.Libp2p.Yamux

/-!
# Exports: libp2p framing and peer IDs

C-ABI exports for the libp2p codecs, callable from the Python C extension.

They cover multistream-select messages, mplex and yamux frames, and secp256k1 peer IDs.

A decoder returns the value at the start of its input and the bytes after it.

An mplex frame crosses as a `dict` of its stream ID, its flag and its data.

A yamux frame crosses as a `dict` of its kind, flags, stream ID, length and data.

An mplex flag or a yamux kind crosses as its name in snake case, such as `new_stream`.

The yamux flags cross as an `int`.

The multistream-select and mplex encoders refuse an input outside the format, with code 0.

The yamux encoder refuses, with code 0, data whose size is not the one its kind and length give.

Each such input breaks a rule of its source, so it has no bytes.

Another export module that passes a frame imports its conversions from this module.

The keys of a frame `dict` are the field names of its Lean structure, in snake case.
-/

public section

namespace EthLib.Networking.Libp2p.Exports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Networking.Encoding
open EthLib.Cryptography.Secp256k1 (Fn)

derive_py Mplex.Flag
derive_py_laws Mplex.Flag
derive_py Mplex.Frame
derive_py_laws Mplex.Frame
derive_py Yamux.Kind
derive_py_laws Yamux.Kind
derive_py Yamux.Frame
derive_py_laws Yamux.Frame

/-- The bytes of one multistream-select message: its length, its bytes, then a newline.

The length counts the newline.

The message must be shorter than `2^63 - 1` bytes, so that its length fits an unsigned varint. -/
@[export eth_multistream_encode]
def multistreamEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (message : ByteArray) => do
    if Uvarint.bound ≤ message.size + 1 then
      throw (0, "message must be shorter than 2^63 - 1 bytes")
    return (⟨(Multistream.encode message).toArray⟩ : ByteArray)) args

/-- The multistream-select message at the start of the bytes, and the bytes after it. -/
@[export eth_multistream_decode]
def multistreamDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (message, rest) ← (Multistream.decode data.data.toList).mapError
      fun e => (e.code, s!"multistream message rejected: {reprStr e}")
    return (message, (⟨rest.toArray⟩ : ByteArray))) args

/-- The bytes of a valid mplex frame. -/
@[export eth_mplex_encode]
def mplexEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (frame : Mplex.Frame) => do
    unless decide frame.Valid do
      throw (0, "frame must have a stream ID below 2^60, at most 1 MiB of data, " ++
        "and no data on a close or a reset")
    return (⟨(Mplex.encode frame).toArray⟩ : ByteArray)) args

/-- The mplex frame at the start of the bytes, and the bytes after it. -/
@[export eth_mplex_decode]
def mplexDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (frame, rest) ← (Mplex.decode data.data.toList).mapError
      fun e => (e.code, s!"mplex frame rejected: {reprStr e}")
    return (frame, (⟨rest.toArray⟩ : ByteArray))) args

/-- The bytes of a valid yamux frame. -/
@[export eth_yamux_encode]
def yamuxEncodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (frame : Yamux.Frame) => do
    unless decide frame.Valid do
      throw (0, "frame must carry as many bytes as its length for data, else none")
    return (⟨(Yamux.encode frame).toArray⟩ : ByteArray)) args

/-- The yamux frame at the start of the bytes, and the bytes after it. -/
@[export eth_yamux_decode]
def yamuxDecodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (frame, rest) ← (Yamux.decode data.data.toList).mapError
      fun e => (e.code, s!"yamux frame rejected: {reprStr e}")
    return (frame, (⟨rest.toArray⟩ : ByteArray))) args

/-- The result of a function on peer identities, with the code of its error. -/
def identityResult {α : Type} (r : Except IdentityError α) : Result α :=
  r.mapError fun e => (e.code, s!"libp2p identity rejected: {reprStr e}")

/-- Read 32 big-endian bytes as a secp256k1 scalar, whose value must be below the group order.

A larger value gives the private-key error; the functions that take the scalar reject 0.

The secret key must stay private, and this function makes no constant-time claim. -/
def secretOfBytes (bytes : Vector UInt8 32) : Except IdentityError Fn :=
  let n := EthLib.Base.bytesToNat bytes.toList
  if h : n < Fn.modulus then .ok ⟨n, h⟩ else .error .privateKey

/-- The public-key protobuf of a 32-byte big-endian secp256k1 secret in [1, n).

Here n is the order of the group.

The secret key must stay private, and this function makes no constant-time claim. -/
@[export eth_libp2p_public_key]
def publicKeyExport (args : PyValue) : Result PyValue :=
  pyExport (fun (secret : Vector UInt8 32) => identityResult do
    publicKey (← secretOfBytes secret)) args

/-- The peer ID of a canonical secp256k1 key protobuf. -/
@[export eth_libp2p_peer_id]
def peerIdExport (args : PyValue) : Result PyValue :=
  pyExport (fun (key : ByteArray) => identityResult do
    return peerId (← decodePublicKey key)) args

/-- The key protobuf that a binary secp256k1 peer ID names. -/
@[export eth_libp2p_decode_peer_id]
def decodePeerIdExport (args : PyValue) : Result PyValue :=
  pyExport (fun (id : ByteArray) => identityResult do
    return encodePublicKey (← decodePeerId id)) args

end EthLib.Networking.Libp2p.Exports
