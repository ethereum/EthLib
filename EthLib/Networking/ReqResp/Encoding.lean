module

public import EthLib.Base.Uint64
public import EthLib.Networking.Encoding.Varint
public import EthLib.Networking.Snappy.Frame
public import EthLib.Networking.Snappy.FrameEncode

/-!
# `Networking.ReqResp.Encoding`

The `ssz_snappy` encoding of consensus-layer requests and responses.

A payload is the SSZ bytes of a message, sent as a varint length, then a Snappy framed stream.

```text
    [ SSZ length: varint | Snappy framed stream of the SSZ bytes ]
```

A response chunk starts with a response code, then context bytes, then such a payload.

These definitions take the whole message at once.

A peer reads a stream and may stop at the first byte past a bound.

How many bytes it reads before it decides is not part of these definitions.
-/

@[expose] public section

namespace EthLib.Networking.ReqResp

open EthLib.Base (ArithError)
open EthLib.Base.Uint64 (addChecked divChecked)
open EthLib.Networking.Encoding

/-- The largest payload of a gossip message, a request or a response chunk, in SSZ bytes: 10 MiB.

The cap is the same at every fork. -/
def MAX_PAYLOAD_SIZE : UInt64 := 10485760

/-- The largest error message, in bytes. -/
def MAX_ERROR_MESSAGE_SIZE : UInt64 := 256

/-- The most compressed bytes a reader accepts after a declared length `n`: `32 + n + n / 6`.

It is the worst-case size of a Snappy block of `n` bytes, from `snappy.cc` of `google/snappy`:
<https://github.com/google/snappy/blob/32ded457c0b1fe78ceb8397632c416568d6714a0/snappy.cc#L218>

The sum is a 64-bit integer, so a value of 2^64 or more is an error. -/
def maxCompressedLen (n : UInt64) : Except ArithError UInt64 := do
  addChecked (← addChecked 32 n) (← divChecked n 6)

/-- The largest message a peer accepts on the gossip network, framing included.

It allows 1024 bytes of overhead above the largest compressed payload, and at least 1 MiB. -/
def maxMessageSize : Except ArithError UInt64 := do
  let framed ← addChecked (← maxCompressedLen MAX_PAYLOAD_SIZE) 1024
  return max framed 1048576

/-- The first byte of a response chunk. -/
inductive ResponseCode where
  /-- 0: the payload is the requested message. -/
  | success
  /-- 1: the request was malformed or could not be understood. -/
  | invalidRequest
  /-- 2: the responder failed while it processed the request. -/
  | serverError
  /-- 3: the responder does not have the requested resource. -/
  | resourceUnavailable
  /-- 4 to 127: reserved, and an error to a reader that does not know the code. -/
  | reserved (code : UInt8)
  /-- 128 to 255: an error that one request type may define. -/
  | requestSpecific (code : UInt8)
  deriving Repr, DecidableEq

namespace ResponseCode

/-- The response code of a byte. -/
def ofByte (b : UInt8) : ResponseCode :=
  if b = 0 then .success
  else if b = 1 then .invalidRequest
  else if b = 2 then .serverError
  else if b = 3 then .resourceUnavailable
  else if b < 128 then .reserved b
  else .requestSpecific b

/-- The byte of a response code. -/
def toByte : ResponseCode → UInt8
  | .success => 0
  | .invalidRequest => 1
  | .serverError => 2
  | .resourceUnavailable => 3
  | .reserved code => code
  | .requestSpecific code => code

end ResponseCode

/-- Every way a request or a response chunk can be rejected. -/
inductive ReqRespError where
  /-- The length prefix is not a valid varint. -/
  | varint (error : Varint.VarintError)
  /-- The declared length is above the bound of the message type or the payload cap. -/
  | lengthOutOfBounds (declared bound : UInt64)
  /-- The declared length is below the smallest SSZ encoding of the message type. -/
  | lengthBelowMinimum (declared minimum : UInt64)
  /-- The bound on the compressed size is 2^64 or more. -/
  | arith (error : ArithError)
  /-- More compressed bytes follow the prefix than the declared length allows. -/
  | compressedTooLong (size bound : Nat)
  /-- The bytes after the prefix are not a valid Snappy framed stream. -/
  | frame (error : Snappy.FrameError)
  /-- The stream decodes to more or fewer bytes than the declared length. -/
  | lengthMismatch (declared : UInt64) (size : Nat)
  /-- A response chunk has no response code. -/
  | missingCode
  /-- A response chunk ends inside its context bytes. -/
  | contextTruncated
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def ReqRespError.code : ReqRespError → UInt32
  | .varint _ => 1
  | .lengthOutOfBounds .. => 2
  | .arith _ => 3
  | .compressedTooLong .. => 4
  | .frame _ => 5
  | .lengthMismatch .. => 6
  | .missingCode => 7
  | .contextTruncated => 8
  | .lengthBelowMinimum .. => 9

/-- The bytes of a varint at the start of the input, and the bytes after them.

A varint ends at its first byte below `0x80`.

The split looks at no more than eleven bytes, so the varint decoder sees an overlong prefix. -/
def splitVarint (bs : List UInt8) : List UInt8 × List UInt8 :=
  let k := (bs.take Varint.maxLength).findIdx (·.toNat < Varint.continuation) + 1
  (bs.take k, bs.drop k)

/-- The SSZ bytes of a payload, given the smallest and the largest encoding of its SSZ type.

The declared length must be at most the smaller of the largest encoding and the payload cap.

It must also be at least the smallest encoding, since a shorter payload cannot be of that type.

The length prefix must be the shortest varint of its value.

The specification only recommends this; requiring it gives each length exactly one prefix.

At most `32 + n + n / 6` bytes may follow a declared length `n`.

The stream must decode to exactly `n` bytes, so a stream that ends early or runs on is rejected.

The caller deserializes the bytes, since it knows their SSZ type. -/
def decodePayload (typeMin typeBound : UInt64) (bs : ByteArray) :
    Except ReqRespError ByteArray := do
  let (header, rest) := splitVarint bs.data.toList
  let declared ← (Varint.decode header).mapError .varint
  let bound := min typeBound MAX_PAYLOAD_SIZE
  if bound < declared then throw (.lengthOutOfBounds declared bound)
  if declared < typeMin then throw (.lengthBelowMinimum declared typeMin)
  let compressedBound ← (maxCompressedLen declared).mapError .arith
  if compressedBound.toNat < rest.length then
    throw (.compressedTooLong rest.length compressedBound.toNat)
  let data ← (Snappy.decodeFrames ⟨rest.toArray⟩).mapError .frame
  if data.size ≠ declared.toNat then throw (.lengthMismatch declared data.size)
  return data

/-- A payload that decodes to `data`: its length as a varint, then uncompressed Snappy frames.

It is the inverse that proofs, tests and bindings use, not a compressor. -/
def encodePayloadLiteral (data : ByteArray) : ByteArray :=
  ⟨(Varint.encode (UInt64.ofNat data.size)).toArray⟩ ++ Snappy.encodeFramesLiteral data

/-- A payload that decodes to `data`: its length as a varint, then a stream that compresses.

A chunk of the stream is compressed when that makes it shorter. -/
def encodePayload (data : ByteArray) : ByteArray :=
  ⟨(Varint.encode (UInt64.ofNat data.size)).toArray⟩ ++ Snappy.encodeFrames data

/-- One chunk of a response: its code, its context bytes and its SSZ bytes.

On an error code, the payload is the error message. -/
structure ResponseChunk where
  /-- The response code. -/
  code : ResponseCode
  /-- The context bytes, such as a fork digest, which select the SSZ type of the payload. -/
  context : ByteArray
  /-- The SSZ bytes of the message, or of the error message. -/
  payload : ByteArray
  deriving DecidableEq

/-- One response chunk, given the number of context bytes that the method sends.

A success carries that many context bytes, and its payload has the bounds of the message type.

An error carries no context bytes, and its payload is an error message of at most 256 bytes. -/
def decodeResponseChunk (contextBytes : Nat) (typeMin typeBound : UInt64)
    (bs : ByteArray) : Except ReqRespError ResponseChunk :=
  match bs.data.toList with
  | [] => throw .missingCode
  | b :: rest =>
    match ResponseCode.ofByte b with
    | .success => do
      if rest.length < contextBytes then throw .contextTruncated
      let payload ← decodePayload typeMin typeBound ⟨(rest.drop contextBytes).toArray⟩
      return ⟨.success, ⟨(rest.take contextBytes).toArray⟩, payload⟩
    | code => do
      let payload ← decodePayload 0 MAX_ERROR_MESSAGE_SIZE ⟨rest.toArray⟩
      return ⟨code, ByteArray.empty, payload⟩

/-- A response chunk that decodes to `chunk`, with its payload in uncompressed Snappy frames.

It is the inverse that proofs, tests and bindings use, not a compressor. -/
def encodeResponseChunkLiteral (chunk : ResponseChunk) : ByteArray :=
  ⟨#[chunk.code.toByte]⟩ ++ chunk.context ++ encodePayloadLiteral chunk.payload

/-- A response chunk that decodes to `chunk`, with its payload in a stream that compresses.

The code and the context bytes are written as they are.

It does not check that the context bytes or the payload fit the method or the code. -/
def encodeResponseChunk (chunk : ResponseChunk) : ByteArray :=
  ⟨#[chunk.code.toByte]⟩ ++ chunk.context ++ encodePayload chunk.payload

end EthLib.Networking.ReqResp
