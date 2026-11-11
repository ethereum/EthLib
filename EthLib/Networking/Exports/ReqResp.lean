module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.ReqResp.Encoding

/-!
# `Exports.ReqResp`

C-ABI exports for the `ssz_snappy` encoding of requests and responses.

Each decoder takes the whole message.

The encoders compress each chunk of a payload when that makes it shorter, and cannot fail.

A rejected message comes back as the code and the message of its error.

A response chunk comes back as a tuple of its code, its context bytes and its payload.
-/

public section

namespace EthLib.Networking.ReqResp.Exports

open EthLib.Exports (Result PyValue pyExport)


/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def message : ReqRespError → String
  | .varint _ => "length prefix is not a valid varint"
  | .lengthOutOfBounds declared bound => s!"declared length {declared} is above {bound}"
  | .lengthBelowMinimum declared minimum => s!"declared length {declared} is below {minimum}"
  | .arith _ => "bound on the compressed size is 2^64 or more"
  | .compressedTooLong size bound => s!"{size} compressed bytes, more than {bound}"
  | .frame _ => "payload is not a valid Snappy framed stream"
  | .lengthMismatch declared size => s!"payload has {size} bytes, not the declared {declared}"
  | .missingCode => "response chunk has no response code"
  | .contextTruncated => "response chunk ends inside its context bytes"
  | .trailingBytes count => s!"{count} bytes follow the last chunk of the payload"

/-- Run a fallible computation, with its error as a code and a message. -/
def runReqResp {α : Type} (act : Except ReqRespError α) : Result α :=
  act.mapError fun e => (e.code, message e)

/-! ## Sizes -/

@[export eth_reqresp_const_max_payload_size]
def constMaxPayloadSize (_ : Unit) : UInt64 := MAX_PAYLOAD_SIZE

@[export eth_reqresp_const_max_error_message_size]
def constMaxErrorMessageSize (_ : Unit) : UInt64 := MAX_ERROR_MESSAGE_SIZE

/-! ## Operations -/

/-- The bound on the compressed size of `n` bytes. -/
@[export eth_reqresp_max_compressed_len]
def maxCompressedLenExport (n : UInt64) : Result UInt64 :=
  runReqResp ((maxCompressedLen n).mapError .arith)

/-- The SSZ bytes of a request or response payload. -/
@[export eth_reqresp_decode_payload]
def decodePayloadExport (typeMin typeBound : UInt64) (bs : ByteArray) : Result ByteArray :=
  runReqResp (decodePayload typeMin typeBound bs)

/-- The code, the context bytes and the payload of one response chunk. -/
def decodeResponseChunkOf (args : UInt64 × UInt64 × UInt64 × ByteArray) :
    Result (UInt8 × ByteArray × ByteArray) := do
  let (contextBytes, typeMin, typeBound, bs) := args
  let chunk ← runReqResp (decodeResponseChunk contextBytes.toNat typeMin typeBound bs)
  return (chunk.code.toByte, chunk.context, chunk.payload)

/-- The code, the context bytes and the payload of one response chunk.

The arguments are the number of context bytes, the bounds of the payload and the chunk. -/
@[export eth_reqresp_decode_response_chunk]
def decodeResponseChunkExport (args : PyValue) : Result PyValue :=
  pyExport decodeResponseChunkOf args

/-- The payload that holds the SSZ bytes, each chunk of its stream compressed when shorter. -/
@[export eth_reqresp_encode_payload]
def encodePayloadExport (data : ByteArray) : Result ByteArray :=
  pure (encodePayload data)

/-- The response chunk of a code byte, context bytes and a payload, compressed when shorter.

It does not check that the context bytes or the payload fit the code. -/
@[export eth_reqresp_encode_response_chunk]
def encodeResponseChunkExport (code : UInt8) (context payload : ByteArray) : Result ByteArray :=
  pure (encodeResponseChunk ⟨.ofByte code, context, payload⟩)

end EthLib.Networking.ReqResp.Exports
