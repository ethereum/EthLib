module

public import EthLib.Base.Exports
public import EthLib.Networking.Exports.Fork
public import EthLib.Networking.ReqResp.Encoding

/-!
# `Exports.ReqResp`

C-ABI exports for the `ssz_snappy` encoding of requests and responses.

Each operation takes the whole message.

A rejected message comes back as the code and the message of its error.

An unknown fork name has code 0, which no error of the encoding has.

A response chunk comes back as one byte string: its code, its context bytes, then its payload.
-/

public section

namespace EthLib.Networking.ReqResp.Exports

open EthLib.Exports (Result)

open EthLib.Networking.Exports (forkAt)

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def message : ReqRespError → String
  | .varint _ => "length prefix is not a valid varint"
  | .lengthOutOfBounds declared bound => s!"declared length {declared} is above {bound}"
  | .arith _ => "bound on the compressed size is 2^64 or more"
  | .compressedTooLong size bound => s!"{size} compressed bytes, more than {bound}"
  | .frame _ => "payload is not a valid Snappy framed stream"
  | .lengthMismatch declared size => s!"payload has {size} bytes, not the declared {declared}"
  | .missingCode => "response chunk has no response code"
  | .contextTruncated => "response chunk ends inside its context bytes"

/-- Run a fallible computation, with its error as a code and a message. -/
def runReqResp {α : Type} (act : Except ReqRespError α) : Result α :=
  act.mapError fun e => (e.code, message e)

/-! ## Sizes -/

@[export eth_reqresp_const_max_error_message_size]
def constMaxErrorMessageSize (_ : Unit) : UInt64 := MAX_ERROR_MESSAGE_SIZE

/-! ## Operations -/

/-- The payload cap at the named fork. -/
@[export eth_reqresp_max_payload_size]
def maxPayloadSizeExport (fork : ByteArray) : Result UInt64 := do
  return maxPayloadSize (← forkAt fork)

/-- The bound on the compressed size of `n` bytes. -/
@[export eth_reqresp_max_compressed_len]
def maxCompressedLenExport (n : UInt64) : Result UInt64 :=
  runReqResp ((maxCompressedLen n).mapError .arith)

/-- The SSZ bytes of a request or response payload. -/
@[export eth_reqresp_decode_payload]
def decodePayloadExport (fork : ByteArray) (typeBound : UInt64) (bs : ByteArray) :
    Result ByteArray := do
  runReqResp (decodePayload (← forkAt fork) typeBound bs)

/-- The code, the context bytes and the payload of one response chunk, as one byte string. -/
@[export eth_reqresp_decode_response_chunk]
def decodeResponseChunkExport (fork : ByteArray) (contextBytes typeBound : UInt64)
    (bs : ByteArray) : Result ByteArray := do
  let chunk ← runReqResp (decodeResponseChunk (← forkAt fork) contextBytes.toNat typeBound bs)
  return ⟨#[chunk.code.toByte]⟩ ++ chunk.context ++ chunk.payload

end EthLib.Networking.ReqResp.Exports
