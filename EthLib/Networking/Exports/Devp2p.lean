module

public import EthLib.Base.Exports
public import EthLib.Networking.Devp2p.P2p

/-!
# `Exports.Devp2p`

C-ABI exports for the messages of the "p2p" capability, callable from the Python C extension.

A message crosses the boundary as its frame data, the message ID then the RLP list.

The flag `snappy` is 1 when the peers compress the messages after Hello, and 0 otherwise.

A rejected message comes back as the code and the message of its error.
-/

public section

namespace EthLib.Networking.Devp2p.Exports

open EthLib.Exports (ExportError Result toResult)

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def message : P2pError → String
  | .rlp _ => "message is not RLP of the expected shape"
  | .snappy _ => "message is not a valid Snappy block"
  | .tooLarge size => s!"message decompresses to {size} bytes, more than {MAX_MESSAGE_SIZE}"
  | .unknownId id => s!"message ID {id} is not a p2p message"

/-- A rejection reaches Python with its code, and its message names the fault. -/
instance : ExportError P2pError where
  code := P2pError.code
  message := message

/-- The uncompressed frame data of the message in the frame data `frameData`. -/
@[export eth_devp2p_decode_message]
def decodeMessageExport (snappy : UInt8) (frameData : ByteArray) : Result ByteArray := do
  let m ← toResult none (decodeMessage (snappy != 0) frameData)
  toResult none (encodeMessage false m)

/-- The frame data of the message in the uncompressed frame data `plain`. -/
@[export eth_devp2p_encode_message]
def encodeMessageExport (snappy : UInt8) (plain : ByteArray) : Result ByteArray := do
  let m ← toResult none (decodeMessage false plain)
  toResult none (encodeMessage (snappy != 0) m)

end EthLib.Networking.Devp2p.Exports
