module

public import EthLib.Networking.ReqResp.Encoding
public import EthLib.Serialization.Ssz.Type.Bounds

/-!
# `Networking.ReqResp.Bounds`

The length bounds of a payload of an SSZ type, as the decoder of a payload takes them.

The length of a request or response payload lies within the bounds of its SSZ type.

It is also at most `MAX_PAYLOAD_SIZE`, and the lower of the two upper bounds applies.

The bounds of a type are those of `Serialization.Ssz.Type.Bounds`.
-/

@[expose] public section

namespace EthLib.Networking.ReqResp

open EthLib.Serialization.Ssz

/-- The smallest and the largest length of a payload of a type, as 64-bit integers.

A type without a largest size takes the payload cap as its largest length.

Each bound is held to one byte past the cap, so it fits in 64 bits and keeps its meaning. -/
def payloadBounds (shape : Desc) : UInt64 × UInt64 :=
  let cap := MAX_PAYLOAD_SIZE.toNat
  (UInt64.ofNat (min shape.minSize (cap + 1)), UInt64.ofNat (min (shape.maxSize.getD cap) cap))

end EthLib.Networking.ReqResp
