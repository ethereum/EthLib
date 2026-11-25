module

public import EthLib.Networking.ReqResp.Encoding
public import EthLib.Serialization.Ssz.Type.Bounds

/-!
# `Networking.ReqResp.Bounds`

The length bounds of a payload of an SSZ type, as the decoder of a payload takes them.

The length of a request or response payload lies within the bounds of its SSZ type.

It is also at most the payload cap of the network, and the lower of the two upper bounds applies.

The bounds of a type are those of `Serialization.Ssz.Type.Bounds`.
-/

@[expose] public section

namespace EthLib.Networking.ReqResp

open EthLib.Serialization.Ssz

/-- The smallest and the largest length of a payload of a type, for a payload cap, in 64 bits.

A type without a largest size takes the payload cap as its largest length.

The smallest is held to one byte past the cap and the largest to the cap.

Both fit in 64 bits when the cap is below `2^64 - 1`. -/
def payloadBounds (maxPayloadSize : UInt64) (shape : Desc) : UInt64 × UInt64 :=
  let cap := maxPayloadSize.toNat
  (UInt64.ofNat (min shape.minSize (cap + 1)), UInt64.ofNat (min (shape.maxSize.getD cap) cap))

end EthLib.Networking.ReqResp
