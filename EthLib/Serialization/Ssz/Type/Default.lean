module

public import EthLib.Serialization.Ssz.Type.Value
public import EthLib.Serialization.Ssz.Error

/-!
The value a type takes when nothing is supplied, and how to tell one.

The core default values are stated in EthLib's own terms, one per comment.

[EIP-7916][eip7916], [EIP-7495][eip7495] and [EIP-8016][eip8016] give those of their types.

[eip7916]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7916.md#progressivelisttype-and-progressivebitlist
[eip7495]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7495.md#progressivecontaineractive_fields
[eip8016]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-8016.md#compatibleunionselector-type
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

mutual

/--
The default value of a type, which a compatible union lacks.

A composite builds from its parts, so a part with no default leaves it none.
-/
def Desc.default : Desc → Except Err Value
  -- boolean: false.
  | .bool => .ok (.bool false)
  -- uintN: 0.
  | .uint _ => .ok (.uint 0)
  -- ByteVector[N]: `N` zero bytes, as for a Vector[byte, N].
  | .byteVector length => .ok (.bytes (Array.replicate length 0))
  -- Bitvector[N]: `N` bits, each false.
  | .bitVector length => .ok (.bits (Array.replicate length false))
  -- ByteList[N]: the empty list.
  | .byteList _ => .ok (.bytes #[])
  -- Bitlist[N]: the empty list.
  | .bitList _ => .ok (.bits #[])
  -- EIP-7916: a ProgressiveBitlist is the empty list.
  | .progressiveBitList _ => .ok (.bits #[])
  -- List[type, N]: the empty list.
  | .list _ _ => .ok (.seq [])
  -- EIP-7916: a ProgressiveList[type] is the empty list.
  | .progressiveList _ _ => .ok (.seq [])
  -- Vector[type, N]: the default of the element type, `N` times.
  | .vector element length => do
    let one ← element.default
    return .seq (List.replicate length one)
  -- Container: the default of each field type, in order.
  | .container _ fields => return .seq (← Desc.defaultFields fields)
  -- EIP-7495: a ProgressiveContainer is the default of each field type, in order.
  | .progressiveContainer _ _ fields => return .seq (← Desc.defaultFields fields)
  -- EIP-8016: a CompatibleUnion has no default value, and asking for one is an error.
  --
  -- A union would have to pick an option, and no option is the one to pick.
  | .compatibleUnion _ _ => .error .noDefault

/-- The default of each field of a struct. -/
def Desc.defaultFields : List Desc → Except Err (List Value)
  | [] => .ok []
  | field :: rest => do
    let head ← field.default
    let tail ← Desc.defaultFields rest
    return head :: tail

end

/-- Whether a value is the default of its own type, which SSZ calls zeroed. -/
def Desc.isZero (shape : Desc) (value : Value) : Except Err Bool := do
  return (← shape.default) == value

end EthLib.Serialization.Ssz
