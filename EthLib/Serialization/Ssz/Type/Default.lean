module

public import EthLib.Serialization.Ssz.Type.Value
public import EthLib.Serialization.Ssz.Codec.Error

/-! The value a type takes when nothing is supplied, and how to tell one. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

mutual

/--
The default value of a type, which every type but one has:

- An unsigned integer is zero, and a boolean is false.
- A fixed byte array has every byte zero, and a bitvector every bit clear.
- A vector holds the element default at each position.
- A container or progressive container holds the default of each field.
- A list, a bitlist or a progressive list is empty.
- A compatible union has none, since no option is the one to take.

A composite builds from its parts, so a part with no default leaves it none.
-/
def Desc.default : Desc → Except Err Value
  | .bool => .ok (.bool false)
  | .uint _ => .ok (.uint 0)
  | .byteVector length => .ok (.bytes (Array.replicate length 0))
  | .bitVector length => .ok (.bits (Array.replicate length false))
  | .byteList _ => .ok (.bytes #[])
  | .bitList _ => .ok (.bits #[])
  | .progressiveBitList _ => .ok (.bits #[])
  | .list _ _ => .ok (.seq [])
  | .progressiveList _ _ => .ok (.seq [])
  | .vector element length => do
    let one ← element.default
    return .seq (List.replicate length one)
  | .container _ fields => return .seq (← Desc.defaultFields fields)
  | .progressiveContainer _ _ fields => return .seq (← Desc.defaultFields fields)
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

/-- Whether a value is the default of its own type, which the specification calls zeroed. -/
def Desc.isZero (shape : Desc) (value : Value) : Except Err Bool := do
  return (← shape.default) == value

end EthLib.Serialization.Ssz
