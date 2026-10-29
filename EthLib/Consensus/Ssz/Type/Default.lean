import EthLib.Consensus.Ssz.Type.Value
import EthLib.Consensus.Ssz.Codec.Error

/-! The value a type takes when nothing is supplied, and how to tell one. -/

namespace EthLib.Consensus.Ssz

mutual

/--
The default value of a type, which every type but one has.

    unsigned integer, boolean          zero, false
    fixed byte array                   every byte zero
    bitvector                          every bit clear
    vector                             the element default, once per position
    container, progressive container   one field default per field
    list, bitlist, progressive lists    empty
    compatible union                   none, since no option is the one to take

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

end EthLib.Consensus.Ssz
