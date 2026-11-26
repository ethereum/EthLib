module

public import EthLib.Base.Proofs.Bytes
public import Mathlib.Logic.Equiv.Defs

/-!
# Proofs: a list of bytes and a byte array are the same byte string

The two views of a byte string are in bijection.
-/

@[expose] public section

namespace EthLib.Base

/-- The bijection between lists of bytes and byte arrays. -/
def listEquivByteArray : List UInt8 ≃ ByteArray where
  toFun := List.toByteArray
  invFun bytes := bytes.data.toList
  left_inv _ := List.toList_data_toByteArray
  right_inv := toByteArray_data_toList

end EthLib.Base
