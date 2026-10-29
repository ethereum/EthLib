import EthLib.Serialization.Ssz.Codec.Serialize

/-! Length words must represent the exact counts they commit to. -/

namespace EthLib.Serialization.Ssz

/--
Every variable-size count fits the unsigned 256-bit word mixed into its root.
Fixed sizes come from the type and impose no additional count bound.
Type and value admissibility are separate requirements.
-/
inductive CommitmentSized : Desc → Value → Prop
  /-- A boolean carries no variable-size count. -/
  | bool (b : Bool) : CommitmentSized .bool (.bool b)
  /-- An integer carries no variable-size count. -/
  | uint (width n : Nat) : CommitmentSized (.uint width) (.uint n)
  /-- A fixed byte count comes from the type rather than a mixing word. -/
  | byteVector (length : Nat) (data : Bytes) : CommitmentSized (.byteVector length) (.bytes data)
  /-- The actual byte count must fit the unsigned 256-bit mixing word. -/
  | byteList {limit : Nat} {data : Bytes} (count : data.size < 2 ^ 256) :
      CommitmentSized (.byteList limit) (.bytes data)
  /-- A fixed bit count comes from the type rather than a mixing word. -/
  | bitVector (length : Nat) (data : Array Bool) : CommitmentSized (.bitVector length) (.bits data)
  /-- The actual bit count must fit the unsigned 256-bit mixing word. -/
  | bitList {limit : Nat} {data : Array Bool} (count : data.size < 2 ^ 256) :
      CommitmentSized (.bitList limit) (.bits data)
  /-- A progressive bit list still encodes its actual count in 256 bits. -/
  | progressiveBitList {limit : Option Nat} {data : Array Bool} (count : data.size < 2 ^ 256) :
      CommitmentSized (.progressiveBitList limit) (.bits data)
  /-- A fixed element count needs no extra bound, but nested variable counts must fit. -/
  | vector {element : Desc} {length : Nat} {values : List Value}
      (each : ∀ value ∈ values, CommitmentSized element value) :
      CommitmentSized (.vector element length) (.seq values)
  /-- The actual element count and every nested variable count must fit their mixing words. -/
  | list {element : Desc} {limit : Nat} {values : List Value}
      (count : values.length < 2 ^ 256)
      (each : ∀ value ∈ values, CommitmentSized element value) :
      CommitmentSized (.list element limit) (.seq values)
  /-- A progressive element list retains the 256-bit count restriction at every nested level. -/
  | progressiveList {element : Desc} {limit : Option Nat} {values : List Value}
      (count : values.length < 2 ^ 256)
      (each : ∀ value ∈ values, CommitmentSized element value) :
      CommitmentSized (.progressiveList element limit) (.seq values)
  /-- Each field retains the count restrictions of its declared type. -/
  | container {names : List String} {fields : List Desc} {values : List Value}
      (each : ∀ pair ∈ fields.zip values, CommitmentSized pair.1 pair.2) :
      CommitmentSized (.container names fields) (.seq values)
  /-- Only declared fields carry values whose nested counts need bounds. -/
  | progressiveContainer {active : List Bool} {names : List String} {fields : List Desc}
      {values : List Value}
      (each : ∀ pair ∈ fields.zip values, CommitmentSized pair.1 pair.2) :
      CommitmentSized (.progressiveContainer active names fields) (.seq values)
  /-- The selected option inherits its own nested count restrictions. -/
  | compatibleUnion {selectors : List Nat} {options : List Desc} {selector : Nat}
      {option : Desc} {value : Value}
      (named : lookupOption selectors options selector = .ok option)
      (inner : CommitmentSized option value) :
      CommitmentSized (.compatibleUnion selectors options) (.union selector value)

end EthLib.Serialization.Ssz
