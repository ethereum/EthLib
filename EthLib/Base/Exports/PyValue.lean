module

public import EthLib.Base.Exports

/-!
# `EthLib.Base.Exports.PyValue`

The values that cross the boundary between Lean and Python.

Each constructor stands for one kind of Python value.

One generic converter in the C layer turns these values into Python objects and back.

So no export writes or reads a byte format of its own.

A type crosses the boundary through a conversion to these values and a conversion back.

Its law says that reading back what a value writes gives that value.
-/

@[expose] public section

namespace EthLib.Exports

/-- A Python value, as the C layer converts it.

Each constructor has at most one field, and that field is a Lean object.

The C layer relies on this layout. -/
inductive PyValue where
  /-- `None`. -/
  | none
  /-- `False`. -/
  | false
  /-- `True`. -/
  | true
  /-- An `int` that is not negative. -/
  | int (n : Nat)
  /-- A `bytes`. -/
  | bytes (data : ByteArray)
  /-- A `str`. -/
  | str (s : String)
  /-- A `list`. -/
  | list (items : Array PyValue)
  /-- A `tuple`. -/
  | tuple (items : Array PyValue)
  /-- A `dict` whose keys are `str`, in its order. -/
  | dict (entries : Array (String × PyValue))
  /-- An error inside a result, as its code and its message.

  Python receives an instance of the error class of the method. -/
  | failure (error : UInt32 × String)
  deriving Inhabited

namespace PyValue

/-- Whether a value is neither `None` nor an error. -/
def isPlain : PyValue → Bool
  | .none | .failure _ => Bool.false
  | _ => Bool.true

end PyValue

/-- A type whose values Python can receive. -/
class ToPy (α : Type) where
  /-- The Python value of a value. -/
  toPy : α → PyValue

/-- A type whose values Python can give. -/
class FromPy (α : Type) where
  /-- The value that a Python value stands for, or why it stands for none. -/
  fromPy : PyValue → Except String α

export ToPy (toPy)
export FromPy (fromPy)

/-- Reading back the Python value of a value gives that value.

So two different values never become one value of the type above. -/
class LawfulPy (α : Type) [ToPy α] [FromPy α] : Prop where
  /-- Reading back the Python value of a value gives that value. -/
  fromPy_toPy (a : α) : fromPy (toPy a) = .ok a

/-- No value of the type becomes `None` or an error.

An optional value, or a result that may be an error, then tells its cases apart. -/
class PlainPy (α : Type) [ToPy α] : Prop where
  /-- No value becomes `None` or an error. -/
  isPlain_toPy (a : α) : (toPy a).isPlain = Bool.true

instance : ToPy PyValue := ⟨id⟩

instance : FromPy PyValue := ⟨.ok⟩

instance : ToPy Unit := ⟨fun _ => .none⟩

instance : FromPy Unit := ⟨fun
  | .none => .ok ()
  | _ => .error "expected None"⟩

instance : ToPy Bool := ⟨fun b => if b then .true else .false⟩

instance : FromPy Bool := ⟨fun
  | .false => .ok Bool.false
  | .true => .ok Bool.true
  | _ => .error "expected a bool"⟩

instance : ToPy Nat := ⟨.int⟩

instance : FromPy Nat := ⟨fun
  | .int n => .ok n
  | _ => .error "expected an int"⟩

/-- A natural number below a bound, read from Python. -/
def fromPyBelow (bound : Nat) (v : PyValue) : Except String { n : Nat // n < bound } := do
  let n ← fromPy (α := Nat) v
  if h : n < bound then return ⟨n, h⟩
  else throw s!"expected an int below {bound}, got {n}"

instance : ToPy UInt8 := ⟨fun n => .int n.toNat⟩

instance : FromPy UInt8 := ⟨fun v => do return UInt8.ofNatLT _ (← fromPyBelow UInt8.size v).2⟩

instance : ToPy UInt16 := ⟨fun n => .int n.toNat⟩

instance : FromPy UInt16 := ⟨fun v => do return UInt16.ofNatLT _ (← fromPyBelow UInt16.size v).2⟩

instance : ToPy UInt32 := ⟨fun n => .int n.toNat⟩

instance : FromPy UInt32 := ⟨fun v => do return UInt32.ofNatLT _ (← fromPyBelow UInt32.size v).2⟩

instance : ToPy UInt64 := ⟨fun n => .int n.toNat⟩

instance : FromPy UInt64 := ⟨fun v => do return UInt64.ofNatLT _ (← fromPyBelow UInt64.size v).2⟩

instance : ToPy ByteArray := ⟨.bytes⟩

instance : FromPy ByteArray := ⟨fun
  | .bytes data => .ok data
  | _ => .error "expected bytes"⟩

instance {n : Nat} : ToPy (Vector UInt8 n) := ⟨fun v => .bytes ⟨v.toArray⟩⟩

instance {n : Nat} : FromPy (Vector UInt8 n) := ⟨fun v => do
  let data ← fromPy (α := ByteArray) v
  if h : data.data.size = n then return ⟨data.data, h⟩
  else throw s!"expected {n} bytes, got {data.size}"⟩

instance : ToPy String := ⟨.str⟩

instance : FromPy String := ⟨fun
  | .str s => .ok s
  | _ => .error "expected a str"⟩

instance {α : Type} [ToPy α] : ToPy (Option α) := ⟨fun
  | none => .none
  | some a => toPy a⟩

instance {α : Type} [FromPy α] : FromPy (Option α) := ⟨fun
  | .none => .ok none
  | v => some <$> fromPy v⟩

/-- The items of a sequence: a list, or a tuple, which Python callers often pass instead. -/
def PyValue.sequence : PyValue → Except String (Array PyValue)
  | .list items | .tuple items => .ok items
  | _ => .error "expected a list or a tuple"

instance {α : Type} [ToPy α] : ToPy (Array α) := ⟨fun xs => .list (xs.map toPy)⟩

instance {α : Type} [FromPy α] : FromPy (Array α) := ⟨fun v => do
  (← v.sequence).mapM fromPy⟩

instance {α : Type} [ToPy α] : ToPy (List α) := ⟨fun xs => .list (xs.map toPy).toArray⟩

instance {α : Type} [FromPy α] : FromPy (List α) := ⟨fun v => do
  (← v.sequence).toList.mapM fromPy⟩

/-- A type whose values Python receives as the items of a tuple. -/
class ToPyItems (α : Type) where
  /-- The items of a value. -/
  items : α → List PyValue

/-- A type whose values Python gives as the items of a tuple. -/
class FromPyItems (α : Type) where
  /-- The value that items stand for, or why they stand for none. -/
  ofItems : List PyValue → Except String α

/-- Reading back the items of a value gives that value. -/
class LawfulPyItems (α : Type) [ToPyItems α] [FromPyItems α] : Prop where
  /-- Reading back the items of a value gives that value. -/
  ofItems_items (a : α) : FromPyItems.ofItems (ToPyItems.items a) = .ok a

/-- A value that is not a pair is one item. -/
instance (priority := low) {α : Type} [ToPy α] : ToPyItems α := ⟨fun a => [toPy a]⟩

/-- A value that is not a pair is one item. -/
instance (priority := low) {α : Type} [FromPy α] : FromPyItems α := ⟨fun
  | [v] => fromPy v
  | [] => .error "a tuple has fewer items than expected"
  | _ => .error "a tuple has more items than expected"⟩

/-- A pair is its first component, then the items of its second. -/
instance {α β : Type} [ToPy α] [ToPyItems β] : ToPyItems (α × β) := ⟨fun (a, b) =>
  toPy a :: ToPyItems.items b⟩

/-- A pair is its first component, then the items of its second. -/
instance {α β : Type} [FromPy α] [FromPyItems β] : FromPyItems (α × β) := ⟨fun
  | v :: vs => do return (← fromPy v, ← FromPyItems.ofItems vs)
  | [] => .error "a tuple has fewer items than expected"⟩

/-- A pair, or a nest of pairs to the right, is one flat tuple. -/
instance {α β : Type} [ToPy α] [ToPyItems β] : ToPy (α × β) := ⟨fun p =>
  .tuple (ToPyItems.items p).toArray⟩

/-- A pair, or a nest of pairs to the right, is one flat tuple. -/
instance {α β : Type} [FromPy α] [FromPyItems β] : FromPy (α × β) := ⟨fun
  | .tuple items => FromPyItems.ofItems items.toList
  | _ => .error "expected a tuple"⟩

/-- A result that may be an error inside a larger result: the error crosses as a failure. -/
instance {α : Type} [ToPy α] : ToPy (Except (UInt32 × String) α) := ⟨fun
  | .error e => .failure e
  | .ok a => toPy a⟩

/-- A result that may be an error inside a larger result: the error crosses as a failure. -/
instance {α : Type} [FromPy α] : FromPy (Except (UInt32 × String) α) := ⟨fun
  | .failure e => .ok (.error e)
  | v => .ok <$> fromPy v⟩

/-- An export between Python values, from a function of typed values.

It reads the tuple of its arguments, runs the function and writes the result.

Arguments that it cannot read fail with code 0.

The type of the result must have the law, so two results never become one value. -/
def pyExport {α β : Type} [FromPyItems α] [ToPy β] [FromPy β] [LawfulPy β]
    (f : α → Result β) (args : PyValue) : Result PyValue := do
  let items ← match args with
    | .tuple items => pure items.toList
    | _ => throw (0, "the arguments are not a tuple")
  let a ← (FromPyItems.ofItems items).mapError fun message => (0, message)
  return toPy (← f a)

/-- The digits of a number in base 16, which the C layer reads for a large `int`. -/
@[export eth_pyvalue_nat_to_hex]
def natToHex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The value of a digit in base 16, in lower case. -/
def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

/-- The number that lower-case digits in base 16 write, for a large `int` from the C layer. -/
@[export eth_pyvalue_nat_of_hex]
def natOfHex (digits : String) : Nat :=
  digits.foldl (fun n c => 16 * n + hexDigit c) 0

end EthLib.Exports
