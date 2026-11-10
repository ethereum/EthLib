module

public import EthLib.Base.Exports.PyValue
public meta import Lean.Elab.Command

/-!
# `EthLib.Base.Exports.PyDerive`

A command that writes the conversions of a type to Python values and back.

A structure becomes a `dict` whose keys are its field names in snake case.

Every field has its key, and an option that holds nothing is `None`.

A constructor with no field becomes its name in snake case, as a `str`.

Another constructor becomes a `tuple` of its name in snake case, then its fields.

The type must take no parameter and must not contain itself.

A type is derived once, and other modules import its conversions.

A second command proves the law of these conversions, and that no value becomes `None` or an error.
-/

@[expose] public section

namespace EthLib.Exports

open Lean Elab Command

/-- A name in camel case, in snake case: an upper-case letter becomes `_` and its lower case. -/
meta def snakeCase (s : String) : String :=
  s.foldl (fun out c => if c.isUpper then out ++ "_" ++ c.toLower.toString else out.push c) ""

/-- The value of a key of a `dict`, read as a value of a type. -/
def PyValue.field {α : Type} [FromPy α] (entries : Array (String × PyValue)) (key : String) :
    Except String α :=
  match entries.toList.lookup key with
  | Option.some v => (fromPy v).mapError fun message => s!"{key}: {message}"
  | Option.none => .error s!"no key {key}"

/-- The entries of a `dict`. -/
def PyValue.entries : PyValue → Except String (Array (String × PyValue))
  | .dict entries => .ok entries
  | _ => .error "expected a dict"

/-- The names of the two conversions of a type, in the namespace of the type. -/
meta def pyNames (name : Name) : Ident × Ident :=
  (mkIdent (`_root_ ++ name ++ `toPyValue), mkIdent (`_root_ ++ name ++ `ofPyValue))

/-- The conversions of a structure. -/
meta def deriveStructure (t : Ident) (name : Name) : CommandElabM Unit := do
  let (toF, ofF) := pyNames name
  let fields := getStructureFieldsFlattened (← getEnv) name (includeSubobjectFields := false)
  let keys := fields.map fun f => Syntax.mkStrLit (snakeCase f.toString)
  let ids := fields.map mkIdent
  -- A quotation splices each array under one name only, so the values take a second name.
  let vars := ids
  let x := mkIdent `x
  let values ← ids.mapM fun f => `(toPy ($x).$f:ident)
  elabCommand (← `(def $toF ($x : $t) : PyValue := .dict #[$[($keys, $values)],*]))
  elabCommand (← `(def $ofF (v : PyValue) : Except String $t := do
    let entries ← PyValue.entries v
    $[let $ids:ident ← PyValue.field entries $keys]*
    return { $[$ids:ident := $vars],* }))

/-- The conversions of an inductive type.

The fields of a constructor cross as the items of a flat tuple, after its name. -/
meta def deriveInductive (t : Ident) (name : Name) : CommandElabM Unit := do
  let (toF, ofF) := pyNames name
  let info ← getConstInfoInduct name
  let mut toAlts := #[]
  let mut nullary : Term ← `(.error s!"no constructor is named {tag}")
  let mut withFields : Term ← `(.error s!"no constructor is named {tag}")
  for ctor in info.ctors.reverse do
    let cinfo ← getConstInfoCtor ctor
    let tag := Syntax.mkStrLit (snakeCase ctor.getString!)
    let args := (Array.range cinfo.numFields).map fun i => mkIdent (.mkSimple s!"a{i}")
    let c := mkIdent ctor
    if args.isEmpty then
      toAlts := toAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $c:ident => .str $tag))
      nullary ← `(if tag = $tag then .ok $c:ident else $nullary)
    else
      let types ← liftTermElabM <| Meta.forallTelescopeReducing cinfo.type fun xs _ =>
        xs.mapM fun x => do PrettyPrinter.delab (← Meta.inferType x)
      let tuple ← args.pop.foldrM (fun a acc => `(($a, $acc))) (args.back! : Term)
      let product ← types.pop.foldrM (fun ty acc => `($ty × $acc)) types.back!
      toAlts := toAlts.push (← `(Lean.Parser.Term.matchAltExpr|
        | $c:ident $args* => .tuple (.str $tag :: ToPyItems.items $tuple).toArray))
      withFields ← `(if tag = $tag then
          (fun ($tuple : $product) => $c:ident $args*) <$> FromPyItems.ofItems rest
        else $withFields)
  elabCommand (← `(def $toF (x : $t) : PyValue := match x with $toAlts:matchAlt*))
  elabCommand (← `(def $ofF (v : PyValue) : Except String $t :=
    match v with
    | .str tag => $nullary
    | .tuple items =>
      match items.toList with
      | .str tag :: rest => $withFields
      | _ => .error "expected the name of a constructor first"
    | _ => .error "expected a str or a tuple"))

/-- Write the conversions of a type to Python values and back. -/
elab "derive_py " t:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  if isStructure (← getEnv) name then deriveStructure t name
  else deriveInductive t name
  let (toF, ofF) := pyNames name
  elabCommand (← `(instance : ToPy $t := ⟨$toF⟩))
  elabCommand (← `(instance : FromPy $t := ⟨$ofF⟩))

/-- Prove that reading back the Python value of each value of a type gives that value.

Prove also that no value becomes `None` or an error, since each is a `dict`, a `str` or a `tuple`.

Each type of a field must have the law of its conversions already. -/
elab "derive_py_laws " t:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let (toF, ofF) := pyNames name
  elabCommand (← `(instance : PlainPy $t where
    isPlain_toPy x := by
      show ($toF x).isPlain = Bool.true
      cases x <;> rfl))
  elabCommand (← `(instance : LawfulPy $t where
    fromPy_toPy x := by
      show $ofF ($toF x) = .ok x
      cases x <;> simp [$toF:ident, $ofF:ident, PyValue.entries, PyValue.field,
        LawfulPy.fromPy_toPy, LawfulPyItems.ofItems_items, bind, Except.bind, pure, Except.pure,
        List.lookup, Except.mapError, Functor.map, Except.map]))

end EthLib.Exports
