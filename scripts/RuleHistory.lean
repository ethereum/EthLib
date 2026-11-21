import Lean

/-!
# `RuleHistory`

Writes the value of each fork-indexed rule at each fork, so that a change at an earlier fork shows.

`tests/execution/history/README.md` says why the file exists and how a pull request changes it.

A rule here is a definition of the execution layer or of `Base`.

Its value depends only on the fork.

The tool finds the rules by their type, so a new rule is listed without editing this file.

- A constant of type `Nat` gives one value for every fork.
- A rule from the fork to `Nat` gives one value per fork.
- A rule from the fork and a `Bool` to `Nat` gives two values per fork, one per `Bool`.
- A rule from the fork to `Option Nat` gives one value per fork, or none.
- A rule from the fork to a structure gives one value per field of type `Nat`.
- A rule whose structure is given from a fork on gives those values from that fork, and none before.

It skips every other type, such as a list of addresses or an opcode table.

It also skips a rule that takes another argument, such as a preset or a chain configuration.

It reads the declarations that the two modules of the execution layer and of `Base` import.

It reads the forks from the constructors of `Fork`, in order, so it never names the last fork.

It reads the values from compiled code, so it runs after `lake build EthLib`.

- `lake exe rule-history` writes `tests/execution/history/rules.tsv`.
- `lake exe rule-history --check` fails if that file differs, and prints the changed lines.

It exits with 1 when the file differs, 2 on an unknown argument, and 3 when it finds no rule.

It also exits with 3 when it finds no fork type.

Four options replace the defaults, for the fixtures of `scripts/test_rule_history.sh`.

- `--module M` reads the rules of module `M`, in place of the two default modules.
- `--scope N` reads only the declarations under the namespace `N`.
- `--base B` reads the fork type and its from-a-fork wrapper under `B`, in place of `Base`.
- `--file F` writes or checks the file `F`.
-/

open Lean Meta

namespace RuleHistory

/-- What the tool reads, and the file it writes. -/
structure Config where
  /-- The modules whose rules are read. -/
  modules : Array Name := #[`EthLib.Execution, `EthLib.Base]
  /-- The namespaces in which a rule is looked for. -/
  scopes : List Name := [`EthLib.Execution, `EthLib.Base]
  /-- The namespace of the fork type `Fork` and of `Since`, which gives a value from a fork on. -/
  base : Name := `EthLib.Base
  /-- The snapshot, relative to the repository root. -/
  file : System.FilePath := "tests/execution/history/rules.tsv"
  /-- Whether to compare with the file instead of writing it. -/
  check : Bool := false

/-- The fork type. -/
def Config.forkType (c : Config) : Name := c.base ++ `Fork

/-- The type constructor that gives a value only from a fork on. -/
def Config.sinceType (c : Config) : Name := c.base ++ `Since

/-- How a rule's value at one fork is read. -/
inductive Shape where
  /-- A constant `Nat`. -/
  | const
  /-- `Fork → Nat`. -/
  | nat
  /-- `Fork → Bool → Nat`, at one value of the `Bool`. -/
  | bool (arg : Bool)
  /-- `Fork → Option Nat`. -/
  | option
  /-- `Fork → S`, one field of `S` of type `Nat`. -/
  | field (proj : Name)
  /-- `(fork : Fork) → Since first fork S`, one field of `S` of type `Nat`. -/
  | since (first : Name) (proj : Name)
  deriving Inhabited

/-- One rule: the declaration and how to read it. -/
structure Rule where
  decl : Name
  shape : Shape
  deriving Inhabited

/-- The `Nat` type. -/
def natE : Expr := mkConst ``Nat

/-- The type `Option Nat`. -/
def optNatE : Expr := mkApp (mkConst ``Option [Level.zero]) natE

/-- The projections of the fields of `S` whose type is `Nat`, in the order of the fields. -/
def natFields (env : Environment) (s : Name) : List Name :=
  if !isStructure env s then [] else
    (getStructureFields env s).toList.filterMap fun f =>
      let proj := s ++ f
      match env.find? proj with
      | some info =>
        match info.type with
        | .forallE _ (.const s' []) (.const ``Nat []) _ => if s' == s then some proj else none
        | _ => none
      | none => none

/-- Whether a type is `Bool → Nat`. -/
def isBoolToNat : Expr → Bool
  | .forallE _ (.const ``Bool []) (.const ``Nat []) _ => true
  | _ => false

/-- The ways to read a declaration of type `ty`, or none if it is not a rule. -/
def shapesOf (c : Config) (env : Environment) (ty : Expr) : List Shape :=
  if ty == natE then [.const] else
  match ty with
  | .forallE _ (.const d []) body _ =>
    if d != c.forkType then [] else
    if !body.hasLooseBVars then
      if body == natE then [.nat]
      else if isBoolToNat body then [.bool false, .bool true]
      else if body == optNatE then [.option]
      else match body with
        | .const s [] => (natFields env s).map .field
        | _ => []
    else
      -- `Since first fork S`, where `fork` is the bound variable.
      match body.getAppFn.constName?, body.getAppArgs with
      | some k, #[.const first [], .bvar 0, .const s []] =>
        if k == c.sinceType then (natFields env s).map (.since first) else []
      | _, _ => []
  | _ => []

/-- A key that orders the shapes of one declaration. -/
def shapeKey : Shape → String
  | .const => "0"
  | .nat => "1"
  | .bool b => s!"2{b}"
  | .option => "3"
  | .field p => s!"4{p}"
  | .since _ p => s!"5{p}"

/-- Every rule of the loaded modules, sorted by name. -/
def rules (c : Config) (env : Environment) : Array Rule := Id.run do
  let mut out := #[]
  for (n, info) in env.constants.map₁.toList do
    let .defnInfo d := info | continue
    unless d.levelParams.isEmpty do continue
    unless c.scopes.any (·.isPrefixOf n) do continue
    -- The order of the forks is not a rule.
    if n.isInternalDetail || c.forkType.isPrefixOf n || isInstanceCore env n then continue
    for shape in shapesOf c env d.type do
      out := out.push { decl := n, shape }
  return out.qsort fun a b =>
    a.decl.toString < b.decl.toString ||
      (a.decl == b.decl && shapeKey a.shape < shapeKey b.shape)

/-- The constructors of the fork type, in the order of the type, or none if it is missing. -/
def forks (c : Config) (env : Environment) : Option (List Name) :=
  match env.find? c.forkType with
  | some (.inductInfo info) => some info.ctors
  | _ => none

/-- The value of a rule at a fork, as a term of type `Option Nat`. -/
def valueTerm (fs : List Name) (r : Rule) (fork : Name) : MetaM Expr := do
  let some_ (e : Expr) := mkApp2 (mkConst ``Option.some [Level.zero]) natE e
  let at_ := mkApp (mkConst r.decl) (mkConst fork)
  match r.shape with
  | .const => return some_ (mkConst r.decl)
  | .nat => return some_ at_
  | .bool b => return some_ (mkApp at_ (toExpr b))
  | .option => return at_
  | .field p => return some_ (mkApp (mkConst p) at_)
  | .since first p =>
    if fs.idxOf first ≤ fs.idxOf fork then
      -- The compiler erases the proof that the fork is reached, so `lcProof` stands in for it.
      let reached ← mkAppM ``LE.le #[mkConst first, mkConst fork]
      return some_ (mkApp (mkConst p) (mkApp at_ (mkApp (mkConst ``lcProof) reached)))
    else
      return mkApp (mkConst ``Option.none [Level.zero]) natE

/-- The values of a rule at every fork, in the order of the forks. -/
unsafe def values (fs : List Name) (r : Rule) : MetaM (List (Option Nat)) := do
  let terms ← fs.mapM (valueTerm fs r)
  let list ← mkListLit optNatE terms
  -- `lcProof` makes the term unsafe, which is fine for a term that is only run.
  evalExpr (List (Option Nat)) (mkApp (mkConst ``List [Level.zero]) optNatE) list
    (safety := .unsafe)

/-- The name of a declaration, without the `EthLib.` prefix. -/
def shortName (n : Name) : String :=
  (n.replacePrefix `EthLib .anonymous).toString

/-- The last component of a name. -/
def lastName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

/-- The rule as text, with `·` for the fork. -/
def ruleText (r : Rule) : String :=
  let d := shortName r.decl
  match r.shape with
  | .const => d
  | .nat | .option => s!"{d} ·"
  | .bool b => s!"{d} · {b}"
  | .field p => s!"({d} ·).{lastName p}"
  | .since _ p => s!"({d} · _).{lastName p}"

/-- A value as text: `some v` and `none` where the rule may have no value. -/
def literal (r : Rule) : Option Nat → String
  | none => "none"
  | some v => match r.shape with
    | .option | .since .. => s!"some {v}"
    | _ => toString v

/-- The lines of the snapshot: rule, fork and value, separated by tabs. -/
def snapshotLines (fs : List Name) (rs : Array (Rule × List (Option Nat))) : List String :=
  rs.toList.flatMap fun (r, vs) =>
    match r.shape, vs with
    | .const, v :: _ => [s!"{ruleText r}\t-\t{literal r v}"]
    | .const, [] => []
    | _, _ => (fs.zip vs).map fun (f, v) => s!"{ruleText r}\t{lastName f}\t{literal r v}"

/-- The text of the snapshot file. -/
def snapshotText (fs : List Name) (rs : Array (Rule × List (Option Nat))) : String :=
  let header := [
    "# Generated by `lake exe rule-history` from compiled code. Do not edit by hand.",
    "# Each line is a rule, a fork (- for a constant) and the value that the code computes.",
    "# A pull request that changes a line names the source that requires the new value."]
  "\n".intercalate (header ++ snapshotLines fs rs) ++ "\n"

/-- Read the options, or fail with the usage. -/
def parse : Config → List String → Except String Config
  | c, [] => .ok c
  | c, "--check" :: rest => parse { c with check := true } rest
  | c, "--module" :: m :: rest =>
    -- The first `--module` replaces the default modules, and later ones add to it.
    let mods := if c.modules == ({} : Config).modules then #[] else c.modules
    parse { c with modules := mods.push m.toName } rest
  | c, "--scope" :: s :: rest =>
    let scopes := if c.scopes == ({} : Config).scopes then [] else c.scopes
    parse { c with scopes := scopes ++ [s.toName] } rest
  | c, "--base" :: b :: rest => parse { c with base := b.toName } rest
  | c, "--file" :: f :: rest => parse { c with file := f } rest
  | _, a :: _ => .error s!"unknown argument {a}"

/-- The usage line. -/
def usage : String :=
  "usage: lake exe rule-history [--check] [--module M]... [--scope N]... [--base B] [--file F]"

unsafe def run (args : List String) : IO UInt32 := do
  if let .error e := parse {} args then
    IO.eprintln e
    IO.eprintln usage
    return 2
  let .ok c := parse {} args | return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (c.modules.map fun m => { module := m }) {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<rule-history>", fileMap := default }
  let some fs := forks c env | do
    IO.eprintln s!"rule-history: no inductive type {c.forkType} in the loaded modules"
    return 3
  let rs := rules c env
  if rs.isEmpty then
    IO.eprintln s!"rule-history: no rule under {c.scopes} in the loaded modules"
    return 3
  let act : MetaM (Array (Rule × List (Option Nat))) := rs.mapM fun r => do
    return (r, ← values fs r)
  let (vals, _) ← (act.run' {} |>.toIO ctx { env })
  let text := snapshotText fs vals
  if c.check then
    let old ← if ← c.file.pathExists then IO.FS.readFile c.file else pure ""
    if old == text then
      IO.println s!"rule-history: {vals.size} rules at {fs.length} forks agree with {c.file}"
      return 0
    let oldLines := old.splitOn "\n"
    let newLines := text.splitOn "\n"
    for l in oldLines do
      unless newLines.contains l do IO.println s!"- {l}"
    for l in newLines do
      unless oldLines.contains l do IO.println s!"+ {l}"
    IO.eprintln s!"rule-history: the code computes other values than {c.file}"
    IO.eprintln "If the change is intended, run `lake exe rule-history` to rewrite the file."
    IO.eprintln "Then name the source of each changed line in the pull request."
    return 1
  if let some d := c.file.parent then IO.FS.createDirAll d
  IO.FS.writeFile c.file text
  IO.println s!"rule-history: wrote {vals.size} rules at {fs.length} forks to {c.file}"
  return 0

end RuleHistory

unsafe def main (args : List String) : IO UInt32 := RuleHistory.run args
