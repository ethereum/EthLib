import Lean

/-!
# `CheckAccessors`

Lists every defaulting accessor that the specification's elaborated declarations use.

A defaulting accessor returns a value instead of failing.

It does so on an index out of range, or on an empty collection.

- `xs[i]!` and `xs.get! i` return the `Inhabited` default when the index is out of range.
- `xs.set! i v` returns `xs` unchanged when the index is out of range.
- `xs.back!` returns the `Inhabited` default on an empty collection.
- `panic! msg` always returns the `Inhabited` default.

The kernel and the compiled code give the same value.

Compiled code also prints a message to stderr, which nothing checks.

So an input that reaches one is accepted silently, in proofs and in the bindings alike.

The check reads what the kernel accepted, not the source.

A comment or a string that spells `]!` is no finding, and a macro that hides one still is.

A site is named by the accessor it calls and its declaration, with a count.

For example, `GetElem?.getElem! EthLib.Serialization.Ssz.Desc.resolveStep 1` is one entry.

A line number would change with every edit above the site, so the list uses names.

The exact list in `scripts/check_accessors_baseline.txt` may only shrink.

A new site fails the check, and so does an entry that does not match.

The check does not see some ways to fall back to a default.

Each one is covered elsewhere or outside the scope of this check:

- The body of a `partial def` is only in its compiled copy, `foo._unsafe_rec`, which is skipped.
  `lake exe check-decls` rejects `partial` in the specification.
- A wrapper whose name has no `!` is counted once, in its own body.
  Its callers are not counted.
- The explicit defaults, such as `getD`, `headD` and `setIfInBounds`, have no `!` in their names.
  Nor does the deprecated `String.get`, which returns a default character at a bad position.
  They are not in the scope of this check.
-/

open Lean

namespace CheckAccessors

/-- The functions that report a failure and return the `Inhabited` default. -/
def panicFamily : NameSet :=
  .ofList [``panicCore, ``panic, ``panicWithPos, ``panicWithPosWithDecl]

/-- Whether calling `n` can return a default in place of failing.

Lean names every such accessor with `!`, such as `getElem!`, `Array.set!` and `Option.get!`.

The panic functions are the exception, and they are listed by name.

A theorem about one, such as `getElem!_pos`, computes nothing, so it is no accessor. -/
def isDefaulting (env : Environment) (n : Name) : Bool :=
  panicFamily.contains n ||
    ((n.components.any fun c => match c with
        | .str _ s => s.contains '!'
        | _ => false) &&
      !(env.find? n |>.any (· matches .thmInfo _)))

/-- The binder kinds of a constant's arguments, read from its type. -/
def binderInfos (env : Environment) (f : Name) : Array BinderInfo :=
  go ((env.find? f).map (·.type) |>.getD (.sort .zero)) #[]
where
  /-- The binder kinds of the leading `∀`s of a type. -/
  go : Expr → Array BinderInfo → Array BinderInfo
    | .forallE _ _ b bi, acc => go b (acc.push bi)
    | _, acc => acc

/-- Each occurrence of a defaulting accessor in `e`, counted with multiplicity.

Only explicit arguments are searched.

The elaborator copies a term into implicit and instance arguments.

Counting those would count one site several times.

For example, `if xs[i]! ≠ 0 then a else b` elaborates to an `ite` with `xs[i]!` in two places.

One is the explicit condition, and the other is the instance that decides it.

Only the explicit occurrence is counted.

An accessor that appears only inside an implicit argument is missed. -/
partial def occurrences (env : Environment) (e : Expr) (acc : NameMap Nat) : NameMap Nat :=
  match e with
  | .const n _ => if isDefaulting env n then acc.insert n ((acc.getD n 0) + 1) else acc
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let infos := match f with
      | .const n _ => binderInfos env n
      | _ => #[]
    let acc := occurrences env f acc
    (args.zipIdx).foldl (init := acc) fun acc (a, i) =>
      if (infos[i]?.getD .default).isExplicit then occurrences env a acc else acc
  -- A binder type of `∀` is part of a statement, as in `(h : xs[i]! = 0) → ...`.
  | .forallE _ t b _ => occurrences env b (occurrences env t acc)
  | .lam _ _ b _ => occurrences env b acc
  | .letE _ _ v b _ => occurrences env b (occurrences env v acc)
  | .mdata _ b | .proj _ _ b => occurrences env b acc
  | _ => acc

/-- The module that defines `n`. -/
def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  return (← env.header.modules[idx.toNat]?).module

/-- Whether `m` is a module of the specification, whose modules are under `scope`.

It is under `scope`, which is `EthLib` unless `--root` names another directory.

It is also outside every proof and export tree. -/
def isSpecModule (scope m : Name) : Bool :=
  scope.isPrefixOf m && !m.components.contains `Proofs && !m.components.contains `Exports

/-- Whether `n` is a declaration Lean generates from another one, which repeats its source.

- `foo._unsafe_rec` is the compiled copy of a recursive definition.
- `foo._sunfold` is the one-step unfolding of a structural recursion.
- `foo.eq_def`, `foo.eq_unfold` and `foo.eq_1`, `foo.eq_2`, ... are equation lemmas.
- `foo._proof_3` is a proof obligation, stated over the source's terms.
- `foo.match_2` is a matcher, and `foo.match_2.splitter` its splitter.

The kernel's copy of a recursion, `foo._f`, `foo._unary` or `foo._mutual`, is kept.

It holds each site once. -/
def isGenerated (n : Name) : Bool :=
  match n with
  | .str _ s =>
    s == "_unsafe_rec" || s == "_sunfold" || s == "eq_def" || s == "eq_unfold" ||
      (s.startsWith "eq_" && (s.drop 3).all Char.isDigit) ||
      (s.startsWith "_proof_" && (s.drop 7).all Char.isDigit) ||
      (s.startsWith "match_" && (s.drop 6).all Char.isDigit) ||
      s == "splitter"
  | _ => false

/-- One site: the declaration, what part of it, the accessor and its count. -/
structure Site where
  decl : Name
  part : String
  accessor : Name
  count : Nat

/-- For each accessor, the larger of its counts in `a` and in `b`. -/
def larger (a b : NameMap Nat) : NameMap Nat :=
  b.toList.foldl (init := a) fun acc (n, k) => acc.insert n (max k (acc.getD n 0))

/-- Every site in a declaration of the specification.

A definition is searched in its type and its value.

Lean can copy a site of the type into the value, as an explicit argument it fills from the type.

For example, take a definition of type `Decidable (b.get! 0 = 1)` whose source value is `decEq _ _`.

Lean elaborates its value to `decEq (b.get! 0) 1`, which holds the site of the type again.

So a definition counts each accessor once over its type and value.

It takes the larger of the two counts, not their sum.

Two different sites, one in the type and one in the value, then count as one.

A copy that Lean makes inside the value, from an expected type there, still counts again.

A theorem is searched in its statement only: its proof computes nothing.

Generated declarations, such as equation lemmas, repeat their source and are skipped. -/
def sites (env : Environment) (scope : Name) : Array (Name × Site) := Id.run do
  let mut out := #[]
  for (n, c) in env.constants.toList do
    let some m := moduleOf? env n | continue
    unless isSpecModule scope m do continue
    if isGenerated n then continue
    let found : Option (String × NameMap Nat) := match c with
      | .defnInfo v =>
        some ("definition", larger (occurrences env v.type {}) (occurrences env v.value {}))
      | .opaqueInfo v =>
        some ("definition", larger (occurrences env v.type {}) (occurrences env v.value {}))
      | .thmInfo v => some ("statement", occurrences env v.type {})
      | _ => none
    let some (part, counts) := found | continue
    for (a, k) in counts.toList do
      out := out.push (m, ⟨n, part, a, k⟩)
  return out

/-- The source lines of `n`.

A generated name, such as `foo._f`, takes those of the nearest prefix that has them. -/
partial def lines? (env : Environment) (n : Name) : Option (Nat × Nat) :=
  match declRangeExt.find? (level := .server) env n with
  | some r => some (r.range.pos.line, r.range.endPos.line)
  | none => match n with
    | .str p _ | .num p _ => lines? env p
    | .anonymous => none

/-- The name a reader knows a site by.

The kernel's copy of a recursion, `foo._f`, `foo._unary` or `foo._mutual`, is reported as `foo`.

A private name is reported without its private prefix. -/
def displayName (n : Name) : Name :=
  let n := match n with
    | .str p s => if s == "_f" || s == "_unary" || s == "_mutual" then p else n
    | _ => n
  privateToUserName n

/-- The modules of the specification, whose modules are under `scope`.

They are the `.lean` files under the root directory, outside the proof and export trees.

The directory is read, not the imports of `EthLib.lean`.

So a module that the library does not import is not skipped: the build leaves it out, and its import fails. -/
partial def specModules (scope : Name) (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for entry in ← dir.readDir do
    let path := entry.path
    if ← path.isDir then
      out := out ++ (← specModules scope path (pre.str entry.fileName))
    else if path.extension == some "lean" then
      let m := pre.str (path.fileStem.getD "")
      if isSpecModule scope m then out := out.push m
  return out

/-- The baseline: one `accessor declaration count` per line.

`#` comments and blank lines are ignored. -/
def readBaseline (path : System.FilePath) : IO (List (Name × Name × Nat)) := do
  let lines ← IO.FS.lines path
  return lines.toList.filterMap fun line =>
    match (line.splitOn "#").head!.splitOn " " |>.filter (· ≠ "") with
    | [a, d, k] => k.toNat?.map fun k => (a.toName, d.toName, k)
    | _ => none

/-- Entry point: `check-accessors [--list | --print] [--baseline FILE] [--root DIR]`.

- `--list` prints every site as `module part accessor declaration count first-line last-line`.
- `--print` prints the sites in the format of the baseline, to create it once.
- Otherwise the sites, summed over each declaration, must match the baseline exactly.
- `--root` reads the modules under `DIR` in place of `EthLib`.
  The last part of `DIR` is the prefix of their names.
  `scripts/test_check_accessors.sh` points it at the fixtures in `scripts/CheckAccessorsTest`.

It is `unsafe` because loading the environment extensions runs their initializers. -/
unsafe def run (args : List String) : IO UInt32 := do
  let baselinePath : System.FilePath := match args.dropWhile (· != "--baseline") with
    | _ :: p :: _ => p
    | _ => "scripts/check_accessors_baseline.txt"
  let root : System.FilePath := match args.dropWhile (· != "--root") with
    | _ :: p :: _ => p
    | _ => "EthLib"
  let scope : Name := .mkSimple (root.fileName.getD "EthLib")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mods ← specModules scope root scope
  -- `.private` loads the bodies of private and non-exposed definitions too.
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024)
    (loadExts := true) (level := .private)
  -- A scan that sees no definition would pass once the baseline is empty, so it fails.
  let scanned := env.constants.toList.countP fun (n, c) =>
    c matches .defnInfo _ && (moduleOf? env n).any (isSpecModule scope)
  if scanned == 0 then
    IO.eprintln "check-accessors: no definition of the specification was loaded"
    return 3
  let found := sites env scope
  if args.contains "--list" then
    for (m, s) in found do
      let (a, b) := (lines? env s.decl).getD (0, 0)
      IO.println s!"{m}\t{s.part}\t{s.accessor}\t{s.decl}\t{s.count}\t{a}\t{b}"
    return 0
  -- Sum over the parts of a declaration: the list names call sites, not where Lean stores them.
  let mut totals : Std.HashMap (Name × Name) Nat := {}
  for (_, s) in found do
    let key := (s.accessor, displayName s.decl)
    totals := totals.insert key (totals.getD key 0 + s.count)
  let entries := totals.toArray.qsort fun ((a, d), _) ((a', d'), _) =>
    d.toString < d'.toString || (d == d' && a.toString < a'.toString)
  if args.contains "--print" then
    for ((a, d), k) in entries do
      IO.println s!"{a} {d} {k}"
    return 0
  let baseline ← readBaseline baselinePath
  let mut failed := false
  for ((a, d), k) in entries do
    match (baseline.find? fun (a', d', _) => a' == a && d' == d).map (·.2.2) with
    | none =>
      IO.println s!"new: {a} {d} {k}"
      failed := true
    | some k' =>
      if k > k' then
        IO.println s!"more than listed: {a} {d} {k}, listed {k'}"
        failed := true
      else if k < k' then
        IO.println s!"fewer than listed, lower the entry: {a} {d} {k}, listed {k'}"
        failed := true
  for (a, d, k) in baseline do
    unless totals.contains (a, d) do
      IO.println s!"stale baseline entry, no longer found: {a} {d} {k}"
      failed := true
  let total := entries.foldl (fun s (_, k) => s + k) 0
  IO.println (s!"check-accessors: {mods.size} modules, {total} sites in {entries.size} entries, " ++
    s!"baseline {baseline.length} entries")
  return if failed then 1 else 0

end CheckAccessors

unsafe def main (args : List String) : IO UInt32 := CheckAccessors.run args
