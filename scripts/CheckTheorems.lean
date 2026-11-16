import Lean
import Lean.Server.References
import CheckTheoremAttributes

/-!
# Theorems in specification modules

The check keeps the theorems that specification definitions and instances use.

A persistent simplification attribute also exempts a theorem.

The dependencies of every retained theorem stay with it.

Other explicit persistent theorem attributes stop the check until they have a placement rule.

All other theorems belong in the property library.

The check reads declaration types, private bodies and elaborated references from build artifacts.

Generated declarations belong to their source declaration rather than to the migration baseline.

An exact baseline permits existing findings, and rejects new and stale entries.
-/

open Lean

namespace CheckTheorems

/-- The defining module, regardless of the declaration's namespace or private prefix. -/
def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  return (← env.header.modules[idx.toNat]?).module

/-- Specification modules exclude every property and export tree. -/
def isSpecModule (scope m : Name) : Bool :=
  scope.isPrefixOf m && !m.components.contains `Proofs && !m.components.contains `Exports

/-- Source positions in their file order. -/
def positionLE (a b : Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.column ≤ b.column)

/-- A declaration's range contains the other declaration's range. -/
def containsRange (outer inner : DeclarationRanges) : Bool :=
  positionLE outer.range.pos inner.range.pos &&
    positionLE inner.range.endPos outer.range.endPos

/-- Resolve a user-facing name within its defining module, including private declarations. -/
abbrev NameIndex := Std.HashMap (Name × Name) (Array Name)

/-- The nearest declaration that owns a generated or local auxiliary.

A source declaration outside the parent's range is independent, even if its name looks generated.

The source ranges also identify a `where` definition inside a theorem's proof. -/
def owner? (env : Environment) (names : NameIndex) (n : Name) : Option Name := do
  let m ← moduleOf? env n
  let ownRange := ranges? env n
  go m ownRange true n.getPrefix <|>
    go m ownRange false (privateToUserName n).getPrefix
where
  /-- Match an exact private parent before resolving a public alias of a private auxiliary. -/
  go (m : Name) (ownRange : Option DeclarationRanges) (raw : Bool) : Name → Option Name
    | .anonymous => none
    | p@(.str pre _) | p@(.num pre _) =>
      let parents := if env.contains p then #[p]
        else if raw then #[] else names[(m, p)]?.getD #[]
      let parent := match ownRange with
        | none => if parents.size == 1 then parents[0]? else none
        | some own => parents.find? fun parent =>
          moduleOf? env parent == some m &&
            (ranges? env parent).any (containsRange · own)
      parent <|> go m ownRange raw pre

/-- Whether an auxiliary belongs to a theorem's proof, through any enclosing auxiliaries.

Computational helpers of definitions remain roots even if their parents never call them. -/
partial def isProofSupport (env : Environment) (names : NameIndex) (n : Name) : Bool :=
  match owner? env names n with
  | some parent =>
    (env.find? parent).any (· matches .thmInfo _) || isProofSupport env names parent
  | none => false

/-- All constants used by a declaration, including implicit proof arguments and binder types. -/
def dependencies (c : ConstantInfo) : Array Name :=
  match c with
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
  | _ => c.type.getUsedConstants

/-- Elaborated references retain named lemmas even when simplification erases their proof terms. -/
abbrev SourceDependencies := Std.HashMap Name (Array Name)

/-- Read the same resolved names that Lean's language server uses for references.

The parent declaration identifies the consumer without guessing namespaces from source text. -/
def sourceDependencies (env : Environment) (root : System.FilePath) (scope : Name)
    (modules : Array Name) : IO SourceDependencies := do
  let mut out := {}
  for m in modules do
    let path := (← findOLean m).withExtension "ilean"
    let refs ← try Server.Ilean.load path catch _ =>
      throw <| IO.userError s!"{path}: cannot read reference metadata"
    unless refs.module == m && refs.version == 5 do
      throw <| IO.userError s!"{path}: unexpected reference metadata module or version"
    let components := m.components.drop scope.components.length
    let source := (components.foldl (fun p n => p / n.toString) root).addExtension "lean"
    let diagnostics ← unsupportedAttributes env source refs
    unless diagnostics.isEmpty do
      throw <| IO.userError (String.intercalate "\n" diagnostics.toList)
    for (ident, info) in refs.references do
      if let .const _ target := ident then
        for usage in info.usages do
          if let some parent := usage.parentDecl? then
            let parent := parent.toName
            out := out.insert parent ((out[parent]?.getD #[]).push target.toName)
  return out

/-- Theorems registered in the persistent global or scoped simplification sets.

Local attributes are absent after import and therefore do not retain a theorem by themselves. -/
def simpNames (env : Environment) : NameSet := Id.run do
  let state := Meta.simpExtension.ext.getState env
  let mut names : NameSet := {}
  for s in state.stateStack do
    for origin in s.state.lemmaNames.toList do
      if let .decl n _ _ := origin then names := names.insert n
  for (_, entries) in state.scopedEntries.map.toList do
    for entry in entries.toArray do
      if let .thm thm := entry then
        if let .decl n _ _ := thm.origin then names := names.insert n
  return names

/-- Registered instance names, including instances in an inactive namespace scope. -/
def instanceNames (env : Environment) : NameSet := Id.run do
  let state := Meta.instanceExtension.ext.getState env
  let mut names : NameSet := {}
  for s in state.stateStack do
    for (n, _) in s.state.instanceNames.toList do names := names.insert n
  for (_, entries) in state.scopedEntries.map.toList do
    for entry in entries.toArray do
      if let some n := entry.globalName? then names := names.insert n
  let defaults := Meta.defaultInstanceExtension.getState env
  for (_, entries) in defaults.defaultInstances.toList do
    for (n, _) in entries do names := names.insert n
  return names

/-- Reachability from retained declarations through every specification dependency. -/
partial def reachable (env : Environment) (source : SourceDependencies) (scope : Name)
    (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | n :: rest =>
    if seen.contains n || !(moduleOf? env n).any (isSpecModule scope) then
      reachable env source scope rest seen
    else
      let seen := seen.insert n
      let children := ((env.find? n).map dependencies |>.getD #[]) ++
        source[n]?.getD #[]
      reachable env source scope (children.toList ++ rest) seen

/-- One movable theorem, identified independently of generated private-name counters. -/
structure Finding where
  moduleName : Name
  decl : Name
  original : Name

/-- The baseline's stable identity for a declaration. -/
def Finding.key (f : Finding) : String × String := (f.moduleName.toString, f.decl.toString)

/-- Find theorems outside the dependencies of definitions, instances and `simp` rules. -/
def findings (env : Environment) (source : SourceDependencies) (scope : Name) :
    Array Finding := Id.run do
  let declarations := env.constants.toList.filter fun (n, _) =>
    (moduleOf? env n).any (isSpecModule scope)
  let mut names : NameIndex := {}
  for (n, _) in declarations do
    if let some m := moduleOf? env n then
      let key := (m, privateToUserName n)
      names := names.insert key ((names[key]?.getD #[]).push n)
  let simp := simpNames env
  let instances := instanceNames env
  let roots := declarations.filterMap fun (n, c) =>
    if simp.contains n || instances.contains n ||
        ((c matches .defnInfo _ | .opaqueInfo _ | .inductInfo _ | .ctorInfo _) &&
          !isProofSupport env names n) then some n
    else none
  let kept := reachable env source scope roots
  let out := declarations.filterMap fun (n, c) => do
    guard (c matches .thmInfo _)
    guard (!kept.contains n && !simp.contains n && (owner? env names n).isNone)
    let m ← moduleOf? env n
    return { moduleName := m, decl := privateToUserName n, original := n : Finding }
  return out.toArray.qsort fun a b =>
    a.moduleName.toString < b.moduleName.toString ||
      (a.moduleName == b.moduleName && a.decl.toString < b.decl.toString)

/-- Discover modules from source files, so an unbuilt module causes an import failure. -/
partial def modulesUnder (scope : Name) (dir : System.FilePath) (pre : Name) :
    IO (Array Name) := do
  let mut modules := #[]
  for entry in ← dir.readDir do
    let m := pre.str entry.fileName
    if ← entry.path.isDir then
      if isSpecModule scope m then
        modules := modules ++ (← modulesUnder scope entry.path m)
    else if entry.path.extension == some "lean" then
      let m := pre.str (entry.path.fileStem.getD "")
      if isSpecModule scope m then modules := modules.push m
  return modules

/-- Strict command-line options. -/
structure Options where
  root : System.FilePath := "EthLib"
  baseline : System.FilePath := "scripts/check_theorems_baseline.txt"
  print : Bool := false
  list : Bool := false
  parseBaseline : Option System.FilePath := none

/-- Read flags without accepting missing values or unknown arguments. -/
def parseArgs : List String → Options → Except String Options
  | [], options =>
    if options.parseBaseline.isSome &&
        (options.root != "EthLib" || options.baseline != "scripts/check_theorems_baseline.txt" ||
          options.print || options.list) then
      .error "choose either --parse-baseline or other options"
    else if options.print && options.list then .error "choose either --print or --list"
    else .ok options
  | "--root" :: value :: rest, options =>
    if value.startsWith "--" then .error "--root needs a directory"
    else parseArgs rest { options with root := value }
  | "--baseline" :: value :: rest, options =>
    if value.startsWith "--" then .error "--baseline needs a file"
    else parseArgs rest { options with baseline := value }
  | "--print" :: rest, options => parseArgs rest { options with print := true }
  | "--list" :: rest, options => parseArgs rest { options with list := true }
  | "--parse-baseline" :: value :: rest, options =>
    if value.startsWith "--" then .error "--parse-baseline needs a file"
    else parseArgs rest { options with parseBaseline := some value }
  | flag :: _, _ => .error s!"unknown or incomplete option {flag}"

/-- Parse one exact baseline entry, with comments and blank lines ignored. -/
def baselineEntry (line : String) : Except String (Option (String × String)) := do
  let line := (line.splitOn "#").headD ""
  let words := (line.splitToList Char.isWhitespace).filter (· != "")
  match words with
  | [] => return none
  | [m, n] => return some (m, n)
  | _ => throw "expected a module and a declaration name"

/-- Malformed and duplicate baseline entries are errors rather than ignored lines. -/
def readBaseline (path : System.FilePath) : IO (Array (String × String)) := do
  let lines ← try IO.FS.lines path catch _ =>
    throw <| IO.userError s!"{path}: cannot read baseline"
  let mut out := #[]
  for (line, index) in lines.zipIdx do
    let entry ← match baselineEntry line with
      | .ok entry => pure entry
      | .error message => throw <| IO.userError s!"{path}:{index + 1}: {message}"
    if let some entry := entry then
      if out.contains entry then
        throw <| IO.userError s!"{path}:{index + 1}: duplicate baseline entry"
      out := out.push entry
  return out

/-- Source path and declaration lines for the reviewable listing. -/
def location (env : Environment) (options : Options) (scope : Name) (f : Finding) :
    System.FilePath × Nat × Nat :=
  let components := f.moduleName.components.drop scope.components.length
  let relative := components.foldl (fun p n => p / n.toString) options.root
  let path := relative.addExtension "lean"
  let range := ranges? env f.original
  (path, range.map (·.range.pos.line) |>.getD 0,
    range.map (·.range.endPos.line) |>.getD 0)

/-- Load private bodies and attribute extensions before classifying theorems. -/
unsafe def run (args : List String) : IO UInt32 := do
  let options ← match parseArgs args {} with
    | .ok options => pure options
    | .error message =>
      IO.eprintln s!"check-theorems: {message}"
      return 2
  if let some path := options.parseBaseline then
    try
      for (m, n) in ← readBaseline path do IO.println s!"{m} {n}"
      return 0
    catch error =>
      IO.eprintln s!"check-theorems: {error}"
      return 2
  let some last := options.root.fileName
    | IO.eprintln "check-theorems: the root has no last part to name its modules"
      return 2
  unless ← options.root.isDir do
    IO.eprintln s!"check-theorems: the root {options.root} is not a directory"
    return 2
  let scope := Name.mkSimple last
  let mut modules ← modulesUnder scope options.root scope
  -- Include the library's root file, which the directory walk cannot visit.
  if ← (options.root.addExtension "lean").pathExists then modules := modules.push scope
  modules := modules.qsort (fun a b => a.toString < b.toString)
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m }) {} (trustLevel := 1024)
    (loadExts := true) (level := .private)
  let scanned := env.constants.toList.countP fun (n, c) =>
    (c matches .defnInfo _ | .opaqueInfo _) &&
      (moduleOf? env n).any (isSpecModule scope)
  if scanned == 0 then
    IO.eprintln "check-theorems: no definition of the specification was loaded"
    return 3
  let source ← try sourceDependencies env options.root scope modules catch error =>
    IO.eprintln s!"check-theorems: {error}"
    return 2
  let found := findings env source scope
  let keys := found.map Finding.key
  if (keys.toList.eraseDups).length != keys.size then
    IO.eprintln "check-theorems: findings have duplicate module and declaration names"
    return 3
  if options.print then
    for f in found do IO.println s!"{f.moduleName} {f.decl}"
    return 0
  if options.list then
    for f in found do
      let (path, first, last) := location env options scope f
      IO.println s!"{f.moduleName}\t{f.decl}\t{path}\t{first}\t{last}"
    return 0
  let baseline ← try readBaseline options.baseline catch error =>
    IO.eprintln s!"check-theorems: {error}"
    return 2
  let fresh := keys.filter (!baseline.contains ·)
  let stale := baseline.filter (!keys.contains ·)
  for (m, n) in fresh do IO.println s!"new: {m} {n}"
  for (m, n) in stale do IO.println s!"stale baseline entry, no longer found: {m} {n}"
  IO.println (s!"check-theorems: {modules.size} modules, {found.size} findings, " ++
    s!"{fresh.size} new, {stale.size} stale")
  return if fresh.isEmpty && stale.isEmpty then 0 else 1

end CheckTheorems

unsafe def main (args : List String) : IO UInt32 := CheckTheorems.run args
