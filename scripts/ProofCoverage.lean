import Lean
import CheckTheoremAttributes

/-!
# Proof coverage of the consensus rules

Grades each pair of a consensus rule and a beacon fork in three tiers.

- Executable: the rule exists at that fork, so every pair is in this tier.
- Touched: the statement of a theorem in a property module mentions the rule at that fork.
- Characterized: `coverage/characterizes.txt` claims that a theorem states the main contract of
  the rule, and that theorem holds at that fork.

The report reads statements only, never proofs.

- `lake exe proof-coverage` prints the counts at each fork, and lists the unread theorems.
- `lake exe proof-coverage --check` fails when a pair differs from the baseline.
- `lake exe proof-coverage --update` writes the baseline.

It exits with 1 on a difference or a wrong claim, 2 on a malformed argument or file, 3 when it
finds no rule or no fork type, and 4 on any other error.
-/

open Lean Meta

namespace ProofCoverage

/-- The fork type of EthLib. -/
def forkType : Name := `EthLib.Base.Fork

/-- The forks at which the beacon chain changes, one column of the report each. -/
def columns : List String :=
  ["phase0", "altair", "bellatrix", "shapella", "dencun", "pectra", "fusaka", "glamsterdam",
    "hegota"]

/-- What the report reads, and the files it reads or writes.

The source directory and the scope replace the defaults for the fixtures of
`scripts/test_proof_coverage.sh`. -/
structure Config where
  /-- The directory that holds the source tree of the scope. -/
  src : System.FilePath := "."
  /-- The modules under this name hold the rules and the property theorems. -/
  scope : Name := `EthLib.Consensus
  /-- Each line names a rule, then a theorem that states its main contract. -/
  claims : System.FilePath := "coverage/characterizes.txt"
  /-- Each line names a tier, a fork and a rule. -/
  baseline : System.FilePath := "scripts/proof_coverage_baseline.txt"
  check : Bool := false
  update : Bool := false

/-- Read the flags, and reject an unknown or incomplete one. -/
def parse : Config → List String → Except String Config
  | c, [] => if c.check && c.update then .error "choose either --check or --update" else .ok c
  | c, "--check" :: rest => parse { c with check := true } rest
  | c, "--update" :: rest => parse { c with update := true } rest
  | c, "--src" :: v :: rest => parse { c with src := v } rest
  | c, "--scope" :: v :: rest => parse { c with scope := v.toName } rest
  | c, "--claims" :: v :: rest => parse { c with claims := v } rest
  | c, "--baseline" :: v :: rest => parse { c with baseline := v } rest
  | _, a :: _ => .error s!"unknown or incomplete argument {a}"

/-- The usage line. -/
def usage : String :=
  "usage: lake exe proof-coverage [--check | --update] [--src DIR] [--scope NAME] " ++
    "[--claims FILE] [--baseline FILE]"

/-- A module of property theorems sits under a `Proofs` directory. -/
def isPropertyModule (scope m : Name) : Bool :=
  scope.isPrefixOf m && m.components.contains `Proofs && !m.components.contains `Exports

/-- Every module under the scope, read from the source files, so an unbuilt one fails to import. -/
def modules (c : Config) : IO (Array Name) := do
  let dir := c.scope.components.foldl (fun p n => p / n.toString) c.src
  let mut out := if ← (dir.addExtension "lean").pathExists then #[c.scope] else #[]
  for path in ← dir.walkDir do
    if path.extension == some "lean" then
      let rel := (path.withExtension "").components.drop c.src.components.length
      out := out.push (rel.foldl (fun n p => n.str p) .anonymous)
  return out.qsort (·.toString < ·.toString)

/-- A declaration that a person wrote has a source range, unlike those the elaborator adds. -/
def isWritten (env : Environment) (n : Name) : Bool :=
  !isPrivateName n && (CheckTheorems.ranges? env n).isSome

/-- A rule is a definition of a specification module that a person wrote.

An instance or a field of a structure is no rule. -/
def isRule (env : Environment) (scope n : Name) : Bool :=
  (env.find? n).any (· matches .defnInfo _) && isWritten env n &&
    (CheckTheorems.moduleOf? env n).any (CheckTheorems.isSpecModule scope) &&
    !isInstanceCore env n && !env.isProjectionFn n

/-- A theorem of a property module that a person wrote.

The report imports statements without proofs, so each theorem reads as an axiom.

`lake exe check-decls` rejects every real axiom. -/
def isPropertyTheorem (env : Environment) (scope n : Name) : Bool :=
  (env.find? n).any (· matches .thmInfo _ | .axiomInfo _) && isWritten env n &&
    (CheckTheorems.moduleOf? env n).any (isPropertyModule scope)

/-- The position of a fork in its type, if `e` is one of its constructors. -/
def forkIndex? (env : Environment) (e : Expr) : Option Nat := do
  let .const n _ := e | none
  let .ctorInfo info ← env.find? n | none
  guard (info.induct == forkType)
  return info.cidx

/-- A bound on a fork variable, `.x ≤ v`, `.x < v`, `v ≤ .x` or `v < .x`, as the forks it allows. -/
def bound? (env : Environment) (t : Expr) : Option (FVarId × (Nat → Bool)) :=
  match t.getAppFnArgs with
  | (``LE.le, #[ty, _, a, b]) => if ty.isConstOf forkType then le a b else none
  | (``LT.lt, #[ty, _, a, b]) => if ty.isConstOf forkType then lt a b else none
  | (``GE.ge, #[ty, _, a, b]) => if ty.isConstOf forkType then le b a else none
  | (``GT.gt, #[ty, _, a, b]) => if ty.isConstOf forkType then lt b a else none
  | _ => none
where
  le (a b : Expr) : Option (FVarId × (Nat → Bool)) :=
    match a, b with
    | .fvar v, _ => (forkIndex? env b).map fun i => (v, (· ≤ i))
    | _, .fvar v => (forkIndex? env a).map fun i => (v, (i ≤ ·))
    | _, _ => none
  lt (a b : Expr) : Option (FVarId × (Nat → Bool)) :=
    match a, b with
    | .fvar v, _ => (forkIndex? env b).map fun i => (v, (· < i))
    | _, .fvar v => (forkIndex? env a).map fun i => (v, (i < ·))
    | _, _ => none

/-- The beacon forks at which a statement holds, as positions in the fork type.

A statement with fork variables holds where some variable may be, as its bounds allow.

A statement with no fork variable holds at the forks it names, or at every fork if it names none.

A hypothesis on the forks alone that is no such bound makes the window unreadable, `none`. -/
def window (env : Environment) (cols : List Nat) (type : Expr) : MetaM (Option (List Nat)) :=
  forallTelescope type fun xs _ => do
    let mut vars : Array FVarId := #[]
    for x in xs do
      if (← inferType x).isConstOf forkType then vars := vars.push x.fvarId!
    if vars.isEmpty then
      let named := type.getUsedConstants.filterMap (forkIndex? env <| mkConst ·)
      return some (if named.isEmpty then cols else cols.filter named.contains)
    let mut bounds := #[]
    for x in xs do
      let t ← inferType x
      -- A hypothesis on the forks alone mentions a fork variable and no other local.
      unless t.hasAnyFVar vars.contains && !t.hasAnyFVar (!vars.contains ·) && (← isProp t) do
        continue
      let some b := bound? env t | return none
      bounds := bounds.push b
    return some <| cols.filter fun c =>
      vars.any fun v => bounds.all fun (u, allows) => u != v || allows c

/-- The three tiers above executable, by name. -/
inductive Tier where
  | touched
  | characterized
  deriving BEq, Hashable, Ord

/-- The name of a tier in the baseline. -/
def Tier.name : Tier → String
  | .touched => "touched"
  | .characterized => "characterized"

/-- One line of the baseline: a tier, a fork and a rule. -/
abbrev Entry := Tier × String × Name

/-- The text of a baseline line. -/
def Entry.text (e : Entry) : String := s!"{e.1.name} {e.2.1} {e.2.2}"

/-- Lines of a file without their comments and blank lines, with their line numbers. -/
def contentLines (path : System.FilePath) : IO (Array (Nat × List String)) := do
  let lines ← IO.FS.lines path
  return lines.zipIdx.filterMap fun (line, i) =>
    let words := ((line.splitOn "#").headD "").splitToList Char.isWhitespace |>.filter (· != "")
    if words.isEmpty then none else some (i + 1, words)

/-- The claims, each a rule and a theorem; a malformed or repeated line is an error. -/
def readClaims (path : System.FilePath) : IO (Array (Name × Name)) := do
  let mut out := #[]
  for (i, words) in ← contentLines path do
    let [r, t] := words | throw <| IO.userError s!"{path}:{i}: expected a rule and a theorem"
    let claim := (r.toName, t.toName)
    if out.contains claim then throw <| IO.userError s!"{path}:{i}: duplicate claim"
    out := out.push claim
  return out

/-- The baseline lines; a malformed one is an error. -/
def readBaseline (path : System.FilePath) : IO (Array Entry) := do
  let mut out := #[]
  for (i, words) in ← contentLines path do
    let entry ← match words with
      | ["touched", f, r] => pure (Tier.touched, f, r.toName)
      | ["characterized", f, r] => pure (Tier.characterized, f, r.toName)
      | _ => throw <| IO.userError s!"{path}:{i}: expected a tier, a fork and a rule"
    unless columns.contains entry.2.1 do
      throw <| IO.userError s!"{path}:{i}: {entry.2.1} is not a beacon fork"
    out := out.push entry
  return out

/-- The header of the baseline that `--update` writes. -/
def header : String :=
  "# Written by `lake exe proof-coverage --update`; CONTRIBUTING.md says when to update it.\n" ++
  "# Each line is a tier, a beacon fork and a consensus rule, for each pair above executable.\n"

/-- Runs the report. -/
unsafe def run (args : List String) : IO UInt32 := do
  let c ← match parse {} args with
    | .ok c => pure c
    | .error e =>
      IO.eprintln s!"proof-coverage: {e}\n{usage}"
      return 2
  let claims ← try readClaims c.claims catch e =>
    IO.eprintln s!"proof-coverage: {e}"
    return 2
  let mods ← modules c
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (mods.map fun m => { module := m }) {} (loadExts := true)
    (level := .server)
  let some (.inductInfo fork) := env.find? forkType | do
    IO.eprintln s!"proof-coverage: no inductive type {forkType} in the loaded modules"
    return 3
  -- Each column is the position of its fork in the fork type.
  let cols := columns.filterMap fun f => fork.ctors.idxOf? (forkType.str f)
  unless cols.length == columns.length do
    IO.eprintln s!"proof-coverage: {forkType} lacks a beacon fork of {columns}"
    return 3
  let colName (i : Nat) : String := (fork.ctors[i]?.map (·.getString!)).getD "?"
  let decls := env.constants.map₁.toList
  let rules := decls.filter (isRule env c.scope ·.1)
  if rules.isEmpty then
    IO.eprintln s!"proof-coverage: no rule under {c.scope} in the loaded modules"
    return 3
  let theorems := decls.filter (isPropertyTheorem env c.scope ·.1)
  let ctx : Core.Context := { fileName := "<proof-coverage>", fileMap := default }
  let act : MetaM _ := do
    let mut ruleWindows : NameMap (List Nat) := {}
    let mut unread : Array Name := #[]
    for (n, info) in rules do
      match ← window env cols info.type with
      | some w => ruleWindows := ruleWindows.insert n w
      | none => unread := unread.push n
    let mut thmWindows : NameMap (List Nat) := {}
    for (n, info) in theorems do
      match ← window env cols info.type with
      | some w => thmWindows := thmWindows.insert n w
      | none => unread := unread.push n
    return (ruleWindows, thmWindows, unread)
  let ((ruleWindows, thmWindows, unread), _) ← act.run' {} |>.toIO ctx { env }
  -- A pair is touched when some theorem mentions the rule and holds at the fork.
  let mut tiers : Std.HashMap (Name × Nat) Tier := {}
  for (n, info) in theorems do
    let some w := thmWindows.find? n | continue
    for r in info.type.getUsedConstants do
      let some rw := ruleWindows.find? r | continue
      for col in w.filter rw.contains do tiers := tiers.insert (r, col) .touched
  -- A claim must name a rule, a property theorem, and a statement that mentions the rule.
  let mut wrong := 0
  for (r, t) in claims do
    let problem :=
      if !ruleWindows.contains r then some s!"{r} is not a rule of {c.scope}"
      else if !thmWindows.contains t then
        some s!"{t} is not a theorem of a property module with a readable fork window"
      else if !((env.find? t).any (·.type.getUsedConstants.contains r)) then
        some s!"the statement of {t} does not mention {r}"
      else none
    if let some p := problem then
      IO.eprintln s!"proof-coverage: wrong claim: {p}"
      wrong := wrong + 1
      continue
    for col in (thmWindows.getD t []).filter (ruleWindows.getD r []).contains do
      tiers := tiers.insert (r, col) .characterized
  -- The lines are sorted by rule, then by fork.
  let ruleNames := (ruleWindows.toList.map (·.1)).toArray.qsort (·.toString < ·.toString)
  let entries : Array Entry := ruleNames.flatMap fun r =>
    (cols.filterMap fun col => (tiers[(r, col)]?).map fun t => (t, colName col, r)).toArray
  IO.println s!"proof-coverage: {ruleNames.size} rules, {thmWindows.size} property theorems"
  for col in cols do
    let rulesAt := ruleNames.filter fun r => (ruleWindows.getD r []).contains col
    let reached (t : Tier) := entries.filter fun e => e.2.1 == colName col && compare e.1 t != .lt
    IO.println s!"{colName col}: {rulesAt.size} rules, {(reached .touched).size} touched, \
      {(reached .characterized).size} characterized"
  if c.update then
    IO.FS.writeFile c.baseline (header ++ String.join (entries.toList.map (·.text ++ "\n")))
    IO.println s!"proof-coverage: wrote {entries.size} lines to {c.baseline}"
  else if c.check then
    let old ← try readBaseline c.baseline catch e =>
      IO.eprintln s!"proof-coverage: {e}"
      return 2
    let now : Std.HashSet Entry := .ofArray entries
    let before : Std.HashSet Entry := .ofArray old
    let gone := old.filter (!now.contains ·)
    let added := entries.filter (!before.contains ·)
    for e in gone do IO.println s!"- {e.text}"
    for e in added do IO.println s!"+ {e.text}"
    unless gone.isEmpty && added.isEmpty do
      IO.eprintln s!"proof-coverage: the coverage differs from {c.baseline}"
      IO.eprintln "If the change is intended, run `lake exe proof-coverage --update`."
      return 1
  else
    for n in unread.qsort (·.toString < ·.toString) do
      IO.println s!"unread fork hypotheses, at no fork: {n}"
  return if wrong == 0 then 0 else 1

end ProofCoverage

/-- Runs the report, and exits with 4 on an error, such as a module that is not built. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    ProofCoverage.run args
  catch e =>
    IO.eprintln s!"proof-coverage: {e}"
    return 4
