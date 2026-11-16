import Lean
import Lean.Server.References

/-!
# Persistent attributes on specification theorems

Moving an attributed theorem can change compilation, elaboration or tactic behaviour.

The source guard accepts `simp` and stops on other explicit persistent theorem attributes.

Prefix parsers identify the attributes, and elaborator references identify their declarations.

Attributes generated only by custom command macros are outside this source inspection.
-/

open Lean

namespace CheckTheorems

/-- The original declaration's source range, without falling back to a parent's range. -/
def ranges? (env : Environment) (n : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .exported) env n <|>
    declRangeExt.find? (level := .server) env n

/-- An attribute application which survives the end of its section. -/
def persistentAttributeName? (stx : Syntax) : Option Name := do
  guard (stx.getKind == ``Parser.Term.attrInstance)
  guard (stx[0][0][0].getKind != ``Parser.Term.local)
  let attr := stx[1]
  if attr.getKind == ``Parser.Attr.simple then
    return attr[0].getId.eraseMacroScopes
  else
    match attr.getKind with
    | .str _ name => return Name.mkSimple name
    | _ => none

/-- Whether the reference location starts inside a source syntax node. -/
def referenceInSyntax (text : FileMap) (stx : Syntax) (loc : Lsp.RefInfo.Location) : Bool :=
  match stx.getPos?, stx.getTailPos? with
  | some first, some last =>
    let pos := text.lspPosToUtf8Pos loc.range.start
    first ≤ pos && pos < last
  | _, _ => false

/-- Resolve declaration binders or attribute targets through elaborator reference locations. -/
def attributedTheorems (env : Environment) (text : FileMap) (refs : Server.Ilean)
    (stx : Syntax) (binder : Bool) : Array Name := Id.run do
  let mut names := #[]
  for (ident, info) in refs.references do
    if let .const _ name := ident then
      let n := name.toName
      if (env.find? n).any (· matches .thmInfo _) then
        let locations := if binder then info.definition?.toArray
          else info.usages.filter (·.parentDecl?.isNone)
        if locations.any (referenceInSyntax text stx) then names := names.push n
  return names

/-- Reject an unsupported attribute before the check can recommend moving its theorem. -/
def attributeDiagnostics (source : System.FilePath) (text : FileMap)
    (attrs : Array Syntax) (names : Array Name) : Array (Nat × String) := Id.run do
  let mut out := #[]
  for attr in attrs do
    if let some name := persistentAttributeName? attr then
      if name != `simp then
        let line := (text.toPosition (attr.getPos?.getD 0)).line
        for n in names do
          out := out.push ((attr.getPos?.getD 0).byteIdx,
            s!"{source}:{line}: unsupported persistent attribute " ++
              s!"[{name}] on theorem {privateToUserName n}")
  return out

/-- Parse theorem modifiers at their recorded source positions, without reading proof bodies.

Local notation can disappear on import, so a compiled environment cannot parse every body again. -/
def declarationAttributeDiagnostics (env : Environment) (source : System.FilePath)
    (input : Parser.InputContext) (refs : Server.Ilean) : IO (Array (Nat × String)) := do
  let mut out := #[]
  for (ident, info) in refs.references do
    if let .const moduleName name := ident then
      let n := name.toName
      if moduleName.toName == refs.module && info.definition?.isSome &&
          (env.find? n).any (· matches .thmInfo _) then
        let some range := ranges? env n
          | throw <| IO.userError s!"{source}: cannot locate theorem {privateToUserName n}"
        let pos := input.fileMap.ofPosition range.range.pos
        let state := (Parser.mkParserState input.inputString).setPos pos
        let parsed := (Parser.Command.declModifiers false).fn.run input { env, options := {} }
          (Parser.getTokenTable env) state
        if parsed.hasError then
          throw <| IO.userError s!"{source}:{range.range.pos.line}: cannot parse modifiers"
        let attrs := parsed.stxStack.back[1][0][1].getSepArgs
        out := out ++ attributeDiagnostics source input.fileMap attrs #[n]
  return out

/-- Source spans that hold documentation rather than persistent commands.

Verso examples can record resolved references, but discard the environments they change. -/
def documentationRanges (env : Environment) (text : FileMap) (refs : Server.Ilean) :
    Array (String.Pos.Raw × String.Pos.Raw) := Id.run do
  let moduleDocs := ((getModuleDoc? env refs.module).getD #[]).map (·.declarationRange)
  let versoDocs := ((getVersoModuleDoc? env refs.module).getD #[]).map (·.declarationRange)
  let mut out := (moduleDocs ++ versoDocs).map fun range =>
    (text.ofPosition range.pos, text.ofPosition range.endPos)
  for (ident, info) in refs.references do
    if let .const moduleName name := ident then
      if moduleName.toName == refs.module && info.definition?.isSome then
        if let some range := ranges? env name.toName then
          out := out.push (text.ofPosition range.range.pos,
            text.ofPosition range.selectionRange.pos)
  return out

/-- Validate command prefixes only where elaboration recorded a top-level theorem target.

Documentation spans are excluded even when their examples record resolved references.

Independent candidates avoid reparsing local notation or nested interpolated strings. -/
def commandAttributeDiagnostics (env : Environment) (source : System.FilePath)
    (input : Parser.InputContext) (refs : Server.Ilean) : Array (Nat × String) := Id.run do
  let context := { env, options := {} : Parser.ParserModuleContext }
  let tokens := Parser.getTokenTable env
  let docs := documentationRanges env input.fileMap refs
  let mut offset := 0
  let mut out := #[]
  for part in (input.inputString.splitOn "attribute").dropLast do
    offset := offset + part.utf8ByteSize
    let pos : String.Pos.Raw := ⟨offset⟩
    let previous := (String.Pos.Raw.prev input.inputString pos).get input.inputString
    -- A dotted identifier or a name literal does not begin an attribute command.
    let insideDoc := docs.any fun (first, last) => first ≤ pos && pos < last
    unless insideDoc ||
        (offset > 0 && (isIdRest previous || previous == '.' || previous == '`')) do
      let state := (Parser.mkParserState input.inputString).setPos pos
      let parsed := Parser.Command.attribute.fn.run input context tokens state
      -- A textual occurrence is not a command unless both syntax and resolved targets agree.
      if !parsed.hasError then
        let command := parsed.stxStack.back
        let names := attributedTheorems env input.fileMap refs command[4] false
        out := out ++ attributeDiagnostics source input.fileMap command[2].getSepArgs names
    offset := offset + "attribute".utf8ByteSize
  return out

/-- Inspect explicit persistent theorem attributes on declarations and `attribute` commands.

The reference file resolves namespaces, private names and aliases without a second name resolver.

Local attributes and erasures do not register a persistent rule for importers. -/
def unsupportedAttributes (env : Environment) (source : System.FilePath)
    (refs : Server.Ilean) : IO (Array String) := do
  let contents ← IO.FS.readFile source
  let input := Parser.mkInputContext contents source.toString
  let declarations ← declarationAttributeDiagnostics env source input refs
  let commands := commandAttributeDiagnostics env source input refs
  let diagnostics := (declarations ++ commands).qsort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  return diagnostics.map (·.2)

end CheckTheorems
