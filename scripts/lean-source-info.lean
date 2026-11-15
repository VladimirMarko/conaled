import Lean

/-! Source preflight using the pinned compiler's header parser and lexer.
This executable does not elaborate project code or import project artifacts. -/
open Lean Parser

private def failAt (ctx : InputContext) (pos : String.Pos.Raw) (message : String) : IO α := do
  let location := ctx.fileMap.toPosition pos
  throw <| IO.userError s!"{ctx.fileName}:{location.line}:{location.column}: {message}"

private def checkLeadingCommands (env : Environment) (ctx : InputContext)
    (state : ModuleParserState) : IO Unit := do
  let mut state := state
  repeat
    let (stx, next, messages) := parseCommand ctx { env, options := {} } state {}
    if stx.isOfKind ``Lean.Parser.Command.import then
      failAt ctx state.pos "invalid 'import' command after module documentation; imports must precede commands"
    -- Only inspect the initial built-in documentation commands. Subsequent
    -- commands may need syntax extensions from not-yet-compiled local imports.
    if messages.hasErrors || !stx.isOfKind ``Lean.Parser.Command.moduleDoc then break
    state := next

private def checkPolicy (env : Environment) (ctx : InputContext) : IO Unit := do
  -- Unknown user-defined symbols need no grammar here. Register their Unicode
  -- characters as opaque tokens; Lean still lexes names, literals and comments.
  let mut tokens := getTokenTable env
  for c in ctx.inputString.toList do
    tokens := tokens.insert (String.singleton c) (String.singleton c)
  let pmctx : ParserModuleContext := { env, options := {} }
  let mut state := whitespace.run ctx pmctx tokens (mkParserState ctx.inputString)
  let forbidden := ["sorry", "admit", "axiom", "unsafe", "partial", "native_decide"]
  let mut previous : List String := []
  while !ctx.atEnd state.pos do
    let pos := state.pos
    -- The term parser also uses fieldIdxFn for projections such as .1.val.
    -- Unknown notation (for example Mathlib's ⁻¹') may contain a character
    -- that begins a literal in isolation. Treat a failed native token as an
    -- opaque character, never as skipped source. Compilation validates syntax.
    state := (orelseFn (atomicFn (tokenFn [])) (orelseFn fieldIdxFn
      (rawFn (satisfyFn fun _ => true) true))).run ctx pmctx tokens state
    if let some error := state.errorMsg then failAt ctx pos (toString error)
    let token := state.stxStack.back
    let word := match token with
      | .atom _ text => text
      | .ident _ _ name _ => name.toString
      | _ => ""
    if word == "/--" || word == "/-!" then
      state := (andthenFn (finishCommentBlock false 1) whitespace).run ctx pmctx tokens state
      if let some error := state.errorMsg then failAt ctx pos (toString error)
    else
      let parts := word.splitOn "."
      if let some banned := forbidden.find? (parts.contains ·) then
        failAt ctx pos s!"Forbidden source construct: {banned}"
      previous := (previous ++ [word]).drop (previous.length + 1 - 3)
      if word == "debug.skipKernelTC" || previous == ["debug", ".", "skipKernelTC"] then
        failAt ctx pos "Forbidden source construct: debug.skipKernelTC"
    state := state.popSyntax

def main (args : List String) : IO Unit := do
  let [manifest] := args | throw <| IO.userError "expected JSON source-path manifest"
  let paths ← IO.ofExcept <| fromJson? (α := Array String) (← IO.ofExcept <| Json.parse (← IO.FS.readFile manifest))
  let env ← mkEmptyEnvironment
  let mut result : Array Json := #[]
  for path in paths do
    let ctx := mkInputContext (← IO.FS.readFile path) path
    let (header, state, messages) ← parseHeader ctx
    if messages.hasErrors then
      for message in messages.toList do IO.eprintln (← message.toString)
      throw <| IO.userError s!"Invalid Lean module header: {path}"
    checkLeadingCommands env ctx state
    checkPolicy env ctx
    result := result.push <| toJson ((Elab.HeaderSyntax.imports header).map fun imp => imp.module.toString)
  IO.println (toJson result).compress
