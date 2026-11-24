module
public meta import Lean
public meta import Core.Waechter.Package

open Lean Parser

namespace Gabbro.Core.Waechter

private meta structure TokenAt where
  text : String
  pos : String.Pos.Raw
  deriving Inhabited

private meta def tokens (env : Environment) (input : InputContext) : Array TokenAt := Id.run do
  let context : ParserModuleContext := { env, options := {} }
  let table := getTokenTable env
  let start := mkParserState input.inputString
  let mut pos := start.pos
  let mut out := #[]
  while !input.atEnd pos do
    let space := whitespace.run input context table { start with pos }
    pos := space.pos
    if input.atEnd pos then break
    let next := input.next pos
    if input.get pos == '/' && input.get next == '-' then
      -- The whitespace parser leaves documentation comments for the command parser.
      let comment := finishCommentBlock false 1
      pos := (comment.run input context table { start with pos := input.next next }).pos
    else
      let state := (tokenFn []).run input context table { start with pos }
      let stop := if state.hasError then next
        else state.stxStack.back.getTailPos?.getD next
      out := out.push ⟨input.extract pos stop, pos⟩
      pos := stop
  return out

private meta def positiveAesopBound (ts : Array TokenAt) (first stop : Nat) (field : String) : Bool :=
  (List.range' first (stop - first)).any fun i =>
    ts[i]?.any (·.text == field) &&
    ts[i + 1]?.any (·.text == ":=") &&
    (ts[i + 2]?.bind (·.text.toNat?)).any (· > 0)

private meta def boundedAesop (ts : Array TokenAt) (i : Nat) : Bool := Id.run do
  let textAt (j : Nat) := (ts[j]?.map (·.text)).getD ""
  unless textAt (i+1) == "(" && textAt (i+2) == "config" && textAt (i+3) == ":=" && textAt (i+4) == "{" do
    return false
  let mut stop := i+5
  while stop < ts.size && textAt stop != "}" && textAt stop != "{" do
    stop := stop + 1
  return textAt stop == "}" && textAt (stop+1) == ")" &&
    positiveAesopBound ts (i+5) stop "maxRuleApplications" &&
    positiveAesopBound ts (i+5) stop "maxNormIterations"

private meta def declarationCommands : Array String :=
  #["syntax", "notation", "infix", "infixl", "infixr", "prefix", "postfix",
    "macro", "macro_rules", "elab", "elab_rules", "run_cmd", "run_elab",
    "run_meta", "initialize", "builtin_initialize", "declare_syntax_cat"]

private meta def commandModifiers : Array String :=
  #["scoped", "local", "private", "public"]

private meta def declarationCommand (text : String) : Option String :=
  declarationCommands.find? (fun w => text == w || text.startsWith (w ++ ":"))

private meta def lineLead (input : InputContext) (ts : Array TokenAt) (i : Nat) : Array String := Id.run do
  let line := (input.fileMap.toPosition ts[i]!.pos).line
  let mut out := #[]
  let mut j := i
  while j > 0 do
    let prev := ts[j-1]!
    if (input.fileMap.toPosition prev.pos).line != line then break
    out := out.push prev.text
    j := j - 1
  return out.reverse

private meta def validCommandLead (lead : Array String) : Bool := Id.run do
  let mut depth : Nat := 0
  for t in lead do
    if commandModifiers.contains t then continue
    if t == "@" && depth == 0 then continue
    if t == "[" then depth := depth + 1
    else if t == "]" then
      if depth == 0 then return false
      depth := depth - 1
    else if depth > 0 then continue
    else return false
  return depth == 0

private meta def localTacticMacro (input : InputContext) (ts : Array TokenAt) (i : Nat)
    (lead : Array String) : Bool := Id.run do
  if ts[i]!.text != "macro" then return false
  unless lead.contains "local" do return false
  unless (ts[i+1]?.map (fun t => t.text.startsWith "\"")).getD false do return false
  let line := (input.fileMap.toPosition ts[i]!.pos).line
  let mut j := i + 2
  let mut colon := false
  let mut tactic := false
  while j < ts.size do
    if (input.fileMap.toPosition ts[j]!.pos).line != line then break
    let txt := ts[j]!.text
    if txt == ":" then colon := true
    else if colon && txt == "tactic" then tactic := true
    else if tactic && txt == "=>" then return true
    j := j + 1
  return false


public meta structure SourceAudit where
  errors : Array String
  wildcardArms : Array Position

/-- Scans Lean tokens, skipping comments and treating strings and quoted identifiers as single tokens.
    It rejects forbidden words, the witness filename convention, and options on the decision tactic.
    Decision.lean checks the goals of retained decision proofs. An anonymous `example` followed by
    an inline or indented decision tactic is refused because its proof is discarded. The speed rule requires `only` after
    `simp`, even in nonterminal positions, except for
    `simp at h` with an explicit hypothesis name. An Aesop call requires an initial literal config with
    positive rule-application and normalization bounds. Outside `Core.Waechter`, declaration commands
    (`syntax`, `notation`, `macro`, `elab`, `initialize`, and the rest) are refused at command position after
    optional modifiers and attributes; a `local macro "…" : tactic` proof tactic is exempt. This is a lexical
    policy, so it does not reconstruct macro expansions or inspect code inside string antiquotations. -/
public meta def auditSource (env : Environment) (source : Source) : SourceAudit := Id.run do
  let input := mkInputContext source.input source.path.toString
  let ts := tokens env input
  let mut errors := #[]
  let mut wildcardArms := #[]
  let mut examplePosition : Option Position := none
  let excluded := ["sorry", "admit", "native_decide", "axiom", "unsafe", "partial"]
  let budgets := ["maxHeartbeats", "synthInstance.maxHeartbeats", "maxRecDepth"]
  let witnessName := source.moduleName.getString!.toLower
  if witnessName.startsWith "witness" || witnessName.endsWith "witness" ||
      witnessName.startsWith "zeuge" || witnessName.endsWith "zeuge" then
    errors := errors.push s!"{source.path}: forbidden witness module name"
  let inWaechter := (`Core.Waechter).isPrefixOf source.moduleName
  for i in [0:ts.size] do
    let t := ts[i]!
    let after := (ts[i+1]?.map (·.text)).getD ""
    let afterNext := (ts[i+2]?.map (·.text)).getD ""
    if let some start := examplePosition then
      let pos := input.fileMap.toPosition t.pos
      if pos.line > start.line && pos.column ≤ start.column then
        examplePosition := none
    if t.text == "example" then
      examplePosition := some (input.fileMap.toPosition t.pos)
    let message :=
      if excluded.contains t.text then some s!"forbidden Lean token {t.text}"
      else if t.text == "set_option" && budgets.contains after then
        some s!"setting {after} overrides the elaboration budget"
      else if t.text == "decide" && after == "+" && afterNext == "kernel" then
        some "forbidden kernel decision tactic"
      else if t.text == "decide" &&
          (after == "+" || after == "-" || (after == "(" && afterNext == "config")) then
        some "decision tactic options are forbidden by the fast-build policy"
      else if t.text == "decide" && examplePosition.isSome then
        some "decision proof in an anonymous example is unavailable to the fast-build guard"
      else if t.text == "simp" && after != "only" &&
          !(after == "at" && afterNext.toList.head?.any (fun c => c.isAlpha)) then
        some "simp requires only or an explicit hypothesis location"
      else if ["aesop", "aesop?"].contains t.text && !boundedAesop ts i then
        some "aesop requires explicit positive maxRuleApplications and maxNormIterations"
      else none
    if let some message := message then
      let pos := input.fileMap.toPosition t.pos
      errors := errors.push s!"{source.path}:{pos.line}:{pos.column}: {message}"
    if !inWaechter then
      if let some word := declarationCommand t.text then
        let lead := lineLead input ts i
        if validCommandLead lead && !(localTacticMacro input ts i lead) then
          let pos := input.fileMap.toPosition t.pos
          errors := errors.push s!"{source.path}:{pos.line}: forbidden declaration command {word} in a Core source file"
    if t.text == "_" && (after == "=>" || after == "↦") then
      wildcardArms := wildcardArms.push (input.fileMap.toPosition t.pos)
  return ⟨errors, wildcardArms⟩

end Gabbro.Core.Waechter
