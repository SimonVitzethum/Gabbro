/- Context for a refused compilation: every item the export gate refuses and every function
   whose elaboration to G fails, by name. The driver prints it after the compiler's own
   diagnostic; nothing here decides acceptance, so it is off the proof path. -/
module
public import Stage0.IRBild
@[expose] public section

namespace Gabbro.Stage0.Diagnose
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- What a statement is, in a few words, for a diagnosis. -/
def statementKind : SAnw → String
  | .bind _ x _ _ | .bindQ _ x _ _ | .bindElse x _ _ _ _ => "let " ++ x
  | .set .. => "assignment"
  | .call f _ | .callElse f _ _ _ | .callQ f _ => "call " ++ f
  | .cond .. => "if"
  | .cases .. => "match"
  | .each x .. => "traverse " ++ x
  | .retry .. => "retry"
  | .boundedLoop .. => "bounded loop"
  | .loop .. => "forever"
  | .locks .. => "locks"
  | .trim .. | .trimReq .. => "narrow"
  | .ret _ => "return"
  | .alloc _ x .. => "alloc " ++ x
  | _ => "statement"

/-- The first statement of a function body at which an elaboration error arises: the smallest number
    of leading statements whose elaboration already answers `reason`. Statements elaborate in order,
    so every longer prefix answers the same; the search halves the range. `none` when no prefix
    answers it (the error belongs to the closing `return`). -/
def firstFailing (attempt : List SAnw → Option String) (reason : String) (statements : List SAnw) :
    Option (Nat × SAnw) :=
  let fails := fun (k : Nat) => attempt (statements.take k) == some reason
  if !fails statements.length then none else
  let rec search (fuel lo hi : Nat) : Nat :=
    match fuel with
    | 0 => hi
    | fuel + 1 =>
      if hi ≤ lo + 1 then hi else
      let mid := (lo + hi) / 2
      if fails mid then search fuel lo mid else search fuel mid hi
  let k := search 64 0 statements.length
  (statements[k - 1]?).map fun s => (k, s)

/-- The line (from 1) of the joined source text that declares the function `name`: the first line
    holding `fn name` followed by `(`, `[` or a blank. -/
def fnLine (text name : String) : Option Nat :=
  let heads := ["(", "[", " "].map fun close => "fn " ++ name ++ close
  ((text.splitOn "\n").findIdx? fun line => heads.any fun head => (line.splitOn head).length > 1).map (· + 1)

/-- One diagnostic token step, using the lexer's own literal, comment and punctuation readers.
    The last component counts consumed newlines; strings and line comments contain none.
    This adapter never participates in compilation or acceptance. -/
def tokenStep : List Char → Option (Option Token × List Char × Nat)
  | '/' :: '/' :: rest => some (none, (nimmZeile rest).2, 0)
  | source@('/' :: '*' :: rest) => do
    let tail ← ueberBlock 1 rest
    let consumed := source.take (source.length - tail.length)
    some (none, tail, (consumed.filter (· == '\n')).length)
  | '"' :: rest => do
    let (value, tail) ← nimmText rest
    some (some (.text (String.ofList value)), tail, 0)
  | c :: rest =>
    if istLeer c then some (none, rest, if c == '\n' then 1 else 0)
    else if istZiffer c then
      (scanZahlKopf (c :: rest)).toOption.map fun (token, tail) => (some token, tail, 0)
    else if istAnfang c then
      let (word, tail) := nimmFolge rest
      let name := String.ofList (c :: word)
      some (some (if istSchluessel name then .wort name else .ident name), tail, 0)
    else
      match nimmZeichen (c :: rest) with
      | some (mark, tail) => some (some (.zeichen mark), tail, 0)
      | none =>
        if c == '\'' then
          (takeCharacter rest).map fun (value, tail) => (some (.num value), tail, 0)
        else none
  | [] => none

/-- Tokens with their original source lines. Agreement with `lex` is checked before using the
    positions, so a future lexical extension makes the adapter decline rather than mislocate a note. -/
def tokenLines (text : String) : Option (List (Token × Nat)) := do
  let expected ← (lex text).toOption
  let rec scanLines : Nat → List Char → Nat → Option (List (Token × Nat))
    | _, [], line => some [(.ende, line)]
    | 0, _ :: _, _ => none
    | fuel + 1, chars@(_ :: _), line => do
      let (token, tail, advance) ← tokenStep chars
      let rest ← scanLines fuel tail (line + advance)
      some (match token with | some token => (token, line) :: rest | none => rest)
  let tokens ← scanLines (text.toList.length + 1) text.toList 1
  if tokens.map (·.1) == expected then some tokens else none

/-- The body opener of a named source function. Parsing the signature skips contract/effects
    braces; prototypes and comments cannot be mistaken for a body. -/
def functionBody (name : String) : List (Token × Nat) → Option (List (Token × Nat))
  | [] => none
  | tokens@((token, _) :: tail) =>
    let found := match token with
      | .wort "fn" =>
        let raw := tokens.map (·.1)
        match parseFnSig (raw.length * 8 + 32) "impl" raw with
        | .ok (sig, rest) =>
          if sig.name == name then
            let body := tokens.drop (raw.length - rest.length)
            match body with
            | (.zeichen "{", _) :: _ => some body
            | _ => none
          else none
        | .error _ => none
      | _ => none
    match found with
    | some body => some body
    | none => functionBody name tail

/-- The N-th top-level statement, excluding a block's closing return just as `firstFailing` does.
    The source statement count and kind must agree with the note: expansion may insert statements,
    in which case no source location is claimed. Nested blocks are consumed by `parseStmt`. -/
def statementLine (text name : String) (index total : Nat) (kind : String) : Option Nat := do
  let tokens ← tokenLines text
  let body ← functionBody name tokens
  let raw := body.map (·.1)
  let fuel := raw.length * 8 + 32
  let (.block statements _, _) ← (parseBlock fuel raw).toOption | none
  if statements.length != total then none else do
    let statement ← statements[index - 1]?
    if statementKind statement != kind then none else do
      let rec locate : Nat → List (Token × Nat) → Option Nat
        | 0, _ => none
        | _ + 1, [] => none
        | k + 1, current@((_, line) :: _) =>
          if k == 0 then some line else do
            let raw := current.map (·.1)
            let (_, rest) ← (parseStmt fuel raw).toOption
            locate k (current.drop (raw.length - rest.length))
      locate index (body.drop 1)

/-- Read the statement index, count and kind already printed by `notesPlain`. -/
def statementPlace (text name note : String) : Option Nat := do
  let suffix ← (note.splitOn " (statement ")[1]?
  let [index, rest] := suffix.splitOn " of " | none
  let [total, kind] := rest.splitOn ": " | none
  statementLine text name (← index.toNat?) (← total.toNat?) ((kind.splitOn ")").headD "")

/-- A note that names its function (`function NAME: ...`), with the place of the declaration added. -/
def withLine (text : String) (place : Nat → String) (note : String) : String :=
  match (note.splitOn "function ").drop 1 with
  | rest :: _ =>
    match rest.splitOn ": " with
    | name :: _ :: _ =>
      let declared := match fnLine text name with
        | some line => note ++ " [declared at " ++ place line ++ "]"
        | none => note
      match statementPlace text name note with
      | some line => declared ++ " [statement at " ++ place line ++ "]"
      | none => declared
    | _ => note
  | [] => note

/-- The notes for one source text under the given options, without the places. -/
def notesPlain (text : String) (options : Profil.Options := {}) : List String := Id.run do
  let tokens ← match lex text with
    | .error _ => return []
    | .ok tokens => pure tokens
  let items ← match parseTopTief tokens with
    | .error _ => return []
    | .ok items => pure items
  let prepared ← match Profil.prepareItems options items with
    | .error _ => return []
    | .ok prepared => pure prepared
  let declarations := pre108 prepared.elaborierbar
  let members := uMembers declarations
  let runtimeMembers := Konst.ohneKonst members
  let refused := (runtimeMembers.filter (ExportMetadata.unitItemMetadata runtimeMembers)).map
    ExportMetadata.metadataReason
  let gate := refused.eraseDups.map fun reason => "export gate refuses: " ++ reason
  let derived ← match Frontend.elaborateConstantScopes members with
    | .error _ => return gate
    | .ok derived => pure derived
  let unit ← match (Frontend.elabWithScopes declarations derived.scope.values derived.scope.types
      derived.scope.functions (Frontend.tableWithEmpty derived.scope.values derived.scope.types)
      (widths := derived.scope.widths)).bind
        (Profil.selectUnit options) with
    | .error _ =>
      -- The same elaboration once more, asked for the place: the function an error arose in.
      let place := match expandU declarations with
        | .error _ =>
          -- The expansion refused: name the calls of functions the unit does not declare.
          match Gabbro.Grammatik.Parser.Modules.prepareDetailedRaw declarations with
          | .error _ => []
          | .ok result =>
            let known := Instantiation.functionNames result.items
            ((Instantiation.directReferences result.items).filter fun name => !known.contains name).eraseDups.map
              fun name => "call of an undeclared function: " ++ name
        | .ok (expanded, requirements) =>
          match Frontend.elabExpanded (expanded.map OldSource.normalizeItem) derived.scope.values
              derived.scope.types derived.scope.functions
              (Frontend.tableWithEmpty derived.scope.values derived.scope.types) requirements (ort := true) (widths := derived.scope.widths) with
          | .error reason =>
            -- The statement: the shortest prefix of the function's body that answers the same error.
            let run := fun (items : List SItemTief) =>
              match Frontend.elabExpanded items derived.scope.values derived.scope.types
                  derived.scope.functions
                  (Frontend.tableWithEmpty derived.scope.values derived.scope.types) requirements (ort := true) (widths := derived.scope.widths) with
              | .error e => some e
              | .ok _ => none
            let normal := expanded.map OldSource.normalizeItem
            let place := normal.findSome? fun
              | .fnT sig (.block statements _) =>
                if reason.startsWith ("function " ++ sig.name ++ ": ") then
                  (firstFailing (fun leading => run (normal.map fun
                      | .fnT other body => if other.name == sig.name then .fnT other (.block leading none) else .fnT other body
                      | item => item)) reason statements).map fun (k, s) =>
                    " (statement " ++ toString k ++ " of " ++ toString statements.length ++ ": " ++
                      statementKind s ++ ")"
                else none
              | _ => none
            ["elaboration: " ++ reason ++ place.getD ""]
          | .ok _ => []
      return gate ++ place
    | .ok unit => pure unit
  let functions := (List.finRange unit.fns.length).filterMap fun f =>
    match lowerFnAt unit f with
    | .ok _ => none
    | .error reason => some ("function " ++ (fnAt unit f).name ++ ": " ++ reason)
  return gate ++ functions

/-- The notes for one source text under the given options. `place` words a line of the joined text
    (the driver names the file and the line in it). -/
def notes (text : String) (options : Profil.Options := {})
    (place : Nat → String := fun line => "line " ++ toString line) : List String :=
  (notesPlain text options).map (withLine text place)

end Gabbro.Stage0.Diagnose
