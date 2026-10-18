/-
  File:      Grammatik/Parser/Cover/Census.lean
  Subject:   Track P, phase 0: the measured coverage of the Lean parser over the corpus.

  `main` reads every `beispiele/*.gab`, lexes it, parses it in depth (`parseTopTief`), elaborates it
  (`elabU`) and, when the whole-file parse fails, splits the token stream into top-level items
  (module wrappers are opened) and reports the FIRST failing item of each file with its first
  tokens. One line per file:

    NAME | lex=ok/err | parse=ok/err:msg | elab=ok/err:msg | items=N bad=M | first=<tokens>

  Run (from `grammatik/`, after `lake build Grammatik.Parser.Cover.Census`):
    `lake env lean --run Grammatik/Parser/Cover/Census.lean ../beispiele`
  The numbers in `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` section 9a come from this run.
-/
import Grammatik.GabbroV.GvZensus
import Grammatik.Parser.Elab.UebersetzeAllg3
import Grammatik.Parser.Print.Stmt
import Grammatik.Parser.Print.Item

namespace Gabbro.Grammatik.Parser.Cover

open Gabbro.Grammatik.GabbroV.GvZensus
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- One item outcome: `ok` with the constructor tag, or `err` with the first tokens and the message. -/
inductive Res
  | ok : String → Res
  | err : String → String → Res

def firstWords (n : Nat) (toks : List Token) : String :=
  String.intercalate " " ((toks.take n).map zeigeTok)

/-- Skip to the next top-level item boundary after a failed item: at least one token, then up to a
    `;` or `}` at bracket depth 0. -/
partial def resync (toks : List Token) (d : Nat) (first : Bool) : List Token :=
  match toks with
  | [] => []
  | .ende :: _ => toks
  | t :: rest =>
    let d' := schrittTiefe t d
    match t with
    | .zeichen ";" => if d' == 0 then rest else resync rest d' false
    | .zeichen "}" => if d' == 0 then rest else resync rest d' false
    | _ => resync rest d' false

/-- The tokens of a module body and the rest after its closing brace. -/
def moduleSplit (toks : List Token) : Option (List Token × List Token) :=
  match toks.dropWhile (fun t => match t with | .zeichen "{" => false | _ => true) with
  | _ :: body =>
    match nimmBereichWorteListe body 1 [] with
    | some (inner, rest) => some (inner, rest)
    | none => none
  | [] => none
where
  nimmBereichWorteListe : List Token → Nat → List Token → Option (List Token × List Token)
    | [], _, _ => none
    | .zeichen "{" :: r, n, acc => nimmBereichWorteListe r (n + 1) (.zeichen "{" :: acc)
    | .zeichen "}" :: r, 1, acc => some (acc.reverse, r)
    | .zeichen "}" :: r, n + 2, acc => nimmBereichWorteListe r (n + 1) (.zeichen "}" :: acc)
    | t :: r, n, acc => nimmBereichWorteListe r n (t :: acc)

def isModuleHead : List Token → Bool
  | .wort "pub" :: .wort "module" :: _ => true
  | .wort "module" :: _ => true
  | _ => false

/-- Every top-level item, one at a time (module wrappers are opened), no short-circuit. -/
partial def scanAll (toks : List Token) : List Res :=
  match toks with
  | [] => []
  | .ende :: _ => []
  | _ =>
    if isModuleHead toks then
      match moduleSplit toks with
      | some (inner, rest) => scanAll inner ++ scanAll rest
      | none => [Res.err (firstWords 8 toks) "module without end"]
    else
      match parseItemTief (toks.length * 8 + 32) toks with
      | .ok (it, rest) => Res.ok (artItem it) :: scanAll rest
      | .error e => Res.err (firstWords 8 toks) e :: scanAll (resync toks 0 true)

def okTxt {α : Type} : Except String α → String
  | .ok _ => "ok"
  | .error e => "err:" ++ e

def tally (rs : List Res) : String :=
  let oks := rs.filterMap fun r => match r with | .ok k => some k | _ => none
  let errs := rs.filterMap fun r => match r with | .err h m => some (h ++ " ## " ++ m) | _ => none
  "ok=" ++ toString oks.length ++ " bad=" ++ toString errs.length ++
    " | kinds=" ++ String.intercalate "," oks ++
    " | blockers=" ++ String.intercalate " ;; " (errs.take 4)

/-- The function bodies of a unit, nested modules opened. -/
def koerperVon (ms : List SItemTief) : List SAnw :=
  (uMembers ms).filterMap fun it => match it with
    | .fnT _ b => some b
    | _ => none

/-- Round trip of every function body: print, read back, compare (`ok/total`). -/
def rundlaufZahl (items : List SItemTief) : String :=
  let bs := koerperVon items
  toString (bs.filter rundlaufBlock).length ++ "/" ++ toString bs.length

/-- Round trip of every leaf item (modules opened): `ok/printable/total`. -/
def rundlaufItemZahl (items : List SItemTief) : String :=
  let leaves := (uMembers items).filter fun it => match it with
    | .modT .. => false
    | _ => true
  let rs := leaves.filterMap rundlaufItem
  toString (rs.filter id).length ++ "/" ++ toString rs.length ++ "/" ++ toString leaves.length

def line (name src : String) : String :=
  match lex src with
  | .error e => name ++ " | lex=err:" ++ zeigeLexFehler e
  | .ok toks =>
    let whole := parseTopTief toks
    let el := match whole with
      | .ok items => okTxt (elabU items)
      | .error _ => "n/a"
    let lo := match whole with
      | .ok items => match elabU items with
        | .ok u => match lowerAllg u with
          | .ok _ => "ok"
          | .error e => "err:" ++ e
        | .error _ => "n/a"
      | .error _ => "n/a"
    let rt := match whole with
      | .ok items => rundlaufZahl items
      | .error _ => "n/a"
    let ri := match whole with
      | .ok items => rundlaufItemZahl items
      | .error _ => "n/a"
    name ++ " | lex=ok | parse=" ++ okTxt whole ++ " | elab=" ++ el ++ " | lower=" ++ lo ++ " | rt=" ++ rt ++ " | ri=" ++ ri ++ " | " ++ tally (scanAll toks)

def run (args : List String) : IO Unit := do
  let dir : System.FilePath := (args.headD "../beispiele")
  let entries ← dir.readDir
  let names := (entries.map (·.fileName)).filter (·.endsWith ".gab")
  let names := names.qsort (· < ·)
  for n in names do
    let src ← IO.FS.readFile (dir / n)
    IO.println (line n src)

end Gabbro.Grammatik.Parser.Cover

def main (args : List String) : IO Unit := Gabbro.Grammatik.Parser.Cover.run args
