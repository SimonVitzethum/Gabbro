import Bruecke.Quelle
import Grammatik.Parser.Lexer

/-!
# P6: the template a person starts from, WRITTEN BY LEAN from the source text

`vorlage name src` is what `gabbro prove --template --source <file.gab>` prints. Everything in the
STATEMENT is computed here from the text by the Lean front end (`uebersetzeAllg`); the Rust side
only quotes the file. The four stage outputs (tokens, items, the elaborated program `u`) are
untrusted HINTS: the kernel checks each against the pinned text (`lex_ok`, `parse_ok`, `elab_ok`,
`low_ok`), so a wrong hint fails to build instead of proving something else.

The source is pinned as `.toList` pieces (`zeilen`) and not as one literal: the kernel decodes a
`String` literal at a cost that explodes with its length (O13, `Parser/Lexer.lean`), and
`uebersetzeAllg_von_zeichen` lets the chain files avoid the decoder altogether. The output then
states -- with the computed functions `Pflichten`, `meetsU`, `zuBody`, never a printed statement --
one duty per function that a person proves, and closes with the generic theorem
`nutzer_aus_quelle`. A construct outside the fragment shows up as a NAMED refusal (the front end
says why, or `zuBody` is `none`, or a Bool check is false): the duty is then unprovable on
purpose, never weaker.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- A Lean string literal for `s` (escapes as `repr` writes them). -/
def literal (s : String) : String := (repr s).pretty 1000000

/-- The characters cut into pieces that end at a newline or after at most 60 characters. -/
def stueckeL : Nat → List Char → List (List Char)
  | 0, cs => if cs.isEmpty then [] else [cs]
  | fuel + 1, cs =>
    if cs.isEmpty then [] else
    let vor := cs.take 60
    let bis := match vor.findIdx? (· == '\n') with
      | some i => i + 1
      | none => vor.length
    cs.take bis :: stueckeL fuel (cs.drop bis)

/-- The pieces of a source text (their concatenation is the text). -/
def stuecke (src : String) : List String :=
  (stueckeL (src.length + 1) src.toList).map String.ofList

/-- The template for the source `src` of the unit `name` (a Lean identifier fragment). -/
def vorlage (name src : String) : String :=
  match lex src with
  | .error _ => "-- REFUSED by the Lean front end: the text does not lex (`lex`).\n"
  | .ok toks =>
  match parseTopTief toks with
  | .error e => "-- REFUSED by the Lean front end: parse: " ++ e ++ "\n"
  | .ok items =>
  match elabU (pre108 items) with
  | .error e => "-- REFUSED by the Lean front end: elab: " ++ e ++ "\n"
  | .ok u =>
  match lowerAllg u with
  | .error e => "-- REFUSED by the Lean front end: lower: " ++ e ++ "\n"
  | .ok _ =>
    let n := u.fns.length
    let wide (x : Std.Format) : String := x.pretty 1000000
    let zeilen := String.intercalate ",\n   " ((stuecke src).map fun s => literal s ++ ".toList")
    let kopf :=
      "import Bruecke.Quelle\n\n" ++
      "/-! Written by `gabbro prove --template --source`. The statements below are COMPUTED from the\n" ++
      "    pinned source by the Lean front end; nothing in them was printed by Rust. The stage\n" ++
      "    outputs `toks`, `items` and `u` are hints the kernel checks against the text. Replace\n" ++
      "    every `sorry` by a proof. -/\n\n" ++
      "namespace Gabbro.Bruecke.Vorlage." ++ name ++ "\n\n" ++
      "open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze\n" ++
      "open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2\n\n" ++
      "set_option maxRecDepth 100000\n\n" ++
      "-- SRC-BEGIN quelle\n" ++
      "/-- THE SOURCE, byte for byte, as pieces (the guardians read this block). -/\n" ++
      "def zeilen : List (List Char) :=\n  [" ++ zeilen ++ "]\n" ++
      "-- SRC-END quelle\n\n" ++
      "def quelle : String := String.ofList zeilen.flatten\n\n" ++
      "def toks : List Token := " ++ wide (repr toks) ++ "\n\n" ++
      "def items : List SItemTief := " ++ wide (repr items) ++ "\n\n" ++
      "def u : UProg := " ++ wide (repr u) ++ "\n\n" ++
      "set_option maxHeartbeats 4000000 in\n" ++
      "theorem lex_ok : lexL zeilen.flatten = .ok toks := by decide +kernel\n\n" ++
      "theorem parse_ok : parseTopTief toks = .ok items := rfl\n\n" ++
      "theorem elab_ok : elabU (pre108 items) = .ok u := rfl\n\n" ++
      "theorem low_ok : (lowerAllg u).toOption.isSome = true := by decide +kernel\n\n" ++
      "/-- PARSE FIDELITY: the pinned text is the program `u`. -/\n" ++
      "theorem uebersetzt : uebersetzeAllg quelle =\n" ++
      "    .ok ⟨u, ((lowerAllg u).toOption.get low_ok).1, ((lowerAllg u).toOption.get low_ok).2⟩ :=\n" ++
      "  uebersetzeAllg_von_zeichen lex_ok parse_ok elab_ok (except_ok_get low_ok)\n\n" ++
      "theorem verankert : uOf quelle = some u := uOf_eq uebersetzt\n\n"
    let bools :=
      (if nullB u then "theorem null : nullB u = true := by decide\n"
       else "-- REFUSED: a field range excludes 0, so there is no zero memory (`nullB u = false`).\n" ++
            "theorem null : nullB u = true := sorry\n") ++
      (if stimmigB u then "theorem stimmig : stimmigB u = true := by decide\n"
       else "-- REFUSED: a name condition fails (`stimmigB u = false`).\n" ++
            "theorem stimmig : stimmigB u = true := sorry\n") ++
      (if rangB u (rangAuto u) then "theorem rang : rangB u (rangAuto u) = true := by decide\n"
       else "-- REFUSED: the call graph has a cycle or no rank (`rangB u (rangAuto u) = false`).\n" ++
            "theorem rang : rangB u (rangAuto u) = true := sorry\n") ++ "\n"
    let pflicht := (List.range n).foldl (fun acc i =>
      let name_i := match u.fns[i]? with | some f => f.name | none => "?"
      let hinweis :=
        match u.fns[i]? with
        | some f => if (zuBody u f).isSome then "" else
            "-- REFUSED: the body of this function has a statement or expression outside the bridge's\n" ++
            "-- fragment (`zuBody` is `none`), so the duty below is false on purpose.\n"
        | none => ""
      acc ++ "/-- The duty of `" ++ name_i ++ "`: the computed statement. -/\n" ++ hinweis ++
        "theorem pflicht_" ++ toString i ++ " : ∃ body, zuBody u (fnAt u ⟨" ++ toString i ++ ", by decide⟩) = some body ∧\n" ++
        "    meetsU u (wfU u) (fnAt u ⟨" ++ toString i ++ ", by decide⟩) body := by\n  sorry\n\n") ""
    let fall := (List.range n).foldl (fun acc i =>
      acc ++ "  | ⟨" ++ toString i ++ ", _⟩ => pflicht_" ++ toString i ++ "\n") ""
    let schluss :=
      "theorem pflichten : Pflichten quelle :=\n" ++
      "  ⟨u, verankert, null, stimmig, rang, fun c => match c with\n" ++ fall ++
      "  | ⟨_ + " ++ toString n ++ ", h⟩ => absurd h\n" ++
      "      (by have hl : u.fns.length = " ++ toString n ++ " := by decide\n          omega)⟩\n\n" ++
      "/-- PREMISE (b) OF THE GOAL THEOREM for the unit the front end builds from `quelle`. -/\n" ++
      "theorem nutzer {u' : UProg} {P : Gabbro.Grammatik.Programm (declOf u')}\n" ++
      "    {fs : List (declOf u').Fn} (h : Gabbro.Grammatik.uebersetzeAllg quelle = .ok ⟨u', P, fs⟩) :\n" ++
      "    ∃ hn : nullB u' = true, Gabbro.Grammatik.Zielsatz.NutzerPflicht (einheitAllg u' P hn) :=\n" ++
      "  nutzer_aus_quelle pflichten h\n\n" ++
      "end Gabbro.Bruecke.Vorlage." ++ name ++ "\n"
    kopf ++ bools ++ pflicht ++ schluss

end Gabbro.Bruecke
