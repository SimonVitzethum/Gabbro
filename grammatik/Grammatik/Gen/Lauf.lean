/-
  File:      Grammatik/Gen/Lauf.lean
  Subject:   Generator, part 2: the model as the ORACLE. Reuses the Track P pipeline unchanged
             (`parseTopTief`, `elabU`, `lowerAllg`) and the model's executable semantics (`rufAt`,
             `execEnd`) to answer two questions about a token list: does the model accept it as a program
             (a G term, `Programm (declOf u)`), and what does `main` return when the model runs it from the
             initial memory `sp0Of`. No semantics is written here.
-/
import Grammatik.Parser.Elab.UebersetzePipeline
import Grammatik.GabbroV.GvStartPflicht

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.GabbroV Gabbro.Grammatik.Parser
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The spelling of one token (the inverse of the lexer on the tokens the printers produce). -/
def tokText : Token → String
  | .ident s => s
  | .wort s => s
  | .num n => toString n
  | .float s => s
  | .text s => "\"" ++ s ++ "\""
  | .zeichen s => s
  | .doku s => "/// " ++ s ++ "\n"
  | .ende => ""

def toksText (ts : List Token) : String := " ".intercalate (ts.map tokText)

/-- `uebersetzeAllg` from tokens: parse, preprocess, elaborate, lower. -/
def uebersetzeToks (toks : List Token) :
    Except String (Σ u : UProg, Programm (declOf u) × List (declOf u).Fn) :=
  match parseTopTief (toks ++ [.ende]) with
  | .error e => .error ("parse: " ++ e)
  | .ok items =>
    match elabU (pre108 items) with
    | .error e => .error ("elab: " ++ e)
    | .ok u =>
      match lowerAllg u with
      | .error e => .error ("lower: " ++ e)
      | .ok (P, fs) => .ok ⟨u, P, fs⟩

/-- The raw word of a result of an optional type. -/
def ergRoh {D : Deklaration} : (o : Option Ty) → ErgVal D o → Int
  | Option.none, _ => 0
  | Option.some _, v => roh v

/-- What the model says `main` does. -/
inductive Ergebnis where
  | wert (n : Int)
  | logik
  | warum
  | hardware
  | keinMain
  | start
  deriving Repr, DecidableEq

def Ergebnis.text : Ergebnis → String
  | .wert n => s!"{n}"
  | .logik => "stop:logic"
  | .warum => "stop:why"
  | .hardware => "stop:hardware"
  | .keinMain => "no-main"
  | .start => "no-start-memory"

/-- Run the function `main` of an elaborated program under the model's semantics: initial memory
    `sp0Of`, an oracle with no axioms, recursion depth and forever-passes `tiefe`. -/
def fuehreMain (tiefe : Nat) (u : UProg) (P : Programm (declOf u)) : Ergebnis :=
  match (List.finRange u.fns.length).find? (fun i => (u.fns.get i).name == "main") with
  | none => .keinMain
  | some f =>
    if h : sp0OkB u = true then
      let O : Orakel (declOf u) :=
        { wirkt := (fun a => nomatch a), regLies := (fun r => nomatch r),
          regSchreib := (fun r => nomatch r), sichtbar := (fun _ _ => true) }
      let σ := (sp0Of u h).welt []
      if hp : (declOf u).params f = [] then
        match rufAt P O tiefe tiefe f σ (hp ▸ Env.nil) with
        | .ok _ v => .wert (ergRoh ((declOf u).erg f) v)
        | .why _ _ => .warum
        | .logik _ => .logik
        | .hardware _ => .hardware
      else .keinMain
    else .start

/-- The names `main` binds with `let` (flat, nested blocks included): the locals a later statement may name. -/
def lokale (u : UProg) : List String :=
  match u.fns.find? (fun f => f.name == "main") with
  | none => []
  | some f => f.body.filterMap fun st => match st with | .bind n _ _ => some n | _ => none

/-- Accept-and-run from tokens: the stage message when the model refuses, else the result and the locals. -/
def pruefeLauf2 (tiefe : Nat) (toks : List Token) : Except String (Ergebnis × List String) :=
  match uebersetzeToks toks with
  | .error e => .error e
  | .ok ⟨u, P, _⟩ => .ok (fuehreMain tiefe u P, lokale u)

/-- Accept-and-run from tokens: `none` when the model refuses (with the stage message), else the result. -/
def pruefeLauf (tiefe : Nat) (toks : List Token) : Except String Ergebnis :=
  match pruefeLauf2 tiefe toks with
  | .error e => .error e
  | .ok (r, _) => .ok r

end Gabbro.Grammatik.Gen
