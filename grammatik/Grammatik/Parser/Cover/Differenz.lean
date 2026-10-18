/-
  File:      Grammatik/Parser/Cover/Differenz.lean
  Subject:   Track P as a CHECKER: the Lean verdict on source text with no Rust exporter in the loop.

  `verdict` runs the whole Lean pipeline on a source text -- lex, parse in depth, elaborate (`elabU`),
  lower every function to a G term (`lowerAllg`) -- and evaluates the Bool of the goal theorem's checker,
  `AkzeptiertX`, on the lowered program with the lock family `SperrInv.leer`, the elaborated locks and
  carriers, and the elaborated thread roots (`UProg.roots`). The answer is one of

    `accept` / `reject`     -- the pipeline decided and `AkzeptiertX` is `true` / `false`;
    `lex-err`, `parse-err`, `elab-err`, `lower-err` + message
                            -- the fragment of Track P does not cover the program (the first stage that
                               refused, with its message): no verdict, never a guess.

  `DifferenzLauf.lean` is the runner (`main`: every `*.gab` of a directory, `NAME<TAB>VERDICT`); the Rust
  differential harness (`crates/gabbro-check/tests/differenzial`) runs it over the generated programs and
  compares it with the Rust checker AND with the exporter route, so the pure-Lean path validates the
  exporter and the checker from source, and the coverage of the generated space it decides is measured.
-/
import Grammatik.GabbroV.GvZensus
import Grammatik.Parser.Elab.UebersetzeAllg3
import Grammatik.Zielsatz.Atomar.AtomarAkzeptiert

namespace Gabbro.Grammatik.Parser.Cover.Differenz

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

/-- The function a thread root names, if the unit has one. -/
def wurzelIdx (u : UProg) (name : String) : Option (Fin u.fns.length) :=
  (List.finRange u.fns.length).find? fun f => (fnAt u f).name == name

/-- **The lock family of an elaborated unit**: the carriers each lock protects (the tables and the statics whose guard
    list names it), and no invariant predicate (`fun _ _ => true`) -- the family the exporter writes as
    `gS` for a lock without an `invariant` clause. (`SperrInv.leer` protects NOTHING, so the footprint
    component would refuse every read under a lock.) -/
def sperrFamilie (u : UProg) : SperrInv (declOf u) :=
  { orte := fun L =>
      ((List.finRange u.tabs.length).filter fun t =>
        ((declOf u).braucht t).any fun x => match x with
          | .inl l => l == L
          | .inr _ => false).map Sum.inl ++
      ((List.finRange u.globs.length).filter fun g =>
        ((declOf u).gbraucht g).any fun x => match x with
          | .inl l => l == L
          | .inr _ => false).map Sum.inr
    inv := fun _ _ => true }

/-- **The checker of the goal theorem on an elaborated unit**: the lowered program, the lock family
    `sperrFamilie`, every lock and every carrier (tables then statics) enumerated, the thread roots of the
    unit as the starts. -/
def akzeptiertU (u : UProg) : Except String Bool :=
  match lowerAllg u with
  | .error e => .error e
  | .ok (P, fs) =>
    haveI : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length))
    let ws : List (declOf u).Fn := u.roots.filterMap fun n => wurzelIdx u n
    let ls : List (declOf u).Lock := List.finRange u.locks.length
    let cs : List ((declOf u).Tab ⊕ (declOf u).Glob) :=
      (List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr
    .ok (AkzeptiertX P (sperrFamilie u) fs ls cs ws)

/-- The ten components of `AkzeptiertX` on an elaborated unit, one digit each (`1` true, `0` false), in
    the order of the definition: fragment, abgeschlossen, fuss, stufen, sperrOrte, wurzeln, einzelnPool,
    renn, antworten, masken. For finding which component refuses a program. -/
def komponenten (u : UProg) : Except String String :=
  match lowerAllg u with
  | .error e => .error e
  | .ok (P, fs) =>
    haveI : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length))
    let ws : List (declOf u).Fn := u.roots.filterMap fun n => wurzelIdx u n
    let ls : List (declOf u).Lock := List.finRange u.locks.length
    let cs : List ((declOf u).Tab ⊕ (declOf u).Glob) :=
      (List.finRange u.tabs.length).map Sum.inl ++ (List.finRange u.globs.length).map Sum.inr
    let S := sperrFamilie u
    let z (b : Bool) : String := if b then "1" else "0"
    .ok (String.join [z (programmImFragmentG P fs), z (abgAlleB P fs), z (fussWXB P S fs ws),
      z (stufenB P fs), z (sperrOrteB S ls), z (wurzelnB ws), z (einzelnPoolB P fs cs ws),
      z (rennB P fs cs ws), z (antwortenB P fs), z (maskenB P fs)])

/-- The verdict on a source text (see the header). -/
def verdict (src : String) : String :=
  match lex src with
  | .error _ => "lex-err"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => "parse-err: " ++ e
    | .ok items =>
      match elabU items with
      | .error e => "elab-err: " ++ e
      | .ok u =>
        match akzeptiertU u with
        | .error e => "lower-err: " ++ e
        | .ok b => if b then "accept" else "reject"

/-- The component string of a source text (see `komponenten`), or the stage that refused. -/
def zerlegt (src : String) : String :=
  match lex src with
  | .error _ => "lex-err"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => "parse-err: " ++ e
    | .ok items =>
      match elabU items with
      | .error e => "elab-err: " ++ e
      | .ok u =>
        match komponenten u with
        | .error e => "lower-err: " ++ e
        | .ok s => s ++ " roots=" ++ toString u.roots

end Gabbro.Grammatik.Parser.Cover.Differenz
