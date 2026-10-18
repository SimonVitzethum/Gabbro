/-
  File:      Grammatik/Gen/Proben.lean
  Subject:   Generator, witnesses and planted defects.

  (1) ROUND TRIP. `rundlaufBlock` (print with `druckAnw`, read with `parseTopBlock`, compare by shape) holds on
      a witness tree; a printer that DROPS A CLAUSE (here: every `else` token) is caught by the same check.
  (2) THE NEW-SYNTAX PROPERTY. The generator reads constructors off the inductive type. `Mini` is a scratch
      inductive with a dummy constructor `neu`; the census over its generated terms contains `neu` with no
      generator code naming it. The same census over the model's surface AST (`SAnw`, closure: `SExpr`,
      `STyp`, `SEnde`, `XKind`) must contain EVERY constructor: a constructor the generator cannot produce
      (a field type it does not know) makes this build fail instead of being skipped silently.
-/
import Grammatik.Gen.Bau

namespace Gabbro.Grammatik.Gen

open Lean Meta Gabbro.Grammatik.Parser

/-! ## 1. Round trip -/

def beispiel : SAnw :=
  .block [ .bind false "x" none (.lit 3),
           .cond (.bin "<" (.variable "x") (.lit 5)) (.block [.set (.variable "x") "=" (.lit 1)] none) []
             (some (.block [] none)) ]
    (some (.ret (some (.variable "x"))))

/-- WITNESS: the surface tree survives print and read. -/
example : rundlaufBlock beispiel = true := by decide +kernel

/-- The same check with another printer. -/
def rundlaufMit (druck : SAnw → List Token) (b : SAnw) : Bool :=
  beqTopBlock (parseTopBlock (druck b ++ [.ende])) (.ok b)

/-- PLANTED DEFECT: a printer that drops the `else` clause. -/
def druckOhneSonst (b : SAnw) : List Token :=
  (druckAnw b).filter fun t => t != Token.wort "else"

example : rundlaufMit druckAnw beispiel = true := by decide +kernel
example : rundlaufMit druckOhneSonst beispiel = false := by decide +kernel

/-! ## 2. The generated space follows the type -/

/-- A scratch inductive: add a constructor here and it is generated, with no other edit. -/
inductive Mini where
  | a : Mini
  | b : Nat → Mini
  | c : Mini → Mini
  | neu : String → Option Mini → Mini

/-- The constructors a closed term mentions. -/
partial def ctorsIn (e : Lean.Expr) : List Name :=
  match e with
  | .const n _ => [n]
  | .app f a => ctorsIn f ++ ctorsIn a
  | _ => []

/-- Constructors of the closure of `root` that appear in `n` generated terms. -/
def erreicht (root : Name) (n : Nat) : MetaM (List Name × List Name) := do
  let k ← baueKontext root
  let mut alle : List Name := []
  for t in k.huelle do alle := alle ++ (← getConstInfoInduct t).ctors
  let mut gesehen : List Name := []
  for _ in [0:n] do
    gesehen := gesehen ++ ctorsIn (← erzeuge k (mkConst root) 4 "")
  return (alle, alle.filter (!gesehen.contains ·))

-- The dummy constructor is generated; no constructor of `Mini` is missing.
#eval show MetaM Unit from do
  IO.setRandSeed 3
  let (alle, fehlt) ← erreicht ``Mini 200
  unless alle.length == 4 && fehlt.isEmpty && alle.contains ``Mini.neu do
    throwError "Mini: not every constructor is generated: missing {fehlt}"

-- Every constructor of the model surface statement language is generated (the closure of `SAnw`).
#eval show MetaM Unit from do
  IO.setRandSeed 5
  let (alle, fehlt) ← erreicht ``SAnw 2500
  unless fehlt.isEmpty do
    throwError "constructors the generator never produced: {fehlt} (of {alle.length})"

end Gabbro.Grammatik.Gen
