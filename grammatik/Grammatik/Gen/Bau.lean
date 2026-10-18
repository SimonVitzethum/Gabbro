/-
  File:      Grammatik/Gen/Bau.lean
  Subject:   Generator, building one program. Candidate statements come from the generic term generator
             (`Reflect.lean`), batch-evaluated to surface trees; the MODEL decides (`uebersetzeToks`): a
             candidate is kept when the program with it still elaborates and lowers to a G term. So a program
             is valid because the model accepts it, and its expected result is what the model's semantics
             (`fuehreMain`) says. Growth is greedy: one accepted statement at a time, then the result
             expression.
-/
import Grammatik.Gen.Reflect
import Grammatik.Gen.Rahmen
import Grammatik.Parser.Print.Item

namespace Gabbro.Grammatik.Gen

open Lean Meta Gabbro.Grammatik.Parser

/-- The seeds of a frame by role (0 integer, 1 truth value, 2 place, 3 lock). -/
def Saat.rolle (s : Saat) : Nat → List String
  | 0 => s.ints
  | 1 => s.bools
  | 2 => s.plaetze
  | _ => s.sperren

/-- Seed `code` = frame * 10000 + role * 1000 + index, parsed by the reader. -/
def saatExpr (code : Nat) : SExpr :=
  match rahmenSaaten[code / 10000]? with
  | none => .lit 0
  | some s =>
    match (s.rolle (code / 1000 % 10))[code % 1000]? with
    | none => .lit 0
    | some t => match parseTopAusText t with | .ok e => e | .error _ => .lit 0

/-- The body as text: `{ stmts return e; }`. -/
def rumpfText (ss : List SAnw) (e : SExpr) : String :=
  toksText (druckAnw (.block ss (some (.ret (some e)))))

/-- The tokens of a whole unit of frame `r`. -/
def einheitToks (r : Rahmen) (ss : List SAnw) (e : SExpr) : List Token :=
  rohToks (r.text (rumpfText ss e))

/-- Does the printed statement parse on its own? (cheap pre-filter before the elaborator) -/
def liest (c : SAnw) : Option String :=
  match parseTopBlock (druckAnw (.block [c] none) ++ [.ende]) with
  | .ok _ => none
  | .error e => some e

/-- The constructor names a value mentions (by its `Repr`; a name counts when no identifier character
    follows it, so `ret` is not found in `retry`). -/
def erwaehnt (s : String) (c : String) : Bool :=
  let pat := c.toList
  let rec go : List Char → Nat → Bool
    | [], _ => false
    | _, 0 => false
    | l@(_ :: t), fuel + 1 =>
      (l.take pat.length == pat &&
        (match l.drop pat.length with
         | [] => true
         | d :: _ => !(d.isAlphanum || d == '_'))) || go t fuel
  let cs := s.toList
  go cs cs.length

unsafe def evalAnwsU (e : Lean.Expr) : MetaM (List SAnw) :=
  evalExpr (List SAnw) (mkApp (mkConst ``List [levelZero]) (mkConst ``SAnw)) e
unsafe def evalExprsU (e : Lean.Expr) : MetaM (List SExpr) :=
  evalExpr (List SExpr) (mkApp (mkConst ``List [levelZero]) (mkConst ``SExpr)) e
@[implemented_by evalAnwsU] opaque evalAnws : Lean.Expr → MetaM (List SAnw)
@[implemented_by evalExprsU] opaque evalExprs : Lean.Expr → MetaM (List SExpr)

/-- A batch of `n` generated values of type `T` (budget `fuel`), as one evaluation. -/
def charge (k : Kontext) (typ : Name) (n fuel : Nat) : MetaM Lean.Expr := do
  let mut es := #[]
  for _ in [0:n] do es := es.push (← erzeuge k (mkConst typ) fuel "")
  mkListLit (mkConst typ) es.toList

/-- The generation context of frame `i`: the closure of `SAnw`, and the frame's seeds. -/
def kontextFuer (k0 : Kontext) (i : Nat) : Kontext :=
  { k0 with saatTyp := ``SExpr, saatFn := ``saatExpr,
            saat := fun role =>
              match rahmenSaaten[i]? with
              | some s => some (i * 10000 + role * 1000, (s.rolle role).length)
              | none => none }

/-- Result of building one program. -/
structure Bau where
  rahmen : String
  stmts : List SAnw
  ender : SExpr
  ergebnis : Ergebnis
  versuche : Nat
  /-- every candidate statement generated, and the ones the model took (for the census). -/
  alle : List SAnw
  genommen : List SAnw
  /-- stage messages of the model's refusals. -/
  absagen : List String

def kurz (s : String) : String := String.ofList (s.toList.take 40)

/-- Grow a program in frame `r`: up to `ziel` statements within `versuche` candidates. -/
def baue (k0 : Kontext) (fi ziel versuche tiefe : Nat) : MetaM Bau := do
  let r := rahmen[fi]!
  let k := kontextFuer k0 fi
  let mut ss : List SAnw := []
  let mut alle : List SAnw := []
  let mut gen : List SAnw := []
  let mut ab : List String := []
  let mut n := 0
  while n < versuche && ss.length < ziel do
    let cs ← evalAnws (← charge k ``SAnw 64 (2 + n % 3))
    for c in cs do
      if n ≥ versuche || ss.length ≥ ziel then break
      n := n + 1
      alle := c :: alle
      match liest c with
      | some e => ab := ("parse: " ++ kurz e) :: ab; continue
      | none => pure ()
      match pruefeLauf tiefe (einheitToks r (ss ++ [c]) (.lit 0)) with
      | .ok (.wert _) => ss := ss ++ [c]; gen := c :: gen
      | .ok _ => ab := "model run stops" :: ab
      | .error e => ab := kurz e :: ab
  -- the result expression
  let mut e : SExpr := .lit 0
  let mut fertig := false
  let mut m := 0
  while m < 8 && !fertig do
    m := m + 1
    for c in (← evalExprs (← charge k ``SExpr 64 (1 + m % 3))) do
      if fertig then break
      match pruefeLauf tiefe (einheitToks r ss c) with
      | .ok (.wert _) => e := c; fertig := true
      | _ => pure ()
  let erg := match pruefeLauf tiefe (einheitToks r ss e) with
    | .ok x => x
    | .error _ => .keinMain
  return { rahmen := r.name, stmts := ss, ender := e, ergebnis := erg, versuche := n,
           alle := alle, genommen := gen, absagen := ab }

/-- The source text of a built program: the declarations on the first line, `{`, one statement per line
    (so a harness can shrink by deleting lines), the result, `}` and the closing brace of the module. -/
def Bau.text (b : Bau) (r : Rahmen) : String :=
  let rumpf := "{\n" ++ "\n".intercalate (b.stmts.map fun c => toksText (druckAnw c)) ++
    "\nreturn " ++ toksText (druckToks b.ender) ++ " ;\n}\n"
  r.text rumpf ++ "\n"

end Gabbro.Grammatik.Gen
