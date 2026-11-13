module
public import Bruecke.Anweisung.Lokal.Benannt
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Match subjects keep option identity in the canonical lowerer. Unsupported storage
    subjects remain refused; local lookup uses the function-wide positional supply. -/
def optionZ (fn : UFn) (ns : BodyNames) : UOpt → Option Gabbro.Body.Expr
  | .nichts => some (.lit .absent)
  | .etwas ix => (renameScalar (ns.lookup fn) (idxExpr ix)).map Gabbro.Body.Expr.someOf
  | .var x => (ns.lookup fn x).map Gabbro.Body.Expr.name
  | _ => none

theorem optionZ_sicht {u : UProg} {ft fn : UFn} (h : Sicht u ft fn)
    (ns : BodyNames) (v : UOpt) : optionZ ft ns v = optionZ fn ns v := by
  have hn : ns.lookup ft = ns.lookup fn := funext (BodyNames.lookup_sicht h ns)
  cases v <;> simp only [optionZ, hn]

/-- A reason subject is resolved at its first source position, with its exact case count. -/
def reasonSubject (fn : UFn) (ns : BodyNames) (x : String) : Option (Nat × Gabbro.Body.Expr) := do
  let .why n ← valueParamTy fn x | none
  let id ← ns.lookup fn x
  pure (n, .name id)

theorem reasonSubject_sicht {u : UProg} {ft fn : UFn} (h : Sicht u ft fn)
    (ns : BodyNames) (x : String) : reasonSubject ft ns x = reasonSubject fn ns x := by
  simp only [reasonSubject, h.2.2.2.2 x, BodyNames.lookup_sicht h ns x]

/-- Bare tags share the reason-arm reader. Payload-bearing schemas refuse explicitly. -/
def tagSubject (fn : UFn) (ns : BodyNames) (x : String) : Option (List (Option Ty) × Gabbro.Body.Expr) := do
  let .sum cs ← valueParamTy fn x | none
  if !cs.all Option.isNone then none else do
    let id ← ns.lookup fn x
    pure (cs, .name id)

theorem tagSubject_sicht {u : UProg} {ft fn : UFn} (h : Sicht u ft fn)
    (ns : BodyNames) (x : String) : tagSubject ft ns x = tagSubject fn ns x := by
  simp only [tagSubject, h.2.2.2.2 x, BodyNames.lookup_sicht h ns x]

def tagArms (arms : List (String × List Gabbro.Body.Stmt)) :
    List (String × Option String × List Gabbro.Body.Stmt) := arms.map (fun a => (a.1, none, a.2))

end Gabbro.Bruecke
