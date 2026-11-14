module
public import Bruecke.Anweisung.Lokal.Benannt
public import Bruecke.Anweisung.Lokal.Kopf
public import Bruecke.Anweisung.Schleife.Basis
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze

/-- Ordinary ending statements preserve their scope. -/
def endLeafB : UStmt → Bool
  | .assign .. | .assignTab .. | .assignOpt .. | .assignTabOpt .. | .assignGlob .. | .assignGlobB .. | .call .. | .setVar .. | .setVarB .. => true
  | _ => false

theorem endLeafB_ok {st : UStmt} (h : endLeafB st = true) : LeseEinzeln st := by
  cases st <;> first | exact True.intro | cases h

/-- Scalar locals use the shared positional statement reader. -/
def endLocalB : UStmt → Bool
  | .bind .. | .bindMut .. | .bindB .. => true
  | _ => false

/-- Read a mandatory ending, including numeric, Boolean and record locals.
    An ending arm has no joining continuation, so its local identifiers cannot escape. -/
def endBodyZ (u : UProg) : Nat → UFn → BodyNames → List UStmt →
    Option (List Gabbro.Body.Stmt × List UStmt)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | _ + 1, fn, ns, .ret r :: rest => (retZ u fn ns r).map (fun b => ([b], rest))
  | _ + 1, _, _, .leave _ :: rest => some ([.leave], rest)
  | _ + 1, _, _, .next _ :: rest => some ([.exit], rest)
  | k + 1, fn, ns, .bindW x d v :: rest => do
      let ty ← recordBinderType u fn d v
      let e ← namedSide u fn ns v
      let (bs, tail) ← endBodyZ u k (fn.mitWert x ty) (ns.push x) rest
      pure (.bindName (ns.fresh x) e :: bs, tail)
  | k + 1, fn, ns, st :: rest =>
      if endLocalB st then do
        let (b, fn', ns') ← schrittB u fn ns st
        let (bs, tail) ← endBodyZ u k fn' ns' rest
        pure (b :: bs, tail)
      else if endLeafB st then do
        let (b, _, _) ← schrittB u fn ns st
        let (bs, tail) ← endBodyZ u k fn ns rest
        pure (b :: bs, tail)
      else none

/-- The narrowed source variable must already be a visible number. -/
def narrowName (fn : UFn) (ns : BodyNames) (x : String) : Option Gabbro.Body.Expr :=
  if numericParam fn x then (ns.lookup fn x).map Gabbro.Body.Expr.name else none

def narrowTest (e : Gabbro.Body.Expr) (lo hi : Int) : Gabbro.Body.Expr :=
  .bin .and (.bin .le (.lit (.int lo)) e) (.bin .le e (.lit (.int hi)))

def narrowStep (ns : BodyNames) (x : String) (lo hi : Int) (e : Gabbro.Body.Expr)
    (err : List Gabbro.Body.Stmt) : Gabbro.Body.Stmt :=
  .ite (narrowTest e lo hi) [.bindName (ns.fresh x) e] err

theorem narrowName_some {fn : UFn} {ns : BodyNames} {x : String} {e : Gabbro.Body.Expr}
    (h : narrowName fn ns x = some e) :
    numericParam fn x = true ∧ ∃ id, ns.lookup fn x = some id ∧ e = .name id := by
  unfold narrowName at h
  split at h
  · rename_i hn
    cases hid : ns.lookup fn x with
    | none => rw [hid] at h; cases h
    | some id =>
      rw [hid] at h
      cases h
      exact ⟨hn, id, rfl, rfl⟩
  · cases h

theorem narrowName_sicht {u : UProg} {ft fn : UFn} (h : Sicht u ft fn)
    (ns : BodyNames) (x : String) : narrowName ft ns x = narrowName fn ns x := by
  simp only [narrowName, h.1 x, BodyNames.lookup_sicht h ns x]

end Gabbro.Bruecke
