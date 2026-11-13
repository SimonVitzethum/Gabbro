module
public import Bruecke.Anweisung.Lokal.Uebersetzung
public import Bruecke.Anweisung.Lokal.Umbenennung
@[expose] public section

/-!
# Statement reading with fresh positional identifiers

The source scope continues to use its declared names and types. Scalar expressions are
read by the existing source reader, then renamed through its first-match position. Callee
entry names and their preconditions remain in the callee's declared scope.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

def namedSide (u : UProg) (fn : UFn) (ns : BodyNames) (v : USide) :
    Option Gabbro.Body.Expr :=
  (sideExpr u fn v).bind (renameScalar (ns.lookup fn))

def namedStmt (u : UProg) (fn : UFn) (ns : BodyNames) (s : UStmt) :
    Option Gabbro.Body.Stmt :=
  (stmtBody u fn s).bind (renameStep (ns.lookup fn))

/-- A binder allocates once; an assignment resolves the existing first-match position. -/
def namedStep (u : UProg) (fn : UFn) (ns : BodyNames) :
    UStmt → Option (Gabbro.Body.Stmt × UFn × BodyNames)
  | .bind x _ v => (namedSide u fn ns v).map
      (fun e => (.bindName (ns.fresh x) e, fn.mitBindung x (0, 0), ns.push x))
  | .bindMut x lo hi v => (namedSide u fn ns v).map
      (fun e => (.bindName (ns.fresh x) e, fn.mitBindung x (lo, hi), ns.push x))
  | .setVar x v =>
      if numericParam fn x then
        match ns.lookup fn x, namedSide u fn ns v with
        | some id, some e => some (.bindName id e, fn, ns)
        | _, _ => none
      else none
  | s => (namedStmt u fn ns s).map (fun b => (b, fn, ns))

/-- The trailing empty return stays empty, as in the source bridge. -/
def namedEnd (u : UProg) (fn : UFn) (ns : BodyNames) : URet → Option (List Gabbro.Body.Stmt)
  | .empty => some []
  | .val v => (namedSide u fn ns v).map (fun e => [.ret (some e)])
  | _ => none

/-- A return inside a block must remain a Body return, including its empty form. -/
def namedRet (u : UProg) (fn : UFn) (ns : BodyNames) : URet → Option Gabbro.Body.Stmt
  | .empty => some (.ret none)
  | .val v => (namedSide u fn ns v).map (fun e => .ret (some e))
  | _ => none

theorem namedSide_some {u : UProg} {fn : UFn} {ns : BodyNames} {v : USide}
    {e : Gabbro.Body.Expr} (h : namedSide u fn ns v = some e) :
    ∃ raw, sideExpr u fn v = some raw ∧ renameScalar (ns.lookup fn) raw = some e := by
  unfold namedSide at h
  cases hr : sideExpr u fn v with
  | none => rw [hr] at h; cases h
  | some raw =>
    rw [hr] at h
    exact ⟨raw, rfl, h⟩

theorem namedStep_bind {u : UProg} {fn fn' : UFn} {ns ns' : BodyNames}
    {x : String} {d : Option (Int × Int)} {v : USide} {b : Gabbro.Body.Stmt}
    (h : namedStep u fn ns (.bind x d v) = some (b, fn', ns')) :
    ∃ e, namedSide u fn ns v = some e ∧ b = .bindName (ns.fresh x) e ∧
      fn' = fn.mitBindung x (0, 0) ∧ ns' = ns.push x := by
  simp only [namedStep] at h
  cases he : namedSide u fn ns v with
  | none => rw [he] at h; cases h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨e, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem namedStep_bindMut {u : UProg} {fn fn' : UFn} {ns ns' : BodyNames}
    {x : String} {lo hi : Int} {v : USide} {b : Gabbro.Body.Stmt}
    (h : namedStep u fn ns (.bindMut x lo hi v) = some (b, fn', ns')) :
    ∃ e, namedSide u fn ns v = some e ∧ b = .bindName (ns.fresh x) e ∧
      fn' = fn.mitBindung x (lo, hi) ∧ ns' = ns.push x := by
  simp only [namedStep] at h
  cases he : namedSide u fn ns v with
  | none => rw [he] at h; cases h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨e, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩

end Gabbro.Bruecke
