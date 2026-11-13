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

variable {u : UProg}

def condZ (u : UProg) (fn : UFn) (ns : BodyNames) (c : UEns) :
    Option Gabbro.Body.Expr :=
  (rawCond u fn c).bind (renameScalar (ns.lookup fn))

def namedSide (u : UProg) (fn : UFn) (ns : BodyNames) (v : USide) :
    Option Gabbro.Body.Expr :=
  (sideExprG u fn v).bind (renameScalar (ns.lookup fn))

def namedStmt (u : UProg) (fn : UFn) (ns : BodyNames) (s : UStmt) :
    Option Gabbro.Body.Stmt :=
  (stmtBody u fn s).bind (renameStep (ns.lookup fn))

/-- Result calls use the same argument reader and renamer as discard calls. Only the
    scalar result types represented by this bridge are admitted. -/
def namedResult (u : UProg) (fn : UFn) (ns : BodyNames) (x g : String)
    (args : List UArg) : Option (Gabbro.Body.Stmt × Ty) := do
  let gf ← fnSuch u g
  let ty ← gf.ergTy
  let _ ← shapeOfTy ty
  let es ← argsExpr u fn args
  let renamed ← renameStep.renameScalars (ns.lookup fn) es
  pure (.bindCall (ns.fresh x) g (gf.params.map (·.1)) renamed (preExpr gf), ty)

/-- A binder allocates once; an assignment resolves the existing first-match position. -/
def schrittB (u : UProg) (fn : UFn) (ns : BodyNames) :
    UStmt → Option (Gabbro.Body.Stmt × UFn × BodyNames)
  | .bind x _ v => (namedSide u fn ns v).map
      (fun e => (.bindName (ns.fresh x) e, fn.mitBindung x (0, 0), ns.push x))
  | .bindMut x lo hi v => (namedSide u fn ns v).map
      (fun e => (.bindName (ns.fresh x) e, fn.mitBindung x (lo, hi), ns.push x))
  | .bindB x v => (condZ u fn ns v).map
      (fun e => (.bindName (ns.fresh x) e, fn.mitBindungB x, ns.push x))
  | .bindCall x g args => (namedResult u fn ns x g args).map
      (fun p => (p.1, fn.mitTy x p.2, ns.push x))
  | .setVarB x v =>
      match ns.lookup fn x, condZ u fn ns v with
      | some id, some e => some (.bindName id e, fn, ns)
      | _, _ => none
  | .setVar x v =>
      if assignableParam fn x then
        match ns.lookup fn x, namedSide u fn ns v with
        | some id, some e => some (.bindName id e, fn, ns)
        | _, _ => none
      else none
  | s => (namedStmt u fn ns s).map (fun b => (b, fn, ns))

/-- The trailing empty return stays empty, as in the source bridge. -/
def namedEnd (u : UProg) (fn : UFn) (ns : BodyNames) : URet → Option (List Gabbro.Body.Stmt)
  | .empty => some []
  | .val v | .wert v => (namedSide u fn ns v).map (fun e => [.ret (some e)])
  | .bool v => (condZ u fn ns v).map (fun e => [.ret (some e)])
  | _ => none

/-- A return inside a block must remain a Body return, including its empty form. -/
def retZ (u : UProg) (fn : UFn) (ns : BodyNames) : URet → Option Gabbro.Body.Stmt
  | .empty => some (.ret none)
  | .val v => (namedSide u fn ns v).map (fun e => .ret (some e))
  | .bool v => (condZ u fn ns v).map (fun e => .ret (some e))
  | _ => none

theorem condZ_some {fn : UFn} {ns : BodyNames} {cnd : UEns} {ce : Gabbro.Body.Expr}
    (h : condZ u fn ns cnd = some ce) :
    ∃ raw, ∃ a : Acc, ensExpr u fn {} cnd = some (raw, a) ∧
      a.olds.length = 0 ∧ a.result = false ∧ renameScalar (ns.lookup fn) raw = some ce := by
  unfold condZ at h
  cases hr : rawCond u fn cnd with
  | none => rw [hr] at h; cases h
  | some raw =>
    rw [hr] at h
    unfold rawCond at hr
    split at hr
    · rename_i x a hx
      split at hr
      · rename_i hc
        cases hr
        exact ⟨raw, a, hx, hc.1, hc.2, h⟩
      · cases hr
    · cases hr

theorem condZ_sicht {fT fn : UFn} (h : Sicht u fT fn) (ns : BodyNames) (c : UEns) :
    condZ u fT ns c = condZ u fn ns c := by
  have hn : ns.lookup fT = ns.lookup fn := funext (BodyNames.lookup_sicht h ns)
  unfold condZ rawCond
  rw [ensExpr_sicht h, hn]


theorem namedSide_some {u : UProg} {fn : UFn} {ns : BodyNames} {v : USide}
    {e : Gabbro.Body.Expr} (h : namedSide u fn ns v = some e) :
    ∃ raw, sideExprG u fn v = some raw ∧ renameScalar (ns.lookup fn) raw = some e := by
  unfold namedSide at h
  cases hr : sideExprG u fn v with
  | none => rw [hr] at h; cases h
  | some raw =>
    rw [hr] at h
    exact ⟨raw, rfl, h⟩

theorem schrittB_bind {u : UProg} {fn fn' : UFn} {ns ns' : BodyNames}
    {x : String} {d : Option (Int × Int)} {v : USide} {b : Gabbro.Body.Stmt}
    (h : schrittB u fn ns (.bind x d v) = some (b, fn', ns')) :
    ∃ e, namedSide u fn ns v = some e ∧ b = .bindName (ns.fresh x) e ∧
      fn' = fn.mitBindung x (0, 0) ∧ ns' = ns.push x := by
  simp only [schrittB] at h
  cases he : namedSide u fn ns v with
  | none => rw [he] at h; cases h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨e, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem schrittB_bindMut {u : UProg} {fn fn' : UFn} {ns ns' : BodyNames}
    {x : String} {lo hi : Int} {v : USide} {b : Gabbro.Body.Stmt}
    (h : schrittB u fn ns (.bindMut x lo hi v) = some (b, fn', ns')) :
    ∃ e, namedSide u fn ns v = some e ∧ b = .bindName (ns.fresh x) e ∧
      fn' = fn.mitBindung x (lo, hi) ∧ ns' = ns.push x := by
  simp only [schrittB] at h
  cases he : namedSide u fn ns v with
  | none => rw [he] at h; cases h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨e, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem schrittB_bindB {u : UProg} {fn fn' : UFn} {ns ns' : BodyNames}
    {x : String} {v : UEns} {b : Gabbro.Body.Stmt}
    (h : schrittB u fn ns (.bindB x v) = some (b, fn', ns')) :
    ∃ e, condZ u fn ns v = some e ∧ b = .bindName (ns.fresh x) e ∧
      fn' = fn.mitBindungB x ∧ ns' = ns.push x := by
  simp only [schrittB] at h
  cases he : condZ u fn ns v with
  | none => rw [he] at h; cases h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨e, rfl, h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem schrittB_setVarB {u : UProg} {fn fn' : UFn} {ns ns' : BodyNames}
    {x : String} {v : UEns} {b : Gabbro.Body.Stmt}
    (h : schrittB u fn ns (.setVarB x v) = some (b, fn', ns')) :
    ∃ id e, ns.lookup fn x = some id ∧ condZ u fn ns v = some e ∧
      b = .bindName id e ∧ fn' = fn ∧ ns' = ns := by
  simp only [schrittB] at h
  split at h
  · rename_i id e hid he
    cases h
    exact ⟨id, e, hid, he, rfl, rfl, rfl⟩
  · cases h

theorem namedStmt_some {u : UProg} {fn : UFn} {ns : BodyNames} {s : UStmt}
    {b : Gabbro.Body.Stmt} (h : namedStmt u fn ns s = some b) :
    ∃ raw, stmtBody u fn s = some raw ∧ renameStep (ns.lookup fn) raw = some b := by
  unfold namedStmt at h
  cases hr : stmtBody u fn s with
  | none => rw [hr] at h; cases h
  | some raw => rw [hr] at h; exact ⟨raw, rfl, h⟩

theorem schrittB_setVar {u : UProg} {fn fn' : UFn} {ns ns' : BodyNames}
    {x : String} {v : USide} {b : Gabbro.Body.Stmt}
    (h : schrittB u fn ns (.setVar x v) = some (b, fn', ns')) :
    assignableParam fn x = true ∧ ∃ id e, ns.lookup fn x = some id ∧
      namedSide u fn ns v = some e ∧ b = .bindName id e ∧ fn' = fn ∧ ns' = ns := by
  simp only [schrittB] at h
  split at h
  · rename_i hn
    split at h
    · rename_i id e hid he
      cases h
      exact ⟨hn, id, e, hid, he, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- The other supported statements preserve the active scope and allocation history. -/
theorem schrittB_stmt {u : UProg} {fn fn' : UFn} {ns ns' : BodyNames}
    {s : UStmt} {b : Gabbro.Body.Stmt}
    (h : schrittB u fn ns s = some (b, fn', ns'))
    (hs : ∀ x d v, s ≠ .bind x d v) (hm : ∀ x lo hi v, s ≠ .bindMut x lo hi v)
    (hv : ∀ x v, s ≠ .setVar x v)
    (hbb : ∀ x v, s ≠ .bindB x v) (hvb : ∀ x v, s ≠ .setVarB x v)
    (hcall : ∀ x g args, s ≠ .bindCall x g args) :
    namedStmt u fn ns s = some b ∧ fn' = fn ∧ ns' = ns := by
  have he : (namedStmt u fn ns s).map (fun b => (b, fn, ns)) = some (b, fn', ns') := by
    cases s
    case bind x d v => exact False.elim (hs x d v rfl)
    case bindMut x lo hi v => exact False.elim (hm x lo hi v rfl)
    case setVar x v => exact False.elim (hv x v rfl)
    case bindB x v => exact False.elim (hbb x v rfl)
    case setVarB x v => exact False.elim (hvb x v rfl)
    case bindCall x g args => exact False.elim (hcall x g args rfl)
    all_goals exact h
  cases hb : namedStmt u fn ns s with
  | none => rw [hb] at he; cases he
  | some b' =>
    rw [hb] at he
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨rfl, rfl, rfl⟩

theorem namedSide_sicht {u : UProg} {fT fn : UFn} (h : Sicht u fT fn)
    (ns : BodyNames) (v : USide) : namedSide u fT ns v = namedSide u fn ns v := by
  have hn : ns.lookup fT = ns.lookup fn := funext (BodyNames.lookup_sicht h ns)
  unfold namedSide
  rw [sideExprG_sicht h, hn]

theorem namedStmt_sicht {u : UProg} {fT fn : UFn} (h : Sicht u fT fn)
    (ns : BodyNames) (s : UStmt) : namedStmt u fT ns s = namedStmt u fn ns s := by
  have hn : ns.lookup fT = ns.lookup fn := funext (BodyNames.lookup_sicht h ns)
  unfold namedStmt
  rw [stmtBody_sicht h, hn]

theorem namedEnd_sicht {u : UProg} {fT fn : UFn} (h : Sicht u fT fn)
    (ns : BodyNames) (r : URet) : namedEnd u fT ns r = namedEnd u fn ns r := by
  cases r <;> simp only [namedEnd, namedSide_sicht h, condZ_sicht h]

theorem retZ_sicht {u : UProg} {fT fn : UFn} (h : Sicht u fT fn)
    (ns : BodyNames) (r : URet) : retZ u fT ns r = retZ u fn ns r := by
  cases r <;> simp only [retZ, namedSide_sicht h, condZ_sicht h]

end Gabbro.Bruecke
