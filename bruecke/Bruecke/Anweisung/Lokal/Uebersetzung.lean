module
public import Bruecke.Nachbedingung
@[expose] public section

/-!
# C3: local bindings and assignment in the Body translation

`zuBody` (`Pflichten.lean`) carries slot writes, direct calls and the trailing return; every
function with a `let` is outside it. `zuBodyB` threads the scope the way the lowering does
(`lowBodyF`): after `let x = v;` (`UStmt.bind`) and `let mut x : T = v;` (`UStmt.bindMut`) the
statements are read under `fn.mitBindung x ..`, and `x = v;` on a number local (`UStmt.setVar`)
keeps the scope. All three become Body's `bindName x e` -- a binding, or a rebinding.

The range of a `let` without annotation is computed by the lowering from typed terms, so the
translation threads `fn.mitBindung x (0, 0)`: the Body reading of a side depends on a scope only
through which names are numbers, which name a pointer and which pointer names a table (`Sicht`),
and those do not see a range. `zuBodyB` agrees with `zuBody` wherever `zuBody` has an answer
(`zuBodyB_of_zuBody`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The translation -/

/-- One statement of a body in the scope `fn`: its Body statement and the scope after it. -/
def schrittB (u : UProg) (fn : UFn) : UStmt → Option (Gabbro.Body.Stmt × UFn)
  | .bind x _ v => (sideExpr u fn v).map (fun e => (.bindName x e, fn.mitBindung x (0, 0)))
  | .bindMut x lo hi v => (sideExpr u fn v).map (fun e => (.bindName x e, fn.mitBindung x (lo, hi)))
  | .setVar x v =>
      if numericParam fn x then (sideExpr u fn v).map (fun e => (.bindName x e, fn)) else none
  | s => (stmtBody u fn s).map (fun b => (b, fn))

/-- The statements and the trailing return, the scope threaded through every binder. -/
def stmtsBodyB (u : UProg) : UFn → List UStmt → URet → Option (List Gabbro.Body.Stmt)
  | fn, [], r => endBody u fn r
  | fn, s :: ss, r =>
      match schrittB u fn s with
      | none => none
      | some (b, fn') => (stmtsBodyB u fn' ss r).map (b :: ·)

/-- **`zuBodyB`** -- the body of `f` with its local bindings, as `Gabbro.Body` sees it. -/
def zuBodyB (u : UProg) (f : UFn) : Option (List Gabbro.Body.Stmt) := stmtsBodyB u f f.body f.ret

/-! ## 2. Reading a translation back -/

theorem stmtsBodyB_cons {fT : UFn} {s : UStmt} {ss : List UStmt} {r : URet}
    {bs : List Gabbro.Body.Stmt} (h : stmtsBodyB u fT (s :: ss) r = some bs) :
    ∃ b fT' bs', schrittB u fT s = some (b, fT') ∧ stmtsBodyB u fT' ss r = some bs' ∧
      bs = b :: bs' := by
  simp only [stmtsBodyB] at h
  split at h
  · cases h
  · rename_i b fT' hs
    cases hr : stmtsBodyB u fT' ss r with
    | none => rw [hr] at h; cases h
    | some bs' =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨b, fT', bs', hs, hr, h.symm⟩

theorem schrittB_bind {fn fn' : UFn} {x : String} {d : Option (Int × Int)} {v : USide}
    {b : Gabbro.Body.Stmt} (h : schrittB u fn (.bind x d v) = some (b, fn')) :
    ∃ e, sideExpr u fn v = some e ∧ b = .bindName x e ∧ fn' = fn.mitBindung x (0, 0) := by
  simp only [schrittB] at h
  cases he : sideExpr u fn v with
  | none => rw [he] at h; cases h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨e, rfl, h.1.symm, h.2.symm⟩

theorem schrittB_bindMut {fn fn' : UFn} {x : String} {lo hi : Int} {v : USide}
    {b : Gabbro.Body.Stmt} (h : schrittB u fn (.bindMut x lo hi v) = some (b, fn')) :
    ∃ e, sideExpr u fn v = some e ∧ b = .bindName x e ∧ fn' = fn.mitBindung x (lo, hi) := by
  simp only [schrittB] at h
  cases he : sideExpr u fn v with
  | none => rw [he] at h; cases h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨e, rfl, h.1.symm, h.2.symm⟩

theorem schrittB_setVar {fn fn' : UFn} {x : String} {v : USide}
    {b : Gabbro.Body.Stmt} (h : schrittB u fn (.setVar x v) = some (b, fn')) :
    numericParam fn x = true ∧ ∃ e, sideExpr u fn v = some e ∧ b = .bindName x e ∧ fn' = fn := by
  simp only [schrittB] at h
  split at h
  · rename_i hn
    cases he : sideExpr u fn v with
    | none => rw [he] at h; cases h
    | some e =>
      rw [he] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨hn, e, rfl, h.1.symm, h.2.symm⟩
  · cases h

/-- A statement `zuBody` carries keeps the scope. -/
theorem schrittB_sonst {fn : UFn} {s : UStmt} {b0 : Gabbro.Body.Stmt}
    (hs : stmtBody u fn s = some b0) : schrittB u fn s = some (b0, fn) := by
  cases s
  case assign p f i v =>
    show (stmtBody u fn _).map _ = _
    rw [hs]; rfl
  case assignTab p f i v =>
    show (stmtBody u fn _).map _ = _
    rw [hs]; rfl
  case call g as =>
    show (stmtBody u fn _).map _ = _
    rw [hs]; rfl
  all_goals simp [stmtBody] at hs

/-- The other statements: what `stmtBody` answers, in the same scope. -/
theorem schrittB_stmt {fn fn' : UFn} {s : UStmt} {b : Gabbro.Body.Stmt}
    (h : schrittB u fn s = some (b, fn')) (hs : ∀ x d v, s ≠ .bind x d v)
    (hm : ∀ x lo hi v, s ≠ .bindMut x lo hi v) (hv : ∀ x v, s ≠ .setVar x v) :
    stmtBody u fn s = some b ∧ fn' = fn := by
  cases hb : stmtBody u fn s with
  | none =>
    exfalso
    cases s
    case bind x d v => exact hs x d v rfl
    case bindMut x lo hi v => exact hm x lo hi v rfl
    case setVar x v => exact hv x v rfl
    case assign p f i v =>
      have h' : (stmtBody u fn _).map (fun b => (b, fn)) = some (b, fn') := h
      rw [hb] at h'; cases h'
    case assignTab p f i v =>
      have h' : (stmtBody u fn _).map (fun b => (b, fn)) = some (b, fn') := h
      rw [hb] at h'; cases h'
    case call g as =>
      have h' : (stmtBody u fn _).map (fun b => (b, fn)) = some (b, fn') := h
      rw [hb] at h'; cases h'
    all_goals simp [schrittB, stmtBody] at h
  | some b1 =>
    rw [schrittB_sonst hb] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by first | rw [h.1] | rw [hb, h.1], h.2.symm⟩

/-! ## 3. Agreement with `zuBody` -/

theorem stmtsBodyB_of (r : URet) : ∀ (fn : UFn) (ss : List UStmt) (bs eB : List Gabbro.Body.Stmt),
    stmtsBody u fn ss = some bs → endBody u fn r = some eB → stmtsBodyB u fn ss r = some (bs ++ eB)
  | fn, [], bs, eB, h, he => by
      simp only [stmtsBody, Option.some.injEq] at h
      subst h
      simpa only [stmtsBodyB, List.nil_append] using he
  | fn, s :: ss, bs, eB, h, he => by
      simp only [stmtsBody] at h
      split at h
      · rename_i x xs hx hxs
        simp only [Option.some.injEq] at h
        subst h
        have ih := stmtsBodyB_of r fn ss xs eB hxs he
        simp only [stmtsBodyB, schrittB_sonst hx, ih, Option.map_some, List.cons_append]
      · cases h

/-- **`zuBodyB` extends `zuBody`**: on a body without binders both give the same program. -/
theorem zuBodyB_of_zuBody {f : UFn} {b : List Gabbro.Body.Stmt} (h : zuBody u f = some b) :
    zuBodyB u f = some b := by
  rw [zuBody_eq] at h
  cases hs : stmtsBody u f f.body with
  | none => rw [hs] at h; cases h
  | some ss =>
    rw [hs] at h
    cases he : endBody u f f.ret with
    | none => rw [he] at h; cases h
    | some eB =>
      rw [he] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact stmtsBodyB_of f.ret f f.body ss eB hs he

/-- A call of the translated statements finds its callee. -/
theorem callee_gefundenB (r : URet) : ∀ (fT : UFn) (ss : List UStmt) (bs : List Gabbro.Body.Stmt),
    stmtsBodyB u fT ss r = some bs → ∀ (g : String) (args : List UArg),
      UStmt.call g args ∈ ss → ∃ gf, fnSuch u g = some gf
  | _, [], _, _, _, _, hm => absurd hm List.not_mem_nil
  | fT, s :: ss, _, h, g, args, hm => by
      obtain ⟨b, fT', bs', hs, hr, _⟩ := stmtsBodyB_cons h
      rcases List.mem_cons.mp hm with rfl | hm
      · have hs' : (stmtBody u fT (.call g args)).map (fun b => (b, fT)) = some (b, fT') := hs
        cases hb : stmtBody u fT (.call g args) with
        | none => rw [hb] at hs'; cases hs'
        | some x =>
          simp only [stmtBody] at hb
          split at hb
          · rename_i gf es hgf _
            exact ⟨gf, hgf⟩
          · cases hb
      · exact callee_gefundenB r fT' ss bs' hr g args hm

/-! ## 4. The view of a scope: what the Body reading sees of it -/

/-- Two scopes the Body reading cannot tell apart: the same numbers, the same pointer tables and
    the same table pointers. -/
def Sicht (u : UProg) (fT fn : UFn) : Prop :=
  (∀ p, numericParam fT p = numericParam fn p) ∧ (∀ p, ptrTab u fT p = ptrTab u fn p) ∧
    ∀ t, ptrParam u fT t = ptrParam u fn t

theorem Sicht.refl (fn : UFn) : Sicht u fn fn := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem numericParam_mitBindung (f : UFn) (x : String) (w : Int × Int) (p : String) :
    numericParam (f.mitBindung x w) p = if x = p then true else numericParam f p := by
  by_cases h : x = p
  · subst h
    simp [numericParam, UFn.mitBindung]
  · simp [numericParam, UFn.mitBindung, h]

theorem ptrTab_mitBindung (f : UFn) (x : String) (w : Int × Int) (p : String) :
    ptrTab u (f.mitBindung x w) p = if x = p then none else ptrTab u f p := by
  by_cases h : x = p
  · subst h
    simp [ptrTab, UFn.mitBindung]
  · simp [ptrTab, UFn.mitBindung, h]

theorem ptrParam_mitBindung (f : UFn) (x : String) (w : Int × Int) (t : String) :
    ptrParam u (f.mitBindung x w) t = ptrParam u f t := by
  first
    | rfl
    | simp [ptrParam, UFn.mitBindung]

/-- Binding one name in both scopes keeps the view, whatever the two ranges. -/
theorem Sicht.bind {fT fn : UFn} (h : Sicht u fT fn) (x : String) (w w' : Int × Int) :
    Sicht u (fT.mitBindung x w) (fn.mitBindung x w') := by
  refine ⟨fun p => ?_, fun p => ?_, fun t => ?_⟩
  · rw [numericParam_mitBindung, numericParam_mitBindung, h.1 p]
  · rw [ptrTab_mitBindung, ptrTab_mitBindung, h.2.1 p]
  · rw [ptrParam_mitBindung, ptrParam_mitBindung, h.2.2 t]

theorem slotPlace_sicht {fT fn : UFn} (h : Sicht u fT fn) (s : USide) :
    slotPlace u fT s = slotPlace u fn s := by
  cases s <;> simp [slotPlace, h.2.1]

theorem sideExpr_sicht {fT fn : UFn} (h : Sicht u fT fn) (sd : USide) :
    sideExpr u fT sd = sideExpr u fn sd := by
  have recurse (sd' : USide) (hlt : sizeOf sd' < sizeOf sd) :
      sideExpr u fT sd' = sideExpr u fn sd' :=
    sideExpr_sicht h sd'
  cases sd with
  | param p => simp only [sideExpr, h.1 p]
  | slot p fld i => simp only [sideExpr, slotPlace_sicht h]
  | add x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExpr, hx, hy]
  | sub x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExpr, hx, hy]
  | mul x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExpr, hx, hy]
  | conv lo hi x =>
    have hx := recurse x (by simp_wf; omega)
    simp only [sideExpr, hx]
  | band x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExpr, hx, hy]
  | bor x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExpr, hx, hy]
  | bxor x y =>
    have hx := recurse x (by simp_wf; omega)
    have hy := recurse y (by simp_wf; omega)
    simp only [sideExpr, hx, hy]
  | _ => simp [sideExpr, slotPlace_sicht h]
termination_by sizeOf sd
decreasing_by assumption

theorem argExpr_sicht {fT fn : UFn} (h : Sicht u fT fn) (a : UArg) :
    argExpr u fT a = argExpr u fn a := by
  cases a <;> simp [argExpr, h.2.2, sideExpr_sicht h]

theorem argsExpr_sicht {fT fn : UFn} (h : Sicht u fT fn) :
    ∀ as : List UArg, argsExpr u fT as = argsExpr u fn as
  | [] => rfl
  | a :: as => by simp only [argsExpr, argExpr_sicht h a, argsExpr_sicht h as]

theorem stmtBody_sicht {fT fn : UFn} (h : Sicht u fT fn) (s : UStmt) :
    stmtBody u fT s = stmtBody u fn s := by
  cases s <;> simp [stmtBody, h.2.1, sideExpr_sicht h, argsExpr_sicht h]

theorem endBody_sicht {fT fn : UFn} (h : Sicht u fT fn) (r : URet) :
    endBody u fT r = endBody u fn r := by
  cases r <;> simp [endBody, sideExpr_sicht h]

end Gabbro.Bruecke
