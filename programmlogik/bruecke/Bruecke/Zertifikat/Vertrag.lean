module
public import Bruecke.Zertifikat.Programm
@[expose] public section

/-!
# A function's contract without its body

The lowering of a plain function computes its precondition (`needs`) and postcondition (`gives`)
before, and independently of, its body (`lowerFnPlain`). `requires_vertrag` and `ensures_vertrag` read
`P.requires g` and `P.ensures g` off the contract lowering alone, so the duty of a caller never needs a
callee's body: a change of one body leaves every other duty as it is.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The precondition of function `c` from its lowered `needs` (as in `lowerFnPlain`). -/
def reqVon (u : UProg) (c : Fin u.fns.length)
    (r0 : Expr (declOf u) (ctxOf u c) (resOf u c) .bool) : ReqTy u c := by
  show Expr (declOf u) ((declOf u).params c) (Signatur.anfang (declOf u) ((declOf u).signatur c)) .bool
  rw [← ctxParams_eq u c, ← anfangRes_eq u c]
  exact r0

/-- The postcondition of function `c` from its lowered `gives` (as in `lowerFnPlain`). -/
def ensVon (u : UProg) (c : Fin u.fns.length)
    (e0 : Expr (declOf u) (ErgCtx (ctxOf u c) ((verOf u c).erg)) (verOf u c).ende .bool) : EnsTy u c := by
  show Expr (declOf u) (ErgCtx ((declOf u).params c) ((declOf u).erg c)) (vertragVon (declOf u) c).ende .bool
  rw [← ensCtx_eq u c]
  exact e0

theorem vertrag_von {u : UProg} {c : Fin u.fns.length} {v : EnsTy u c × RumpTy u c × ReqTy u c}
    (hv : lowerFnAt u c = .ok v) (ht : transitionOfFn u c = none)
    (hname : (fnAt u c).name.startsWith "#transition#" = false)
    {r0 : Expr (declOf u) (ctxOf u c) (resOf u c) .bool}
    (hr : lowEnsList u (ctxOf u c) (resOf u c) (fnAt u c) none (fnAt u c).needs = .ok r0)
    {e0 : Expr (declOf u) (ErgCtx (ctxOf u c) ((verOf u c).erg)) (verOf u c).ende .bool}
    (he : lowEnsList u (ErgCtx (ctxOf u c) ((verOf u c).erg)) (verOf u c).ende (fnAt u c) (fnAt u c).ergTy
      (fnAt u c).gives = .ok e0) :
    v.1 = ensVon u c e0 ∧ v.2.2 = reqVon u c r0 := by
  unfold lowerFnAt at hv
  rw [ht] at hv
  simp only [hname, Bool.false_eq_true, if_false] at hv
  unfold lowerFnPlain at hv
  rw [hr, he] at hv
  cases hb : lowBody u c (fnAt u c).body (fnAt u c).ret with
  | error e => rw [hb] at hv; cases hv
  | ok b0 =>
    rw [hb] at hv
    dsimp only at hv
    injection hv with hv'
    subst hv'
    exact ⟨rfl, rfl⟩

theorem requires_vertrag {u : UProg} {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : lowerAllg u = .ok (P, fs)) (c : Fin u.fns.length) (ht : transitionOfFn u c = none)
    (hname : (fnAt u c).name.startsWith "#transition#" = false)
    {r0 : Expr (declOf u) (ctxOf u c) (resOf u c) .bool}
    (hr : lowEnsList u (ctxOf u c) (resOf u c) (fnAt u c) none (fnAt u c).needs = .ok r0)
    {e0 : Expr (declOf u) (ErgCtx (ctxOf u c) ((verOf u c).erg)) (verOf u c).ende .bool}
    (he : lowEnsList u (ErgCtx (ctxOf u c) ((verOf u c).erg)) (verOf u c).ende (fnAt u c) (fnAt u c).ergTy
      (fnAt u c).gives = .ok e0) :
    P.requires c = (if (fnAt u c).needs = [] then Expr.tru else reqVon u c r0) := by
  obtain ⟨v, hv, _, _, hreq⟩ := programm_von h c
  rw [hreq, (vertrag_von hv ht hname hr he).2]

theorem ensures_vertrag {u : UProg} {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : lowerAllg u = .ok (P, fs)) (c : Fin u.fns.length) (ht : transitionOfFn u c = none)
    (hname : (fnAt u c).name.startsWith "#transition#" = false)
    {r0 : Expr (declOf u) (ctxOf u c) (resOf u c) .bool}
    (hr : lowEnsList u (ctxOf u c) (resOf u c) (fnAt u c) none (fnAt u c).needs = .ok r0)
    {e0 : Expr (declOf u) (ErgCtx (ctxOf u c) ((verOf u c).erg)) (verOf u c).ende .bool}
    (he : lowEnsList u (ErgCtx (ctxOf u c) ((verOf u c).erg)) (verOf u c).ende (fnAt u c) (fnAt u c).ergTy
      (fnAt u c).gives = .ok e0) :
    P.ensures c = ensVon u c e0 := by
  obtain ⟨v, hv, hens, _⟩ := programm_von h c
  rw [hens, (vertrag_von hv ht hname hr he).1]

/-- **No atomic globals, decided on the elaborated program**: the Boolean test over `u.globs` gives the
    premise of `atomarA_id` for every global of `declOf u`. -/
theorem atomar_frei {u : UProg} (h : (u.globs.all fun x => !x.atomic) = true) :
    ∀ g : (declOf u).Glob, (declOf u).atomar g = false := by
  intro g
  have hg := List.all_eq_true.mp h _ (List.get_mem u.globs g)
  show (globAt u g).atomic = false
  simpa [globAt] using hg

end Gabbro.Bruecke
