module
public import Grammatik.Parser.Elab.Export.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
public import Grammatik.Parser.Elab.UebersetzeAllg3.Transition
public import Grammatik.Parser.Elab.UebersetzeAllg3.Body
@[expose] public section


namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000


/-- The body: the statements of a function, then the trailing return, in the scope of its parameters,
    starting from the signature beginning (held locks plus consumed input marks). -/
def lowBody (u : UProg) (caller : Fin u.fns.length)
    (ss : List UStmt) (r : URet) :
    Except String (Endblock (declOf u) (verOf u caller) false
      (ctxOf u caller) (resOf u caller)) :=
  lowBodyF u caller (ctxOf u caller) (fnAt u caller) (ss.length + 1) (resOf u caller) ss r


/-- One whole function: contracts and body through the
    declaration. -/
def lowerFnPlain (u : UProg) (c : Fin u.fns.length) :
    Except String (EnsTy u c × RumpTy u c × ReqTy u c) :=
  match lowEnsList u (ctxOf u c) (resOf u c) (fnAt u c) none (fnAt u c).needs with
  | .error e => .error e
  | .ok r0 =>
  match lowEnsList u (ErgCtx (ctxOf u c) ((verOf u c).erg))
      (verOf u c).ende (fnAt u c) (fnAt u c).ergTy
      (fnAt u c).gives with
  | .error e => .error e
  | .ok e0 =>
    match lowBody u c (fnAt u c).body (fnAt u c).ret with
    | .error e => .error e
    | .ok b0 =>
      have e1 : EnsTy u c := by
        show Expr (declOf u)
          (ErgCtx ((declOf u).params c) ((declOf u).erg c))
          (vertragVon (declOf u) c).ende .bool
        rw [← ensCtx_eq u c]
        exact e0
      have b1 : RumpTy u c := by
        show Endblock (declOf u) (vertragVon (declOf u) c) false
          ((declOf u).params c)
          (Signatur.anfang (declOf u) ((declOf u).signatur c))
        rw [← ctxParams_eq u c, ← anfangRes_eq u c]
        exact b0
      have r1 : ReqTy u c := by
        show Expr (declOf u) ((declOf u).params c) (Signatur.anfang (declOf u) ((declOf u).signatur c)) .bool
        rw [← ctxParams_eq u c, ← anfangRes_eq u c]
        exact r0
      .ok (e1, b1, r1)

/-- One whole function. A function a transition declaration generates is lowered as
    the typed expansion of that declaration (`lowerTransitionAt`); a function of the
    generated name range that matches no declaration is refused, never lowered as an
    ordinary function. -/
def lowerFnAt (u : UProg) (c : Fin u.fns.length) :
    Except String (EnsTy u c × RumpTy u c × ReqTy u c) :=
  match transitionOfFn u c with
  | some (state, tr) => lowerTransitionAt u c state tr
  | none =>
    if (fnAt u c).name.startsWith "#transition#" then
      .error "generated transition function without declaration"
    else lowerFnPlain u c

/-- Every function lowers (the success check of `lowerAllg`;
    the values ride `lowerFnAt` directly). -/
def lowerEach (u : UProg) :
    List (Fin u.fns.length) → Except String Unit
  | [] => .ok ()
  | f :: fs =>
    match lowerFnAt u f with
    | .error e => .error e
    | .ok _ => lowerEach u fs

end Gabbro.Grammatik.Parser.UebersetzeAllg2
