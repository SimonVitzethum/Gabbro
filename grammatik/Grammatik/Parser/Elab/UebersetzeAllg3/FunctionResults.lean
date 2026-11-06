module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Facts selecting the ordinary dispatcher with empty actual contracts. -/
structure PlainFunctionHeader (unit : UProg) (f : Fin unit.fns.length) : Prop where
  transition : transitionOfFn unit f = none
  ordinary : (fnAt unit f).name.startsWith "#transition#" = false
  requires : (fnAt unit f).needs = []
  ensures : (fnAt unit f).gives = []

abbrev PlainFunctionBody (unit : UProg) (f : Fin unit.fns.length) :=
  Endblock (declOf unit) (verOf unit f) false (ctxOf unit f) (resOf unit f)

/-- Compose the actual body result through the unchanged function dispatcher. -/
def lowerFnAt_from_body {unit : UProg} {f : Fin unit.fns.length}
    (header : PlainFunctionHeader unit f)
    (body : { actual : PlainFunctionBody unit f //
      lowBody unit f (fnAt unit f).body (fnAt unit f).ret = .ok actual }) :
    { actual : EnsTy unit f × RumpTy unit f × ReqTy unit f //
      lowerFnAt unit f = .ok actual } := by
  let ensures : EnsTy unit f := by
    show Expr (declOf unit) (ErgCtx ((declOf unit).params f) ((declOf unit).erg f))
      (vertragVon (declOf unit) f).ende .bool
    rw [← ensCtx_eq unit f]
    exact .tru
  let lowered : RumpTy unit f := by
    show Endblock (declOf unit) (vertragVon (declOf unit) f) false
      ((declOf unit).params f) (Signatur.anfang (declOf unit) ((declOf unit).signatur f))
    rw [← ctxParams_eq unit f, ← anfangRes_eq unit f]
    exact body.val
  let requires : ReqTy unit f := by
    show Expr (declOf unit) ((declOf unit).params f)
      (Signatur.anfang (declOf unit) ((declOf unit).signatur f)) .bool
    rw [← ctxParams_eq unit f, ← anfangRes_eq unit f]
    exact .tru
  refine ⟨(ensures, lowered, requires), ?_⟩
  simp only [lowerFnAt, header.transition, header.ordinary, Bool.false_eq_true,
    reduceIte, lowerFnPlain, header.requires, header.ensures, lowEnsList, body.property]
  rfl

/-- Preserve the body's actual first error through the same dispatcher. -/
theorem lowerFnAt_error_from_body {unit : UProg} {f : Fin unit.fns.length} {error : String}
    (header : PlainFunctionHeader unit f)
    (body : lowBody unit f (fnAt unit f).body (fnAt unit f).ret = .error error) :
    lowerFnAt unit f = .error error := by
  simp only [lowerFnAt, header.transition, header.ordinary, Bool.false_eq_true,
    reduceIte, lowerFnPlain, header.requires, header.ensures, lowEnsList, body]

end Gabbro.Grammatik.Parser.UebersetzeAllg
