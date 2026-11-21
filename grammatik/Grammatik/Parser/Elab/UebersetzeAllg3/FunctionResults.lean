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

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The lowered pair at an index known good. -/
theorem lowerAtPair_of_ok (u : UProg) (f : Fin u.fns.length) (hw : ∃ v, lowerFnAt u f = .ok v)
    {v : EnsTy u f × RumpTy u f × ReqTy u f} (hv : lowerFnAt u f = .ok v) :
    lowerAtPair u f hw = v := by
  unfold lowerAtPair
  split
  · rename_i v' hv'
    rw [hv] at hv'
    cases hv'
    rfl
  · rename_i e he
    rw [hv] at he
    cases he

/-- What the assembled program holds at a function of a successful lowering. -/
theorem lowerAllg_fields (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn)
    (h : lowerAllg u = .ok (P, fs)) (c : Fin u.fns.length) :
    ∃ v, lowerFnAt u c = .ok v ∧ P.ensures c = v.1 ∧ P.rumpf c = v.2.1 ∧
      ((fnAt u c).needs ≠ [] → P.requires c = v.2.2) := by
  unfold lowerAllg at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · obtain ⟨rfl, -⟩ := Gabbro.Grammatik.Parser.Measures.checkedProgram_eq h
        obtain ⟨v, hv⟩ := lowerEach_all_ok u (List.finRange u.fns.length) c (List.mem_finRange c)
          ‹lowerEach u (List.finRange u.fns.length) = .ok ()›
        refine ⟨v, hv, ?_, ?_, ?_⟩
        · exact congrArg Prod.fst (lowerAtPair_of_ok u c _ hv)
        · exact congrArg (fun p => p.2.1) (lowerAtPair_of_ok u c _ hv)
        · intro hne
          simp only [progOfFn, reqOf, hne, ↓reduceIte]
          exact congrArg (fun p => p.2.2) (lowerAtPair_of_ok u c _ hv)
      · cases h

/-- The assembled requires keeps the actual function result and the empty-clause rule. -/
theorem lowerAllg_requires (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn)
    (lowered : lowerAllg u = .ok (P, fs)) (f : Fin u.fns.length)
    {value : EnsTy u f × RumpTy u f × ReqTy u f}
    (functionLowered : lowerFnAt u f = .ok value) :
    P.requires f = if (fnAt u f).needs = [] then .tru else value.2.2 := by
  unfold lowerAllg at lowered
  split at lowered
  · cases lowered
  · split at lowered
    · cases lowered
    · split at lowered
      · obtain ⟨rfl, _⟩ := Gabbro.Grammatik.Parser.Measures.checkedProgram_eq lowered
        simp only [progOfFn, reqOf, lowerAtPair_of_ok u f _ functionLowered]
      · cases lowered

end Gabbro.Grammatik.Parser.UebersetzeAllg2
