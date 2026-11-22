module
public import Grammatik.Parser.Elab.UebersetzePipeline
@[expose] public section

/-!
# What the lowering answers, for every function and every form

`programm_von`: the program `lowerAllg u` answers has, at every function, the postcondition, body
and precondition of that function's lowering `lowerFnAt`. No form is special: this is read off the
definition of `lowerAllg` once.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

theorem lowerAtPair_von {u : UProg} (f : Fin u.fns.length) (h : ∃ v, lowerFnAt u f = .ok v)
    {v : EnsTy u f × RumpTy u f × ReqTy u f} (hv : lowerFnAt u f = .ok v) : lowerAtPair u f h = v := by
  unfold lowerAtPair
  split
  · rename_i v' hv'
    rw [hv] at hv'
    cases hv'
    rfl
  · rename_i e he
    rw [hv] at he
    cases he

/-- **The program of the lowering, function by function.** -/
theorem programm_von {u : UProg} {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : lowerAllg u = .ok (P, fs)) (f : Fin u.fns.length) :
    ∃ v, lowerFnAt u f = .ok v ∧ P.ensures f = v.1 ∧ P.rumpf f = v.2.1 ∧
      P.requires f = (if (fnAt u f).needs = [] then Expr.tru else v.2.2) := by
  unfold lowerAllg at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hall
      split at h
      · obtain ⟨rfl, -⟩ := Gabbro.Grammatik.Parser.Measures.checkedProgram_eq h
        obtain ⟨v, hv⟩ := lowerEach_all_ok u (List.finRange u.fns.length) f (List.mem_finRange f) hall
        refine ⟨v, hv, ?_, ?_, ?_⟩
        · show (lowerAtPair u f _).1 = v.1
          rw [lowerAtPair_von f _ hv]
        · show (lowerAtPair u f _).2.1 = v.2.1
          rw [lowerAtPair_von f _ hv]
        · show (if (fnAt u f).needs = [] then Expr.tru else (lowerAtPair u f _).2.2) = _
          rw [lowerAtPair_von f _ hv]
      · cases h

#print axioms programm_von

end Gabbro.Bruecke
