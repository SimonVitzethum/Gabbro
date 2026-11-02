module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures
open Uebersetze UebersetzeAllg UebersetzeAllg2

/-- Clause collection preserves the one original expression exactly, including operator spelling. -/
theorem uMeasureClause_exact (alias : List (String × (Int × Int))) (clauses : List SKlausel)
    (source : SExpr) (measure : UMeasure)
    (written : clauses.filterMap (fun | .drops e => some e | _ => none) = [source])
    (collected : uMeasureClause alias clauses = .ok (some measure)) : measure.source = source := by
  unfold uMeasureClause at collected
  rw [written] at collected
  cases hs : uMeasureSource source with
  | error error => simp only [hs] at collected; cases collected
  | ok m =>
    simp only [hs] at collected
    cases hc : uMeasureCheck alias m with
    | error error => simp only [hc] at collected; cases collected
    | ok _ =>
      simp only [hc, Except.ok.injEq, Option.some.injEq] at collected
      subst measure
      exact uMeasureSource_exact source m hs

/-- A successful function export retains its clause and its precise scalar entry scope. -/
theorem elabUFunktion_measure (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (tabs : List UTab) (locks : List ULock)
    (globs : List UGlob) (heads : List UFnKopf) (sig : FnSig) (body : SAnw)
    (assumptions : List String) (whys : List UWhy) (sums : List USum) (devices : List String)
    (registers : List UReg) (states : List UZustand) (pointers : List String) (base : Nat)
    (specs : List (String × List String × SExpr)) (arrays : List (String × USide)) (fn : UFn)
    (lowered : elabUFunktion consts alias tabs locks globs heads sig body assumptions whys sums
      devices registers states pointers base specs arrays = .ok fn) :
    uMeasureClause alias sig.klauseln = .ok fn.decreases ∧
      fn.measureConstants = (if fn.decreases.isSome then consts else []) ∧
      fn.measureTypes = (if fn.decreases.isSome then alias else []) := by
  cases hh : elabKopf consts alias tabs locks globs whys sums sig devices pointers base with
  | error error => simp only [elabUFunktion, hh, reduceCtorEq] at lowered
  | ok pair =>
    rcases pair with ⟨head, writes⟩
    let ctx := {uCtxVon alias consts tabs locks globs head sig.name assumptions whys sums registers states specs arrays with
      zeiger := pointers, zeigerBasis := base}
    cases hb : elabFn ctx heads sig.klauseln body with
    | error error => simp only [elabUFunktion, hh, hb, reduceCtorEq] at lowered
    | ok parts =>
      rcases parts with ⟨gives, needs, statements, returned⟩
      cases hm : uMeasureClause alias sig.klauseln with
      | error error => simp only [elabUFunktion, hh, hb, hm, reduceCtorEq] at lowered
      | ok measure =>
        simp only [elabUFunktion, hh, hb, hm, Except.ok.injEq] at lowered
        subst fn
        exact ⟨hm, rfl, rfl⟩

/-- Connect the original clause to the typed exported tuple and its source denotation. -/
theorem lowerMeasures_denotes (u : UProg) (exported : Export u) (f : (declOf u).Fn)
    (alias : List (String × (Int × Int)))
    (clauses : List SKlausel) (source : SExpr) (measure : UMeasure)
    (written : clauses.filterMap (fun | .drops e => some e | _ => none) = [source])
    (collected : uMeasureClause alias clauses = .ok (some measure))
    (entry : (fnAt u f).decreases = some measure) :
    ∃ c : Component u f, exported.mass f = [c] ∧
      ∀ (initial state : World (declOf u)) (env : Env (declOf u) ((declOf u).params f)),
        SourceValue (fnAt u f) (fnAt u f).measureConstants env source
          (eval initial c.2.1 state env).n := by
  have provenance := exported.source f
  simp only [SourceTuple, entry] at provenance
  rw [uMeasureClause_exact alias clauses source measure written collected] at provenance
  exact provenance

end Gabbro.Grammatik.Parser.Measures
