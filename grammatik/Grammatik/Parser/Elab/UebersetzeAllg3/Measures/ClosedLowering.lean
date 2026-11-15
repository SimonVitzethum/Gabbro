module

public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

-- The measure gate retains its actual export. Absent clauses make its length
-- comparisons true independently of bodies, so no reachability reduction is needed.
theorem check_measure_gate (u : UProg) (exported : Measures.Export u)
    (made : Measures.lowerMeasures u = .ok exported)
    (absent : ∀ fn ∈ u.fns, fn.decreases = none) (P : Programm (declOf u)) :
    Measures.checkedProgram u P = .ok (P, List.finRange u.fns.length) := by
  have cycles : Measures.cycleLengths u P exported.mass = true := by
    unfold Measures.cycleLengths
    apply List.all_eq_true.mpr
    intro f _
    apply List.all_eq_true.mpr
    intro g _
    have empty (i : (declOf u).Fn) : exported.mass i = [] :=
      Measures.lowerMeasures_absent u exported i
        (absent (fnAt u i) (List.get_mem u.fns i))
    rw [empty f, empty g]
    change (!zykS P (List.finRange u.fns.length) f g || true) = true
    exact Bool.or_true _
  -- Pin the whole tuple at the declaration's actual function type before
  -- reducing the dependent export match. No rewrite crosses its binder.
  let accepted : Programm (declOf u) × List (declOf u).Fn :=
    (P, List.finRange u.fns.length)
  change @Eq (Except String (Programm (declOf u) × List (declOf u).Fn))
    (match Measures.lowerMeasures u with
    | .error error => .error error
    | .ok actual =>
      if Measures.cycleLengths u P actual.mass then .ok accepted
      else .error "differing decreases tuple lengths in a recursion cycle") (.ok accepted)
  rw [made]
  dsimp only
  exact if_pos cycles

/-- Absent source clauses export an actual empty measure family without inspecting bodies. -/
theorem lowerMeasures_without_clauses (u : UProg)
    (absent : ∀ fn ∈ u.fns, fn.decreases = none) :
    ∃ exported, Measures.lowerMeasures u = .ok exported := by
  let entries : (f : (declOf u).Fn) → Measures.At u f := fun f =>
    ⟨[], by simp only [Measures.SourceTuple, absent (fnAt u f) (List.get_mem u.fns f)]⟩
  have each (f : (declOf u).Fn) : Measures.lowerAt u f = .ok (entries f) := by
    unfold Measures.lowerAt
    split
    · rfl
    · rename_i source found
      cases found.symm.trans (absent (fnAt u f) (List.get_mem u.fns f))
  have collected :
      Measures.collect u.fns.length (Measures.At u) (Measures.lowerAt u) = .ok entries := by
    exact (Measures.collect_eq_sammle _ _ _).trans (sammle_ok _ _ _ entries each)
  let assemble (values : (f : (declOf u).Fn) → Measures.At u f) : Measures.Export u :=
    ⟨fun f => (values f).tuple, fun f => (values f).source⟩
  refine ⟨assemble entries, ?_⟩
  exact congrArg (fun result : Except String ((f : (declOf u).Fn) → Measures.At u f) =>
    result.bind (fun values => Except.ok (assemble values))) collected

/-- Successful invariant, function and contract checks, together with an actual
    empty-clause measure export, close the unchanged canonical lowering endpoint. -/
theorem closed_lowering (u : UProg)
    (invariants : lowerInvs u (List.finRange u.invs.length) = .ok ())
    (functions : lowerEach u (List.finRange u.fns.length) = .ok ())
    (contracts : contractGate u = true)
    (absent : ∀ fn ∈ u.fns, fn.decreases = none) :
    (lowerAllg u).toOption.isSome = true := by
  obtain ⟨exported, made⟩ := lowerMeasures_without_clauses u absent
  unfold lowerAllg
  split
  · rename_i error rejected
    cases rejected.symm.trans invariants
  · split
    · rename_i error rejected
      cases rejected.symm.trans functions
    · simp only [dif_pos contracts, check_measure_gate u exported made absent,
        Except.toOption, Option.isSome_some]

end Gabbro.Grammatik.Parser.Uebersetze
