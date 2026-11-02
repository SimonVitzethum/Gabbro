module
public import Stage0.Senke.Ausdruck.Old.Source
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Pipeline
@[expose] public section

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Old-state postcondition restoration leaves all bodies and therefore all cycle edges intact. -/
theorem restore_measure_lengths (items : List SItemTief) (u : UProg)
    (raw final : Programm (declOf u)) (exported : Measures.Export u)
    (restored : OldSource.restore items u raw = .ok final)
    (lengths : Measures.cycleLengths u raw exported.mass = true) :
    Measures.cycleLengths u final exported.mass = true := by
  unfold OldSource.restore at restored
  cases hc : OldSource.collect u.fns.length (EnsTy u) (OldSource.atFunction items u raw) with
  | error error => simp only [hc, bind, Except.bind, reduceCtorEq] at restored
  | ok predicates =>
    simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at restored
    subst final
    exact lengths

/-- The same source measure remains valid after the existing old-state restoration step. -/
theorem compiled_measure_lengths (items : List SItemTief) (u : UProg)
    (final : Programm (declOf u)) (exported : Measures.Export u)
    (origin : Measures.lowerMeasures u = .ok exported)
    (lowered : ∃ raw fs, lowerAllg u = .ok (raw, fs) ∧ OldSource.restore items u raw = .ok final) :
    Measures.cycleLengths u final exported.mass = true := by
  obtain ⟨raw, fs, lowered, restored⟩ := lowered
  obtain ⟨other, sameOrigin, lengths⟩ := Measures.lowerAllg_measures u raw fs lowered
  have same : other = exported := Except.ok.inj (sameOrigin.symm.trans origin)
  subst other
  exact restore_measure_lengths items u raw final exported restored lengths

end Gabbro.Stage0.Frontend
