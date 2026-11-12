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
  cases hx : expandU items with
  | error error => simp only [hx, bind, Except.bind, reduceCtorEq] at restored
  | ok expanded =>
    simp only [hx, bind, Except.bind] at restored
    cases hc : OldSource.collect u.fns.length (EnsTy u) (OldSource.atFunction (OldSource.koepfeVon expanded.1) u raw) with
    | error error => simp only [hc, bind, Except.bind, reduceCtorEq] at restored
    | ok predicates =>
      simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at restored
      subst final
      have reachable (equality : DecidableEq (declOf u).Fn) (w : (declOf u).Fn) (n : Nat) (f : (declOf u).Fn) :
          @erreichB (declOf u) equality { raw with ensures := predicates } (List.finRange u.fns.length) w n f =
            @erreichB (declOf u) equality raw (List.finRange u.fns.length) w n f := by
        induction n generalizing f with
        | zero => rfl
        | succ n ih =>
          simp only [erreichB, erreichSchritt, ih, ruftB]
      have cycles (equality : DecidableEq (declOf u).Fn) (f g : (declOf u).Fn) :
          @zykS (declOf u) equality { raw with ensures := predicates } (List.finRange u.fns.length) f g =
            @zykS (declOf u) equality raw (List.finRange u.fns.length) f g := by
        unfold zykS zyklusMit reachB
        refine congr (congrArg Bool.and ?_) ?_
        · exact congr (congrArg Bool.and (reachable equality f _ g)) (reachable equality g _ f)
        · apply congrArg (List.any (List.finRange u.fns.length))
          funext h
          exact congrArg (fun b => @ruftB (declOf u) equality raw f h && b) (reachable equality h _ f)
      have unchanged : Measures.cycleLengths u { raw with ensures := predicates } exported.mass =
          Measures.cycleLengths u raw exported.mass := by
        unfold Measures.cycleLengths
        apply congrArg (List.all (List.finRange u.fns.length))
        funext f
        apply congrArg (List.all (List.finRange u.fns.length))
        funext g
        exact congrArg (fun b => !b || decide ((exported.mass f).length = (exported.mass g).length))
          (cycles _ f g)
      exact unchanged.trans lengths

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
