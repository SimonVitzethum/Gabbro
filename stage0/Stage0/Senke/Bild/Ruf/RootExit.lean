module

public import Stage0.Senke.Bild.Mehr.ImageTransition

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner Runner.IR Runner.Beweis Runner.Mach

/-- The actual thread exit retires one allocated slot. A completed call
    keeps its finished source head, and a declared non-returning call
    keeps the exact issuing head and request. -/
theorem ImageSlotsMatch.retire [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {i : Nat} {req : Req} {resume : Ans → Res T}
    (slots : ImageSlotsMatch output E O history before state)
    (reached : ImageReach output E O (imageSourceStart E) state)
    (ready : before.ths[i]? = some (some (.ask (.sys req) resume)))
    (number : req.nr.toNat = NR_EXIT)
    (matching : FertigG state.m i ∨ ImageNeverRequest output O state i req) :
    let after : Cfg imageTSO (Res T) := ⟨before.ms, before.ths.set i none⟩
    ProcessStep imageTSO actI before [(i, req, none)] after ∧
      ImageSlotsMatch output E O (history ++ [(i, req, none)]) after state := by
  intro after
  refine ⟨.exit ready rfl number, ?_, ?_⟩
  · intro j
    simpa only [after, List.length_set] using slots.1 j
  · intro j retired
    by_cases same : j = i
    · subst j
      rcases matching with finished | declared
      · exact Or.inl finished
      · refine Or.inr ⟨state, req, history.filter (fun event => event.1 == i),
          reached, .start, rfl, declared, number, ?_⟩
        simp only [List.filter_append, List.filter_cons, beq_self_eq_true, ite_true, List.filter_nil]
    · have unchanged : before.ths[j]? = some none := by
        simpa only [after, List.getElem?_set_ne (Ne.symm same)] using retired
      obtain finished | ⟨atExit, call, earlier, fromStart, since, sameHead, matched, kind, last⟩ :=
        slots.2 j unchanged
      · exact Or.inl finished
      · refine Or.inr ⟨atExit, call, earlier, fromStart, since, sameHead, matched, kind, ?_⟩
        simp only [List.filter_append, List.filter_cons, beq_eq_false_iff_ne.mpr (Ne.symm same),
          Bool.false_eq_true, ite_false, List.filter_nil, List.append_nil, last]

/-- A real thread exit leaves the previously matched external call
    history intact. The exit is already accounted for by the slot proof. -/
theorem ImageForeignTrace.retire {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {history : List Ev}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {i : Nat} {req : Req}
    (matched : ImageForeignTrace output history state) (exit : req.nr.toNat = NR_EXIT) :
    ImageForeignTrace output (history ++ [(i, req, none)]) state := by
  have internal : imageExternalEvent (i, req, none) = false := by
    simp only [imageExternalEvent, exit, true_or, or_true, decide_true, Bool.not_true]
  unfold ImageForeignTrace at matched ⊢
  simpa only [List.filter_append, List.filter_cons, internal, Bool.false_eq_true, ite_false,
    List.filter_nil, List.append_nil] using matched

/-- A reached hardware failure explains the real process exit with its
    exact request and status. All prior microsteps are silent. -/
theorem image_hardware_exit [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {O : Orakel (declOf output.compiled.unit)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {history : List Ev}
    {before armed : Cfg imageTSO (Res T)} {steps i : Nat} {req : Req} {resume : Ans → Res T}
    {cause : Hardware (declOf output.compiled.unit).mitRuhe}
    (silent : ProcessPrefix imageTSO actI before [] steps armed)
    (ready : armed.ths[i]? = some (some (.ask (.sys req) resume)))
    (number : req.nr.toNat = NR_EXIT_GROUP) (status : req.a1 = BitVec.ofNat 64 (hwCode cause))
    (alive : state.lebt i = true) (matched : ImageHardwareCause O.mitRuhe output.image.passes state.m i cause) :
    Tr imageTSO actI before [(i, req, none)] (.exit req.a1) (steps + 1) ∧
      ImageStopMatches output O state history [(i, req, none)] (.exit req.a1) := by
  have stop : Tr imageTSO actI armed [(i, req, none)] (.exit req.a1) 1 := .exitGroup ready rfl number
  exact ⟨by simpa only [List.nil_append, Nat.add_comm] using silent.prepend stop,
    ⟨i, req, rfl, number, rfl, .inr (.inr (.inl ⟨alive, cause, matched, status⟩))⟩⟩

end Gabbro.Stage0
