module

public import Stage0.Senke.Bild.Ruf.RootAdmission

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

/-- An actual load or buffered store at a body position advances the
    runner on the same answer while GX stays at its committed boundary.
    Every other thread, including roots still entering, retains its view. -/
theorem image_body_read_store [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))}
    {snapshots : Nat → Option Solo} {positions : Nat → MLage (declOf output.compiled.unit).mitRuhe}
    {committed : Mem} {i : Nat} {solo : Solo} {request : Op} {resume : Ans → Res T}
    {answer : Ans} {memory : imageTSO.St}
    (buffers : PrivateBuffers footprint before.ms.1) (length : body.length = before.ths.length)
    (related : MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState footprint before.ms).1, body⟩ state snapshots positions committed)
    (indices : ∀ j s, snapshots j = some s → (positions j).thr = j ∧ SoloFootprint footprint j s)
    (roots : ∀ j, body[j]? = before.ths[j]? ∨
      ∃ r, body[j]? = some none ∧ before.ths[j]? = some (some r) ∧
        ImageRootPhase output E history (before.ms.1.view j) j r state)
    (present : snapshots i = some solo) (covers : ImFuss solo) (blind : Blind solo.r)
    (ready : solo.r = .ask request resume)
    (ordinary : match request with | .rd .. | .wr .. => True | _ => False)
    (answered : imageTSO.ans before.ms i request answer memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, before.ths.set i (some (resume answer))⟩
    ProcessStep imageTSO actI before [] after ∧ ImageRuntimeMatches output E O history after state := by
  intro after
  have started : body[i]? = some (some (.ask request resume)) := ready ▸ related.zustand i solo present
  have actual : before.ths[i]? = some (some (.ask request resume)) := by
    rcases roots i with same | ⟨_, absent, _, _⟩
    · exact same.symm.trans started
    · rw [absent] at started
      cases started
  have kind : istSpeicherOp request = true := by
    cases request <;> first | rfl | cases ordinary
  have quiet : lbl i request answer = [] := by
    cases request <;> first | rfl | cases ordinary
  have otherViews : ∀ j, j ≠ i → memory.1.view j = before.ms.1.view j := by
    cases request with
    | rd width addr =>
      have same := answered.1.1
      cases same
      intro j _
      rfl
    | wr addr value =>
      rcases tso_store_updates_view answered.1 with ⟨_, same⟩ | ⟨_, _, stable⟩
      · cases same
        intro j _
        rfl
      · exact stable
    | cas | sys | fp => cases ordinary
  have step := ProcessStep.ask (M := imageTSO) (act := actI) actual rfl
    (special_speicherOp kind) answered rfl
  rw [quiet] at step
  obtain ⟨buffers', projected⟩ :=
    (indices i solo present).2.project_answer covers ready kind buffers answered.1
  let updated := body.set i (some (resume answer))
  have sc : SCSchritt L0 i ⟨projectSCState footprint before.ms, body⟩
      ⟨projectSCState footprint memory, updated⟩ := .ask started kind projected
  have relatedStep := sc_mSchritt sc (fun r atSlot => by
    change body[i]? = some (some r) at atSlot
    rw [related.zustand i solo present] at atSlot
    exact (Option.some.inj (Option.some.inj atSlot)) ▸ blind)
  obtain ⟨next, sameRead, sameWrite, advanced⟩ :=
    mtRel_schritt related present covers relatedStep
  refine ⟨step, footprint, updated, buffers', ?_, .inr ⟨setzeS snapshots i next, positions, committed, advanced, ?_⟩, ?_⟩
  · simpa only [updated, after, List.length_set] using length
  · intro j s known
    rcases setzeS_fall known with ⟨rfl, rfl⟩ | ⟨_, previous⟩
    · obtain ⟨sameThread, owned⟩ := indices i solo present
      exact ⟨sameThread, ⟨fun byte read => owned.read byte (sameRead ▸ read),
        fun byte write => owned.write byte (sameWrite ▸ write)⟩⟩
    · exact indices j s previous
  · intro j
    by_cases same : j = i
    · subst j
      left
      exact (List.getElem?_set_self (List.getElem?_eq_some_iff.mp started).1).trans
        (List.getElem?_set_self (List.getElem?_eq_some_iff.mp actual).1).symm
    · have bodySame : updated[j]? = body[j]? := List.getElem?_set_ne (Ne.symm same)
      have threadSame : after.ths[j]? = before.ths[j]? := List.getElem?_set_ne (Ne.symm same)
      rcases roots j with equal | ⟨r, pending, control, phase⟩
      · exact Or.inl (bodySame.trans (equal.trans threadSame.symm))
      · exact Or.inr ⟨r, bodySame.trans pending, threadSame.trans control, by
          change ImageRootPhase output E history (memory.1.view j) j r state
          rw [otherViews j same]
          exact phase⟩

end Gabbro.Stage0
