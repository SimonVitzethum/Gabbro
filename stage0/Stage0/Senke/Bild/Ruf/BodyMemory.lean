module

public import Stage0.Senke.Bild.Ruf.RootAdmission
public import Stage0.Senke.Bild.Mehr.Ort.Footprint

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

private theorem body_slot_present [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {body : List (Option (Res T))} {i : Nat} {control : Res T}
    (roots : ∀ j, body[j]? = before.ths[j]? ∨
      ∃ r, body[j]? = some none ∧ before.ths[j]? = some (some r) ∧
        ImageRootPhase output E history (before.ms.1.view j) j r state)
    (began : body[i]? = some (some control)) : before.ths[i]? = some (some control) := by
  rcases roots i with same | ⟨_, absent, _, _⟩
  · exact same.symm.trans began
  · rw [absent] at began
    cases began

/-- Lift one already projected, private request transition at a body slot
    into the whole image, including any roots still being started. -/
private theorem image_body_local_change [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))}
    {snapshots : Nat → Option Solo} {positions : Nat → MLage (declOf output.compiled.unit).mitRuhe}
    {committed : Mem} {i : Nat} {solo : Solo} {control : Res T} {memory : imageTSO.St}
    (length : body.length = before.ths.length)
    (related : MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState footprint before.ms).1, body⟩ state snapshots positions committed)
    (indices : ∀ j s, snapshots j = some s → (positions j).thr = j ∧ SoloFootprint footprint j s)
    (roots : ∀ j, body[j]? = before.ths[j]? ∨
      ∃ r, body[j]? = some none ∧ before.ths[j]? = some (some r) ∧
        ImageRootPhase output E history (before.ms.1.view j) j r state)
    (present : snapshots i = some solo) (covers : ImFuss solo)
    (buffers : PrivateBuffers footprint memory.1)
    (otherViews : ∀ j, j ≠ i → memory.1.view j = before.ms.1.view j)
    (advance : MSchritt i ⟨(projectSCState footprint before.ms).1, body⟩
      ⟨(projectSCState footprint memory).1, body.set i (some control)⟩) :
    ImageRuntimeMatches output E O history ⟨memory, before.ths.set i (some control)⟩ state := by
  let updated := body.set i (some control)
  let after : Cfg imageTSO (Res T) := ⟨memory, before.ths.set i (some control)⟩
  have started := related.zustand i solo present
  have actual := body_slot_present roots started
  obtain ⟨next, sameRead, sameWrite, advanced⟩ := mtRel_schritt related present covers advance
  refine ⟨footprint, updated, buffers, ?_, .inr ⟨setzeS snapshots i next, positions, committed, advanced, ?_⟩, ?_⟩
  · simpa only [updated, List.length_set] using length
  · intro j s known
    rcases setzeS_fall known with ⟨rfl, rfl⟩ | ⟨_, previous⟩
    · obtain ⟨sameThread, owned⟩ := indices j solo present
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
      rcases roots j with equal | ⟨r, pending, running, phase⟩
      · exact Or.inl (bodySame.trans (equal.trans threadSame.symm))
      · exact Or.inr ⟨r, bodySame.trans pending, threadSame.trans running, by
          change ImageRootPhase output E history (memory.1.view j) j r state
          rw [otherViews j same]
          exact phase⟩

/-- Starting an instruction takes the actual thread from its pointer to
    the runner's opcode read without advancing the committed GX state. -/
theorem image_body_begin_instruction [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {body : List (Option (Res T))}
    {snapshots : Nat → Option Solo} {positions : Nat → MLage (declOf output.compiled.unit).mitRuhe}
    {committed : Mem} {i : Nat} {solo : Solo} {pointer : T}
    (buffers : PrivateBuffers footprint before.ms.1) (length : body.length = before.ths.length)
    (related : MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState footprint before.ms).1, body⟩ state snapshots positions committed)
    (indices : ∀ j s, snapshots j = some s → (positions j).thr = j ∧ SoloFootprint footprint j s)
    (roots : ∀ j, body[j]? = before.ths[j]? ∨
      ∃ r, body[j]? = some none ∧ before.ths[j]? = some (some r) ∧
        ImageRootPhase output E history (before.ms.1.view j) j r state)
    (present : snapshots i = some solo) (running : solo.r = .next pointer) :
    let after : Cfg imageTSO (Res T) := ⟨before.ms, before.ths.set i (some (IR.step pointer))⟩
    ProcessStep imageTSO actI before [] after ∧ ImageRuntimeMatches output E O history after state := by
  intro after
  have started : body[i]? = some (some (.next pointer)) := running ▸ related.zustand i solo present
  have covers : ImFuss solo := by
    intro request resume asks
    rw [running] at asks
    cases asks
  exact ⟨.priv (body_slot_present roots started) rfl,
    image_body_local_change length related indices roots present covers buffers (fun _ _ => rfl) (.priv started)⟩

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
  have actual := body_slot_present roots started
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
  exact ⟨step, image_body_local_change length related indices roots present covers buffers' otherViews relatedStep⟩

/-- Once every live slot has a body relation, an actual buffer drain
    preserves all body states and the exact committed GX world. -/
theorem image_body_flush [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {snapshots : Nat → Option Solo}
    {positions : Nat → MLage (declOf output.compiled.unit).mitRuhe} {committed : Mem} {memory : imageTSO.St}
    (buffers : PrivateBuffers footprint before.ms.1)
    (related : MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState footprint before.ms).1, before.ths⟩ state snapshots positions committed)
    (indices : ∀ i s, snapshots i = some s → (positions i).thr = i ∧ SoloFootprint footprint i s)
    (flushed : imageTSO.tau before.ms memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, before.ths⟩
    ProcessStep imageTSO actI before [] after ∧ ImageRuntimeMatches output E O history after state := by
  have same := projectSCState_flush (layout := L0) flushed footprint
    (fun i store pending byte hit => (buffers i store pending byte hit).1) buffers.disjoint
  have stable : MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState footprint memory).1, before.ths⟩ state snapshots positions committed := by
    rw [same]
    exact related
  exact ⟨.tau flushed, footprint, before.ths, buffers.flush flushed, rfl,
    .inr ⟨snapshots, positions, committed, stable, indices⟩, fun _ => .inl rfl⟩

/-- The current carrier ownership can change at a lock boundary without
    modifying the runner or the committed GX memory. Each executing
    segment must retain access to its remaining reads and writes. -/
theorem image_body_reassign_region [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {machine : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {before after : Nat → W → Prop} {body : List (Option (Res T))}
    {snapshots : Nat → Option Solo} {positions : Nat → MLage (declOf output.compiled.unit).mitRuhe}
    {committed : Mem}
    (length : body.length = machine.ths.length)
    (old : PrivateBuffers before machine.ms.1) (new : PrivateBuffers after machine.ms.1)
    (related : MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState before machine.ms).1, body⟩ state snapshots positions committed)
    (indices : ∀ i s, snapshots i = some s → (positions i).thr = i ∧ SoloFootprint after i s)
    (roots : ∀ i, body[i]? = machine.ths[i]? ∨
      ∃ r, body[i]? = some none ∧ machine.ths[i]? = some (some r) ∧
        ImageRootPhase output E history (machine.ms.1.view i) i r state) :
    ImageRuntimeMatches output E O history machine state := by
  refine ⟨after, body, new, length, .inr ⟨snapshots, positions, committed, ?_, indices⟩, roots⟩
  rw [projectSCState_reassign old new]
  exact related

end Gabbro.Stage0
