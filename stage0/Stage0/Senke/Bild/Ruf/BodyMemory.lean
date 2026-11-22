module

public import Stage0.Senke.Bild.Ruf.RootMemory
public import Stage0.Senke.Bild.Mehr.Ort.Footprint
public import Stage0.Senke.Bild.Mehr.Ort.CommitMemory
public import Stage0.Senke.Bild.Mehr.Ort.LockFootprint
public import Stage0.Senke.Bild.Ruf.ExpressionMemory
import Stage0.Senke.Bild.ImageAddress
import Lean.Elab.Tactic.Omega

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
    ImageRuntimeMatchesAt footprint output E O history ⟨memory, before.ths.set i (some control)⟩ state := by
  let updated := body.set i (some control)
  let after : Cfg imageTSO (Res T) := ⟨memory, before.ths.set i (some control)⟩
  have started := related.zustand i solo present
  have actual := body_slot_present roots started
  obtain ⟨next, sameRead, sameWrite, advanced⟩ := mtRel_schritt related present covers advance
  refine ⟨updated, buffers, ?_, .inr ⟨setzeS snapshots i next, positions, committed, advanced, ?_⟩, ?_⟩
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
    ProcessStep imageTSO actI before [] after ∧ ImageRuntimeMatchesAt footprint output E O history after state := by
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
    ProcessStep imageTSO actI before [] after ∧ ImageRuntimeMatchesAt footprint output E O history after state := by
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

/-- A silent flush preserves the IR projection, startup frames,
    admitted bodies, and ticket registry for the same GX state. -/
theorem image_body_flush [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {memory : imageTSO.St} {N : Nat} {tickets : _ → Senke.Faeden.Zustand N}
    {footprint : Nat → W → Prop}
    (matched : ImageRuntimeMatchesAt footprint output E O history before state)
    (placed : ∀ thread byte, footprint thread byte → imageStackFootprint output thread byte ∨
      output.image.Y.lo ≤ byte.toNat ∧ byte.toNat < output.image.Y.hi)
    (registry : Senke.Faeden.ImageTicketStates output.image.Y.withIdle before.ms.1.m state.m tickets)
    (synchronized : Senke.LaySync output.image.Y.withIdle)
    (order : output.image.Y.lo ≤ output.image.Y.hi) (bound : output.image.Y.sye ≤ 2 ^ 64)
    (allocated : before.ths.length ≤ output.starts.length + 1)
    (pastLoader : before.ths[0]? ≠ some (some Runner.Beweis.t4))
    (flushed : imageTSO.tau before.ms memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, before.ths⟩
    ProcessStep imageTSO actI before [] after ∧
      ImageRuntimeMatchesAt footprint output E O history after state ∧
      Senke.Faeden.ImageTicketStates output.image.Y.withIdle memory.1.m state.m tickets := by
  intro after
  obtain ⟨body, buffers, length, registered, roots⟩ := matched
  have belowLocks : ∀ thread byte, footprint thread byte → byte.toNat < output.image.Y.hi := by
    intro thread byte owned
    rcases placed thread byte owned with stack | ⟨_, world⟩
    · exact (imageStackFootprint_before_world stack).trans_le order
    · exact world
  obtain ⟨step, buffers', projection, registry'⟩ := registry.flush synchronized bound buffers
    (fun lock byte lockByte thread owned => Nat.not_le_of_lt (belowLocks thread byte owned)
      ((synchronized.1 lock).1.trans lockByte.1)) flushed
  have preserved := tso_flush_preserves_views (layout := L0) flushed (imageRootReads output) (by
    intro i store pending j different address readable written
    have privateByte := (buffers i store pending address written).1
    rcases readable with own | code
    · exact different (imageStackFootprint_owner placed own privateByte).symm
    · exact (Nat.not_le_of_lt code) (imageFootprint_after_code placed privateByte))
  refine ⟨step, ⟨body, buffers', length, ?_, ?_⟩, registry'⟩
  · change _ ∨ ∃ snapshots positions committed,
      MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
        ⟨(projectSCState footprint memory).1, body⟩ state snapshots positions committed ∧ _
    rw [projection]
    exact registered
  · intro thread
    rcases roots thread with same | ⟨control, absent, live, phase⟩
    · exact .inl same
    · have declared : thread ≤ output.starts.length := by
        have present := (List.getElem?_eq_some_iff.mp live).1
        omega
      have running : thread ≠ 0 ∨ control ≠ Runner.Beweis.t4 := by
        by_cases entry : thread = 0
        · subst thread
          exact .inr (fun loader => pastLoader (loader ▸ live))
        · exact .inl entry
      exact .inr ⟨control, absent, live, ImageRootPhase.transport phase running declared (fun address visible =>
        (preserved thread address visible).symm)⟩

/-- A floating answer is an internal IR observation of the issuing
    thread. It changes neither committed memory nor pending stores, and
    the sequential IR semantics can use the exact observed word. -/
theorem image_body_float [Kern] {before : Cfg imageTSO (Res T)}
    {memory : imageTSO.St} {thread : Nat} {kind : NativeFPOp} {a b : W}
    {answer : Ans} {resume : Ans → Res T}
    (ready : before.ths[thread]? = some (some (.ask (.fp kind a b) resume)))
    (answered : imageTSO.ans before.ms thread (.fp kind a b) answer memory) :
    let after : Cfg imageTSO (Res T) := ⟨memory, before.ths.set thread (some (resume answer))⟩
    ProcessStep imageTSO actI before [] after ∧ memory = before.ms ∧
      ∃ word, answer = some (word, 0) ∧ NativeFPEval kind a b word ∧
        ∀ {finish : T} {last : Mem},
          Run (resume answer) (before.ms.1.view thread) finish last →
          Run (.ask (.fp kind a b) resume) (before.ms.1.view thread) finish last := by
  intro after
  obtain ⟨unchanged, word, exactAnswer, valid⟩ := answered.1
  refine ⟨.ask ready rfl rfl answered rfl, unchanged, word, exactAnswer, valid, ?_⟩
  intro finish last later
  rw [exactAnswer] at later
  exact .fp valid later

/-- A whole private memory segment may run on several threads before
    the next source boundary. The generic IR memory semantics preserves
    the committed GX state and every thread's footprint throughout it. -/
theorem image_body_memory_segment [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)}
    {before after : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {snapshots : Nat → Option Solo}
    {positions : Nat → MLage (declOf output.compiled.unit).mitRuhe} {committed : Mem} {count : Nat}
    (buffers : PrivateBuffers footprint before.ms.1)
    (related : MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState footprint before.ms).1, before.ths⟩ state snapshots positions committed)
    (indices : ∀ i s, snapshots i = some s → (positions i).thr = i ∧ SoloFootprint footprint i s)
    (blind : AlleBlind before.ths)
    (classify : ∀ {c : Cfg imageTSO (Res T)} {steps},
      ProcessPrefix imageTSO actI before [] steps c →
      ∀ {i : Nat} {request : Op} {resume : Ans → Res T} {response : Ans} {memory : (TSO L0).St},
        c.ths[i]? = some (some (.ask request resume)) → request.special = false → lbl i request response = [] →
        (TSO L0).ans c.ms i request response memory → ProjectedRequest footprint i request)
    (access : ∀ {first last i},
      SCErreichbar L0 ⟨projectSCState footprint before.ms, before.ths⟩ first → SCSchritt L0 i first last →
      ∀ {s request resume}, snapshots i = some s → first.ths[i]? = some (some (.ask request resume)) →
        (∀ byte, fussOp request byte → s.F byte) ∧
        (schreibtOp request = true → ∀ byte, fussOp request byte → s.Wr byte))
    (segment : ProcessPrefix imageTSO actI before [] count after) :
    PrivateBuffers footprint after.ms.1 ∧ AlleBlind after.ths ∧
    ∃ updated : Nat → Option Solo,
      MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
        ⟨(projectSCState footprint after.ms).1, after.ths⟩ state updated positions committed ∧
      ∀ i s, updated i = some s → (positions i).thr = i ∧ SoloFootprint footprint i s := by
  obtain ⟨pending, projected⟩ := image_memory_prefix_projects segment buffers classify
  obtain ⟨updated, matched, stable, sameFootprints⟩ := sc_private_runs_refine related blind access projected
  refine ⟨pending, stable, updated, matched, ?_⟩
  intro i s known
  obtain ⟨first, present, reads, writes⟩ := sameFootprints i s known
  obtain ⟨thread, owned⟩ := indices i first present
  exact ⟨thread, ⟨fun byte read => owned.read byte (reads ▸ read),
    fun byte write => owned.write byte (writes ▸ write)⟩⟩

private theorem privateTrace_foreign {D : Deklaration} {before after : Lauf D}
    (trace : PrivateSourceTrace before after) : imageSourceForeignEvents after = imageSourceForeignEvents before := by
  obtain ⟨suffix, rfl, quiet⟩ := trace
  have projected : imageSourceForeignEvents suffix = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro step member
    cases event : step.ereignis with
    | fremd foreign =>
      cases foreign with
      | inl called => exact (quiet step member called event).elim
      | inr _ => rfl
    | nimmt | gibt | zugriff | gzugriff => rfl
  unfold imageSourceForeignEvents at projected ⊢
  rw [List.filterMap_append, projected, List.append_nil]

/-- A completed segment of a registered body advances the common GX
    machine. Its next phase is anchored in the same actual IR endpoint
    while every other body keeps its current phase. -/
theorem image_body_publish [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {after : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {footprint : Nat → W → Prop} {snapshots : Nat → Option Solo}
    {positions : Nat → MLage (declOf output.compiled.unit).mitRuhe} {committed : Mem}
    {body : List (Option (Res T))}
    {thread : Nat} {snapshot : Solo} {pc : W}
    {carriers : (declOf output.compiled.unit).mitRuhe.Tab ⊕ (declOf output.compiled.unit).mitRuhe.Glob → Prop}
    {Γ : Ctx} {Λ : List (Grammatik.Res (declOf output.compiled.unit).mitRuhe)}
    {rest : Endblock (declOf output.compiled.unit).mitRuhe
      (vertragVon _ (positions thread).B.f) (positions thread).l Γ Λ}
    {world : World (declOf output.compiled.unit).mitRuhe} {env : Env _ Γ}
    (buffers : PrivateBuffers footprint after.ms.1)
    (length : body.length = after.ths.length)
    (slots : ImageSlotsMatch output E O history after state)
    (foreign : ImageForeignTrace output history state)
    (matched : MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState footprint after.ms).1, body⟩ state snapshots positions committed)
    (roots : ∀ j, body[j]? = after.ths[j]? ∨
      ∃ r, body[j]? = some none ∧ after.ths[j]? = some (some r) ∧
        ImageRootPhase output E history (after.ms.1.view j) j r state)
    (pastLoader : after.ths[0]? ≠ some (some Runner.Beweis.t4))
    (indices : ∀ i s, snapshots i = some s → (positions i).thr = i ∧ SoloFootprint footprint i s)
    (registered : snapshots thread = some snapshot)
    (quiet : let x := positions thread
      Segment x.B.O x.B.passes x.B.R x.Agl x.Cg carriers x.eb x.σ x.ρ rest world env)
    (control : snapshot.r = .next ⟨pc, (positions thread).B.fp⟩)
    (boundary : let x := positions thread
      x.B.RandIR rest pc snapshot.m world env)
    (agree : let x := positions thread
      OrtGleich carriers x.σ (state.m.speicher.welt x.σ.spur))
    (free : FreiA (positions thread).Agl state.m (positions thread).thr)
    (inside : Senke.LayIn output.image.Y.withIdle) (separated : Senke.LayDis output.image.Y.withIdle)
    (covers : ∀ byte, carrierFootprint output.image.Y.withIdle carriers byte → snapshot.F byte)
    (permissions : (positions thread).mb.rd = committed.rd ∧ (positions thread).mb.wr = committed.wr) :
    ∃ next, ImageReach output E O state next ∧ ImageSlotsMatch output E O history after next ∧
      ImageForeignTrace output history next ∧ ImageRuntimeMatchesAt footprint output E O history after next ∧
      imageSourceForeignEvents next.m.lauf = imageSourceForeignEvents state.m.lauf ∧
      ∀ issuer, offen (next.m.faeden issuer).spur = offen (state.m.faeden issuer).spur := by
  obtain ⟨machine, _, next, reaches, atBody, _, _, otherHeads, holdings, trace, _, _, threadEq, related⟩ :=
    matched.commit_world registered (shared := GeteiltV (D := declOf output.compiled.unit) E.P E.ws)
      quiet control boundary agree free inside separated covers permissions
  let published := { state with m := machine }
  have retired (i : Nat) (inactive : after.ths[i]? = some none) :
      published.m.faeden i = state.m.faeden i := by
    apply otherHeads i
    intro same
    have own := same.trans (indices thread snapshot registered).1
    subst i
    rw [body_slot_present roots atBody] at inactive
    cases inactive
  have sameTrace := privateTrace_foreign trace
  refine ⟨published, reaches, slots.follow_silent (.nil after) reaches rfl retired, ?_,
    ⟨body, buffers, length, .inr ⟨snapshots, _, _, related, ?_⟩, ?_⟩, sameTrace, holdings⟩
  · unfold ImageForeignTrace at foreign ⊢
    change ImageForeignTraceAlignment output history (imageSourceForeignEvents machine.lauf)
    rw [sameTrace]
    exact foreign
  · intro i s found
    obtain ⟨identity, owned⟩ := indices i s found
    refine ⟨?_, owned⟩
    by_cases current : i = thread
    · subst i
      simpa only [ite_true] using threadEq.trans identity
    · simpa only [ite_eq_right current] using identity
  · intro i
    rcases roots i with same | ⟨residual, absent, live, root⟩
    · exact .inl same
    · have another : i ≠ thread := by
        intro same
        subst i
        rw [absent] at atBody
        cases atBody
      have installed : i ≠ 0 ∨ residual ≠ Runner.Beweis.t4 := by
        by_cases entry : i = 0
        · subst i
          exact .inr (fun loader => pastLoader (loader ▸ live))
        · exact .inl entry
      refine .inr ⟨residual, absent, live, ?_⟩
      simpa only [List.append_nil] using root.advance_source (extension := []) installed
        (otherHeads i (fun same => another (same.trans (indices thread snapshot registered).1)))

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
