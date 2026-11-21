module

public import Stage0.Senke.Bild.Mehr.Goal
public import Stage0.Senke.Bild.Mehr.BootClone
public import Stage0.Senke.Images.GateAnswers
public import Runner.IR.Futex

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- The runner uses the TSO memory model for its own operations. At the
    external boundary its answer and memory effect are those of the host
    relation. Clone only allocates a thread slot or reports a refusal. -/
def imageTSO [Kern] : MemSys where
  St := (TSO L0).St
  ans before thread request answer after :=
    (TSO L0).ans before thread request answer after ∧
      match request with
      | .sys call =>
        if call = cloneReq then
          after = before ∧ ∃ id extra, answer = some (id, extra) ∧ id ≠ 0
        else
          Kern.ans call (before.1.view thread) answer (after.1.view thread) ∧ after.1.buf = before.1.buf
      | _ => True
  tau := (TSO L0).tau

theorem imageTSO_fixed [Kern] : Fixed imageTSO L0 := by
  intro memory thread row answer after valid step
  exact tso_fixed L0 memory thread row answer after valid step.1

/-- The host gives futex completions their existing WAIT/WAKE meaning
    and does not write the image while completing a futex request. -/
structure ImageFutexAnswers [Kern] : Prop where
  protocol : FutexOK (fun _ _ before after => after = before)
  unchanged : ∀ base mode value answer before after,
    (mode = 128 ∨ mode = 129) →
    Kern.ans (futexReq base mode value) before answer after →
    after = before ∧ answer.isSome = true

/-- The external loader has mapped the exact emitted image, and the x86
    process is at the corresponding real loader read. -/
structure MappedImage [Kern] (output : Emitted src reserve options)
    (machine : Cfg imageTSO Runner.X86.X) : Prop where
  bytes : BytesAt machine.ms.1.m Runner.Prog.IMG output.bytes
  emptyBuffers : ∀ i, machine.ms.1.buf i = []
  loader : Rel L0 (M := imageTSO) ⟨machine.ms, [some t4]⟩ machine
  runnerFile : FileInv machine.ms.1.m

def imageAccumulatorItems (output : Emitted src reserve options) : List SItemTief :=
  (uMembers (pre108 output.compiled.source.prepared.elaborierbar)).filter fun item =>
    match item with
    | .accT .. => true
    | _ => false

/-- An accumulator descriptor elaborates the actual selected declaration
    with its generated cells, locks and functions. -/
def ImageAccumulator (output : Emitted src reserve options) (item : SItemTief)
    (acc : Kernzelle.AccumulatorDecl (declOf output.compiled.unit)) : Prop :=
  let unit := output.compiled.unit
  let scopes := output.compiled.source.scopes
  (∃ cells locks, uAkkuDecl scopes.values scopes.types item cells locks
    acc.kernAbfrage acc.aktualisiere acc.falte = .ok acc) ∧
  (∀ i, (unit.globs.get (acc.zellen i)).name = acc.name ++ "#zelle" ++ toString i.val) ∧
  (∀ i, (unit.locks.get (acc.sperren i)).name = acc.name ++ "#sperre" ++ toString i.val) ∧
  (fnAt unit acc.kernAbfrage).name = acc.name ++ "#query" ∧
  (fnAt unit acc.aktualisiere).name = acc.name ++ "#aktualisiere" ∧
  (fnAt unit acc.falte).name = acc.name ++ "#falte"

/-- The source's canonical bodies and initial declarations used by both
    the compiler and the goal theorem are the same. -/
structure ImageModelUnit (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) : Prop where
  program : E.P = output.compiled.program
  locks : E.S = Gabbro.Grammatik.Parser.Cover.Differenz.sperrFamilie output.compiled.unit
  lockSources : HEq E.lockFormulas (Gabbro.Grammatik.Parser.Cover.Differenz.sperrQuellen output.compiled.unit)
  memory : E.sp0 = output.sp0
  starts : E.starts = ⟨output.compiled.main, output.args⟩ :: output.starts
  checks : E.pruefungen = output.compiled.checkedDeclarations.val
  measure : E.measure = Gabbro.Grammatik.Parser.Cover.Differenz.massVon output.compiled.unit
  pointerSignatures : E.pointerSignatures =
    some (Gabbro.Grammatik.Parser.Cover.Differenz.zeigerSignaturen output.compiled.unit)
  runtimeRoots : E.gestartet.map (·.1) =
    output.compiled.unit.gestartet.filterMap (Gabbro.Grammatik.Parser.Cover.Differenz.wurzelIdx output.compiled.unit)
  runtimeParams : ∀ root ∈ E.gestartet, (declOf output.compiled.unit).params root.1 = []
  arenaTables : ∀ t : (declOf output.compiled.unit).Tab, (output.compiled.unit.tabs.get t).arena = true ↔
    ∃ arena ∈ E.arenen, arena.A.tab = t
  accumulators : List.Forall₂ (ImageAccumulator output) (imageAccumulatorItems output) E.akku
  summary : ∀ item world value, E.Q item world value = true ↔
    ∃ old arguments, AxNach E.P.axVertrag item old arguments world value

/-- For the part of the current emitter with no foreign or ownership
    declarations, the checked output supplies the specified source unit
    and its checker verdict without an extra unit-check hypothesis. -/
theorem Emitted.checked_image_model_empty (output : Emitted src reserve options)
    (noAxioms : output.compiled.unit.axs.length = 0)
    (noOwnership : OldSource.zertifizierbar output.compiled.unit = true)
    (noAccumulators : imageAccumulatorItems output = []) :
    let E := output.goalUnit (axWahr _)
    ImageModelUnit output E ∧
      akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true := by
  refine ⟨{
    program := rfl
    locks := rfl
    lockSources := HEq.rfl
    memory := rfl
    starts := rfl
    checks := rfl
    measure := rfl
    pointerSignatures := rfl
    runtimeRoots := OldSource.gestartet_leer _ output.compiled.hostedStarts.noDynamicRoots
    runtimeParams := ?_
    arenaTables := ?_
    accumulators := ?_
    summary := ?_
  }, output.goal_checker_concurrent _ (output.goal_axiomFree _ noAxioms)⟩
  · intro root member
    change root ∈ ([] : List _) at member
    cases member
  · intro t
    have closed := OldSource.zertifizierbar_ohne_arena _ noOwnership (output.compiled.unit.tabs.get t)
      (List.get_mem _ _)
    change _ ↔ ∃ arena ∈ ([] : List _), arena.A.tab = t
    simp only [closed, Bool.false_eq_true, List.not_mem_nil, false_and, exists_false]
  · rw [noAccumulators]
    exact .nil
  · intro item _ _
    exact False.elim ((Nat.not_lt_zero item.val) (noAxioms ▸ item.isLt))

/-- The source's one live entry, with every declared boot position already
    provisioned with its exact argument environment. -/
abbrev imageSourceStart {D : Deklaration} (E : Einheit D) : FadenMaschine D.mitRuhe :=
  FadenStart E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts) (fun i => decide (i = 0))

/-- Payload-level correspondence once runner threads have reached their
    lowered body positions. Private buffered writes are included in the
    per-thread views of the shared machine. -/
def ImageBodyMatches [Kern] (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    (machine : Cfg imageTSO (Res T)) (state : FadenMaschine (declOf output.compiled.unit).mitRuhe) : Prop :=
  ∃ footprint snapshots positions committed,
    PrivateBuffers footprint machine.ms.1 ∧
    MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
      ⟨(projectSCState footprint machine.ms).1, machine.ths⟩ state snapshots positions committed ∧
    ∀ i s, snapshots i = some s → (positions i).thr = i

/-- Initially the loader and the startup code can stutter in G. Allocated
    root positions remain ordered, and the initialized code stays loaded. -/
def ImageBootMatches [Kern] (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (machine : Cfg imageTSO (Res T))
    (state : FadenMaschine (declOf output.compiled.unit).mitRuhe) : Prop :=
  state.m = (imageSourceStart E).m ∧ state.wartet = (imageSourceStart E).wartet ∧
  machine.ths.length ≤ E.starts.length ∧
  (∀ i, state.lebt i = true ↔ i < machine.ths.length) ∧
  BytesAt machine.ms.1.m codeBase (output.image.code.flatMap encII)

/-- Slots are allocated only once. A retired runner slot still has a
    finished logical thread at the same index. -/
def ImageSlotsMatch [Kern] {D : Deklaration} (machine : Cfg imageTSO (Res T))
    (state : FadenMaschine D) : Prop :=
  (∀ i, state.lebt i = true ↔ i < machine.ths.length) ∧
  (∀ i, machine.ths[i]? = some none → FertigG state.m i)

def imageExternalEvent (event : Ev) : Bool :=
  let request := event.2.1
  !(decide (request = cloneReq ∨ request.nr.toNat = NR_EXIT ∨ request.nr.toNat = NR_EXIT_GROUP ∨
    request = futexReq request.a1 128 request.a3 ∨ request = futexReq request.a1 129 request.a3))

/-- The typed program's foreign calls occur in the same global order
    and at the same thread indices as the runner's external requests. -/
def ImageForeignTrace (output : Emitted src reserve options)
    (history : List Ev) (state : FadenMaschine (declOf output.compiled.unit).mitRuhe) : Prop :=
  let model := state.m.lauf.filterMap (fun step => match step.ereignis with
    | .fremd (.inl routine) => some (step.faden, routine)
    | _ => none)
  List.Forall₂ (fun event (typed : Faden × (declOf output.compiled.unit).Ax) =>
    event.1 = typed.1 ∧ ∃ gate, output.tor typed.2 = some gate ∧
      event.2.1.nr = BitVec.ofNat 64 gate.nr) (history.filter imageExternalEvent) model

/-- An accepted image may return its entry result, stop at a named
    hardware condition, or report a refused host clone. The exit is
    matched to the boundary preceding the terminal operation. -/
def ImageStopMatches (output : Emitted src reserve options)
    (O : Orakel (declOf output.compiled.unit)) (state : FadenMaschine (declOf output.compiled.unit).mitRuhe)
    (earlier last : List Ev) (ending : Ende) : Prop :=
  ∃ i req, last = [(i, req, none)] ∧ req.nr.toNat = NR_EXIT_GROUP ∧ ending = .exit req.a1 ∧
    let thread := state.m.faeden i
    ((i = 0 ∧ state.lebt i = true ∧ thread.stapel = [] ∧ thread.kopf.f = some output.compiled.main ∧
        ∃ (l : Bool) (Γ : Ctx) (env : Env _ Γ)
          (value : ErgVal _ (vertragVon _ thread.kopf.f).erg) (world : World _),
          thread.kopf.rest = ⟨l, Γ, (vertragVon _ thread.kopf.f).ende, env, .zurueckgekehrt (.inl value, world)⟩ ∧
          ExitErg output.image.Y.withIdle _ value req.a1) ∨
      (state.lebt i = true ∧ HaltBenannt O.mitRuhe output.image.passes state.m .hardware i ∧
        110 ≤ req.a1.toNat ∧ req.a1.toNat ≤ 115) ∨
      (req.a1 = BitVec.ofNat 64 cloneCode ∧
        ∃ id extra, (i, cloneReq, some (id, extra)) ∈ earlier ∧ id.toInt < 0))

abbrev ImageReach (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit)) :=
  FadenErreichbarX E.P.mitRuhe O.mitRuhe output.image.passes
    (GeteiltV (D := declOf output.compiled.unit) E.P E.ws)

abbrev ImageGoalAt (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit)) :=
  ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe output.image.passes
    (GeteiltV (D := declOf output.compiled.unit) E.P E.ws) (imageSourceStart E).m
    (E.arenen.map (·.mitRuhe))

/-- A source call used to explain a syscall lies inside that syscall's
    matching GX segment. Its request arguments and actual answer are tied
    to the oracle at that call, including caller-owned result areas. -/
def ImageGateEvent [Kern] (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    (before after : FadenMaschine (declOf output.compiled.unit).mitRuhe)
    (returned : Cfg imageTSO (Res T)) (event : Ev) : Prop :=
  let D := (declOf output.compiled.unit).mitRuhe
  let layout := output.image.Y.withIdle
  let request := event.2.1
  ∃ site : FadenMaschine D, ∃ memory : Speicher D,
    ∃ (routine : D.Ax) (world : World D) (args : Env D (D.aparams routine)),
      ImageReach output E O before site ∧ ImageReach output E O site after ∧
      site.lebt event.1 = true ∧
      (mitSpeicher site.m memory).foreignCallKey event.1 = some ⟨routine, world, args⟩ ∧
      (∀ carrier, ¬ GeteiltV (D := declOf output.compiled.unit) E.P E.ws carrier →
        TraegerGleich memory site.m.speicher carrier) ∧
      ∃ gate word extra, layout.tor routine = some gate ∧ request.nr = BitVec.ofNat 64 gate.nr ∧
        ArgsW layout (reqArg request) args ∧ event.2.2 = some (word, extra) ∧
        ((gate.resultArea = none ∧ (O.mitRuhe.wirkt routine world args).2 = rohW gate (D.agruende routine) word) ∨
          ∃ (j : Nat) (τ : Ty) (typed : D.aerg routine = some τ) (fp : W) (base : Nat),
            gate.resultArea = some j ∧ reqArg request j = slot fp (BitVec.ofNat 64 base) ∧
            AreaReply layout O.mitRuhe routine gate τ typed world args (returned.ms.1.view event.1) fp base word)

/-- One simulation carries the same IR endpoint and runner history through
    the entire execution. Its source steps must construct a reachable GX
    execution, including all intervening steps. -/
structure ImageSimulation [Kern] (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    (start : Cfg imageTSO Runner.X86.X) where
  related : List Ev → Cfg imageTSO Runner.X86.X → Cfg imageTSO (Res T) →
    FadenMaschine (declOf output.compiled.unit).mitRuhe → Prop
  initial : related [] start ⟨start.ms, [some t4]⟩ (imageSourceStart E)
  image : ∀ history machine ir state, related history machine ir state →
    Rel L0 ir machine ∧ ImageSlotsMatch ir state ∧ ImageForeignTrace output history state ∧
    (ImageBootMatches output E ir state ∨ ImageBodyMatches output E O ir state)
  step : ∀ history before ir state after events, related history before ir state →
    ProcessStep imageTSO (actX L0) before events after →
    ∃ ir' count next, ProcessPrefix imageTSO actI ir events count ir' ∧
      related (history ++ events) after ir' next ∧ ImageReach output E O state next ∧
      ∀ event ∈ events, imageExternalEvent event = true → ImageGateEvent output E O state next ir' event
  stop : ∀ earlier before ir state last ending, related earlier before ir state →
    Tr imageTSO (actX L0) before last ending 1 → ending ≠ .lauf →
    ImageStopMatches output O state earlier last ending

private theorem imageReach_trans {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {start middle last : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (first : ImageReach output E O start middle) (second : ImageReach output E O middle last) :
    ImageReach output E O start last := by
  induction second with
  | start => exact first
  | schritt before after _ step ih => exact .schritt before after ih step

/-- The single-step compiler obligation implies a matching GX endpoint
    for every continuing prefix of the actual x86 process. -/
theorem ImageSimulation.follow [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {start before finish : Cfg imageTSO Runner.X86.X} (sim : ImageSimulation output E O start)
    {events : List Ev} {count : Nat} (run : ProcessPrefix imageTSO (actX L0) before events count finish) :
    ∀ {history ir state}, sim.related history before ir state →
      ∃ ir' steps next, ProcessPrefix imageTSO actI ir events steps ir' ∧
        sim.related (history ++ events) finish ir' next ∧ ImageReach output E O state next := by
  induction run with
  | nil =>
    intro history ir state initial
    exact ⟨ir, 0, state, .nil ir, by simpa only [List.append_nil] using initial, .start⟩
  | cons step _ ih =>
    intro history ir state current
    obtain ⟨midIR, count, mid, trace, matched, advanced, _⟩ := sim.step _ _ _ _ _ _ current step
    obtain ⟨ir', steps, next, tail, endpoint, reached⟩ := ih matched
    exact ⟨ir', steps + count, next, trace.trans tail, by simpa only [List.append_assoc] using endpoint,
      imageReach_trans advanced reached⟩

/-- Once the compiler constructs the simulation, the full existing goal
    follows for each matched x86 prefix. Checker acceptance is proved by
    the Stage 0 theorem on its exported unit. -/
theorem ImageSimulation.goal [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {start finish : Cfg imageTSO Runner.X86.X} (sim : ImageSimulation output E O start)
    (accepted : akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true)
    (duties : NutzerPflichtA E) (calls : CallSitePflicht E) (posts : PostDeckt E)
    (binding : ForeignVertrag E O) (hardware : HardwareAnnahmenHw O E.Q)
    {events : List Ev} {count : Nat} (run : ProcessPrefix imageTSO (actX L0) start events count finish) :
    ∃ ir steps state, ProcessPrefix imageTSO actI ⟨start.ms, [some t4]⟩ events steps ir ∧
      sim.related events finish ir state ∧ ImageReach output E O (imageSourceStart E) state ∧
      ImageGoalAt output E O state := by
  obtain ⟨ir, steps, state, trace, endpoint, reached⟩ := sim.follow run sim.initial
  refine ⟨ir, steps, state, trace, endpoint, reached, ?_⟩
  exact gabbro_ziel akzeptiertX_pruefer _ E output.fsA output.lsA output.csA accepted duties calls posts O binding
    hardware output.image.passes _ _ (laufzeit_initRuhe E) _ _ reached

/-- A terminal observation is explained at its actual last runner step.
    The continuing prefix determines the corresponding source state. -/
theorem ImageSimulation.terminal [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {start : Cfg imageTSO Runner.X86.X} (sim : ImageSimulation output E O start)
    {events : List Ev} {ending : Ende} {count : Nat}
    (run : Tr imageTSO (actX L0) start events ending count) (stopped : ending ≠ .lauf) :
    ∃ earlier last state, events = earlier ++ last ∧
      ImageReach output E O (imageSourceStart E) state ∧ ImageStopMatches output O state earlier last ending := by
  obtain ⟨boundary, earlier, last, steps, trace, finish, eventsEq, _⟩ := run.split_stop stopped
  obtain ⟨ir, _, state, _, endpoint, reached⟩ := sim.follow trace sim.initial
  exact ⟨earlier, last, state, eventsEq, reached, sim.stop earlier boundary ir state last ending endpoint finish stopped⟩

/-- B6 for the production Stage 0 emitter. This definition is the claim
    to prove. A successful build fixes the source and model unit before
    universal quantification over the hardware, schedule and run. -/
def Stage0Correct [Kern] : Prop :=
  ∀ (source : String) (reserve : Nat) (options : Profil.Options) (bytes : List B),
    irBild source reserve options = .ok bytes →
    ∃ (output : Emitted source reserve options) (E : Einheit (declOf output.compiled.unit)),
      emit source reserve options = .ok output ∧ output.bytes = bytes ∧
      CanonicalSourceProgram output.compiled ∧ ImageModelUnit output E ∧
      akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true ∧
      ∀ (O : Orakel (declOf output.compiled.unit)),
        NutzerPflichtA E → CallSitePflicht E → PostDeckt E → ForeignVertrag E O →
        HardwareAnnahmenHw O E.Q → TorOK output.image.Y O → ImageGateAnswers output.image.Y O →
        ImageFutexAnswers → SichtOK O →
        ∀ (start : Cfg imageTSO Runner.X86.X), MappedImage output start →
        Nonempty (ImageSimulation output E O start)

end Gabbro.Stage0
