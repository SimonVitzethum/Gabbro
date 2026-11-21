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

/-- The actual x86 runner maps to the same IR history under the external
    answer restrictions, independently of any compiler simulation. -/
theorem MappedImage.runner_prefix [Kern] {output : Emitted src reserve options}
    {start finish : Cfg imageTSO Runner.X86.X} (mapped : MappedImage output start)
    {events : List Ev} {count : Nat}
    (run : ProcessPrefix imageTSO (actX L0) start events count finish) :
    ∃ ir steps, ProcessPrefix imageTSO actI ⟨start.ms, [some t4]⟩ events steps ir ∧ Rel L0 ir finish :=
  runner_process_prefix imageTSO_fixed cinv_L0 mapped.loader run

/-- Every first continuing IR step at the mapped loader reads the exact
    frame word and enters the emitted code. The caller's empty buffers
    exclude a flush and the singleton thread list excludes other work. -/
theorem MappedImage.dispatch_step [Kern] {output : Emitted src reserve options}
    {start : Cfg imageTSO Runner.X86.X} (mapped : MappedImage output start)
    {after : Cfg imageTSO (Res T)} {events : List Ev}
    (step : ProcessStep imageTSO actI ⟨start.ms, [some t4]⟩ events after) :
    events = [] ∧ after =
      ⟨start.ms, [some (.next ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩)]⟩ := by
  have onlyThread {i : Nat} {r : Res T} (found : ([some t4] : List (Option (Res T)))[i]? = some (some r)) :
      i = 0 ∧ r = t4 := by
    cases i <;> simp_all
  cases step with
  | tau flush =>
    obtain ⟨i, _, _, _, pending, _⟩ := flush
    rw [mapped.emptyBuffers i] at pending
    cases pending
  | priv found executed =>
    obtain ⟨_, rfl⟩ := onlyThread found
    cases executed
  | ask found asked _ answered continued =>
    obtain ⟨rfl, rfl⟩ := onlyThread found
    cases asked
    have frame := output.loader_frame mapped.bytes
    obtain ⟨same, extra, read⟩ := answered.1
    have exactWord : _ = some (BitVec.ofNat 64 output.image.fp0, extra) := by
      simpa only [rdN, TSt.view, mapped.emptyBuffers 0, List.foldl_nil, frame, Option.map_some] using read
    subst_vars
    cases continued
    exact ⟨rfl, rfl⟩
  | exit found asked _ =>
    obtain ⟨_, rfl⟩ := onlyThread found
    cases asked
  | cloneNo found asked _ _ _ =>
    obtain ⟨_, rfl⟩ := onlyThread found
    cases asked
  | clone found asked _ _ _ _ =>
    obtain ⟨_, rfl⟩ := onlyThread found
    cases asked

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
    change _ ↔ ∃ arena ∈ ([] : List (ArenaOwnership.Body.ArenaIface (declOf output.compiled.unit))), arena.A.tab = t
    simp only [closed, Bool.false_eq_true, List.not_mem_nil, false_and, exists_false]
  · rw [noAccumulators]
    exact .nil
  · intro item _ _
    exact False.elim ((Nat.not_lt_zero item.val) (noAxioms ▸ item.isLt))

/-- The source's one live entry, with every declared boot position already
    provisioned with its exact argument environment. -/
abbrev imageSourceStart {D : Deklaration} (E : Einheit D) : FadenMaschine D.mitRuhe :=
  FadenStart E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts) (fun i => decide (i = 0))

/-- An instruction in the compiled root stub uses the stack frame and
    code range assigned to that root by the image layout. -/
def ImageRootInstruction (output : Emitted src reserve options) (thread : Nat) (pointer : T) : Prop :=
  let count := output.starts.length
  let base := if thread = 0 then 0 else 10 * count + startLen * thread
  let size := if thread = 0 then 10 * count + startLen else startLen
  pointer.fp = BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * thread)) ∧
  ∃ instruction, base ≤ instruction ∧ instruction < base + size ∧
    pointer.pc = BitVec.ofNat 64 (codeBase + 16 * instruction)

/-- A thread outside the lowered body is at the mapped loader, its
    own root stub, or the pending clone continuation of that stub. -/
def ImageRootPhase [Kern] (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (history : List Ev)
    (memory : Mem) (thread : Nat) (control : Res T)
    (state : FadenMaschine (declOf output.compiled.unit).mitRuhe) : Prop :=
  (thread = 0 ∧ control = t4 ∧ state = imageSourceStart E ∧
    BytesAt memory Runner.Prog.IMG output.bytes) ∨
  ∃ start, E.starts[thread]? = some start ∧
    (state.m.faeden thread = (imageSourceStart E).m.faeden thread ∨ FertigG state.m thread) ∧
    BytesAt memory codeBase (output.image.code.flatMap encII) ∧
    FrameOK memory (BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * thread))) output.image.Ks ∧
    (∀ i (inside : i < (encodeEnv output.image.Y start.2).length),
      memory.rd64 (BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * thread) +
        8 * (FB + FB + i))) = some (encodeEnv output.image.Y start.2)[i]) ∧
    ∃ t : T, ImageRootInstruction output thread t ∧
      (control = .next t ∨ RunP (IR.step t) memory control memory ∨
        ∃ id extra, (thread, cloneReq, some (id, extra)) ∈ history ∧ control = ret1 t id)

/-- Startup and lowered body threads can coexist. Body positions use the
    compiler's frame relation. Each omitted live slot is accounted for
    by its exact root stub or by the loader. -/
def ImageRuntimeMatches [Kern] (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    (history : List Ev) (machine : Cfg imageTSO (Res T))
    (state : FadenMaschine (declOf output.compiled.unit).mitRuhe) : Prop :=
  ∃ footprint body,
    PrivateBuffers footprint machine.ms.1 ∧ body.length = machine.ths.length ∧
    (((∀ (i : Nat) (r : Res T), body[i]? ≠ some (some r)) ∧
      WeltAt (projectSCState footprint machine.ms).1 output.image.Y.withIdle (state.m.speicher.welt [])) ∨
      ∃ snapshots positions committed,
        MTRel E.P.mitRuhe O.mitRuhe output.image.passes output.image.Y.withIdle
          ⟨(projectSCState footprint machine.ms).1, body⟩ state snapshots positions committed ∧
        ∀ i s, snapshots i = some s → (positions i).thr = i ∧ footprint i = s.F) ∧
    ∀ i, body[i]? = machine.ths[i]? ∨
      ∃ r, body[i]? = some none ∧ machine.ths[i]? = some (some r) ∧
        ImageRootPhase output E history (machine.ms.1.view i) i r state

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

/-- The actual mapped output and empty initial buffers establish the
    initial phase, exact source memory and empty observation history. -/
theorem MappedImage.source_start [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {machine : Cfg imageTSO Runner.X86.X}
    (mapped : MappedImage output machine) (unit : ImageModelUnit output E)
    (O : Orakel (declOf output.compiled.unit)) :
    let ir : Cfg imageTSO (Res T) := ⟨machine.ms, [some t4]⟩
    Rel L0 ir machine ∧ ImageSlotsMatch ir (imageSourceStart E) ∧
      ImageForeignTrace output [] (imageSourceStart E) ∧
      ImageRuntimeMatches output E O [] ir (imageSourceStart E) := by
  intro ir
  refine ⟨mapped.loader, ⟨?_, ?_⟩, .nil, ?_⟩
  · intro i
    cases i <;> simp [ir, imageSourceStart, FadenStart]
  · intro i retired
    cases i <;> simp [ir] at retired
  · refine ⟨fun _ _ => False, [none], privateBuffers_empty mapped.emptyBuffers, rfl, Or.inl ⟨?_, ?_⟩, ?_⟩
    · intro i r
      cases i <;> simp
    · change WeltAt (mergedView machine.ms.1 (fun _ _ => False)) _
        ((speicherR E.sp0).welt [])
      rw [mergedView_empty _ _ mapped.emptyBuffers, unit.memory]
      exact (output.loaded_initial_world mapped.bytes).withIdle
    · intro i
      cases i with
      | zero => exact Or.inr ⟨t4, rfl, rfl, Or.inl ⟨rfl, rfl, rfl, by
          change BytesAt (machine.ms.1.view 0) Runner.Prog.IMG output.bytes
          simpa only [TSt.view, mapped.emptyBuffers 0, List.foldl_nil] using mapped.bytes⟩⟩
      | succ i => exact Or.inl rfl

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
      (i = 0 ∧ req.a1 = BitVec.ofNat 64 cloneCode ∧
        ∃ prior id extra, earlier.filter (fun event => event.1 == i) =
          prior ++ [(i, cloneReq, some (id, extra))] ∧ id.toInt < 0))

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
    Rel L0 ir machine ∧ FileInv machine.ms.1.m ∧ ImageSlotsMatch ir state ∧ ImageForeignTrace output history state ∧
    ImageRuntimeMatches output E O history ir state
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
        ∃ sim : ImageSimulation output E O start,
          ∀ finish events count, ProcessPrefix imageTSO (actX L0) start events count finish →
            ∃ ir steps state, ProcessPrefix imageTSO actI ⟨start.ms, [some t4]⟩ events steps ir ∧
              sim.related events finish ir state ∧ ImageReach output E O (imageSourceStart E) state ∧
              ImageGoalAt output E O state

end Gabbro.Stage0
