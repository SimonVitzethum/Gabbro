module

public import Stage0.Senke.Bild.ImageGoal
public import Stage0.Senke.Welt.Spans.IdleValue
public import Stage0.Senke.Bild.Mehr.StoreBuffer
public import Runner.Beweis.Lader
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner Runner.IR Runner.Beweis Runner.Mach
  Gabbro.Stage0.Senke.BildMehr

variable {src : String} {K : Nat} {options : Profil.Options}

/-- The frame word consumed by the real runner loader is taken from the
    production payload and names the certified image's initial frame. -/
theorem Emitted.loader_frame [Kern] (output : Emitted src K options) {m : Mem}
    (loaded : BytesAt m Runner.Prog.IMG output.bytes) :
    m.rd64 (BitVec.ofNat 64 Runner.Prog.IMG) = some (BitVec.ofNat 64 output.image.fp0) := by
  obtain ⟨_, _, _, _, _, _, header, _, _⟩ :=
    bild_initialized_loaded_u output.initialValid output.emission output.funktionen_voll loaded
  obtain ⟨_, _, _, placed, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  have fits := placed.hfit
  exact rd64_leN header (by omega)

/-- After mapping the actual CLI payload, the runner's real header request
    can read it under TSO and resumes at the image's certified entry.
    The reading thread has no pending writes to forward. -/
theorem irBild_loader_dispatch [Kern] {output : Emitted src K options} {bytes : List Runner.B}
    (built : emit src K options = .ok output) (payload : irBild src K options = .ok bytes)
    {s : (TSO L0).St} {thread : Nat} (empty : s.1.buf thread = [])
    (loaded : BytesAt s.1.m Runner.Prog.IMG bytes) :
    ∃ resume : Ans → Res T,
      t4 = .ask (.rd 8 (BitVec.ofNat 64 Runner.Prog.IMG)) resume ∧
      (TSO L0).ans s thread (.rd 8 (BitVec.ofNat 64 Runner.Prog.IMG))
        (some (BitVec.ofNat 64 output.image.fp0, 0)) s ∧
      resume (some (BitVec.ofNat 64 output.image.fp0, 0)) =
        .next ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩ := by
  have frame := output.loader_frame ((irBild_eq_output built payload).symm ▸ loaded)
  refine ⟨fun answer => opt answer fun pair => .next ⟨BitVec.ofNat 64 Runner.Prog.IMG + 16, pair.1⟩,
    rfl, ⟨rfl, 0, ?_⟩, rfl⟩
  simpa only [TSt.view, empty, List.foldl_nil, rdN, frame, Option.map_some]

/-- The mapped CLI payload reaches its certified entry through an actual
    continuing process step, with the same memory and no host event. -/
theorem irBild_loaded_entry_prefix [Kern] {output : Emitted src K options} {bytes : List Runner.B}
    (built : emit src K options = .ok output) (payload : irBild src K options = .ok bytes)
    {s : (TSO L0).St} (empty : s.1.buf 0 = [])
    (loaded : BytesAt s.1.m Runner.Prog.IMG bytes) :
    ProcessPrefix (TSO L0) actI ⟨s, [some t4]⟩ [] 1
      ⟨s, [some (.next ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩)]⟩ := by
  obtain ⟨resume, read, answered, entered⟩ := irBild_loader_dispatch built payload empty loaded
  have step : ProcessStep (TSO L0) actI ⟨s, [some t4]⟩
      (lbl 0 (.rd 8 (BitVec.ofNat 64 Runner.Prog.IMG))
        (some (BitVec.ofNat 64 output.image.fp0, 0)))
      ⟨s, [some (.next ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩)]⟩ :=
    ProcessStep.ask (i := 0) rfl (by rw [read]; rfl) rfl answered
      (congrArg Res.next entered)
  exact ProcessPrefix.ofStep step

/-- The actual post-mapping entry step starts at the certified frame and
    preserves the full typed initial world in the SC projection. -/
theorem irBild_loaded_entry_world [Kern] {output : Emitted src K options} {bytes : List Runner.B}
    (built : emit src K options = .ok output) (payload : irBild src K options = .ok bytes)
    (Q : AxEns (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit))
    {s : (TSO L0).St} (empty : ∀ i, s.1.buf i = [])
    (loaded : BytesAt s.1.m Runner.Prog.IMG bytes) (footprint : Nat → W → Prop) :
    ProcessPrefix (TSO L0) actI ⟨s, [some t4]⟩ [] 1
        ⟨s, [some (.next ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩)]⟩ ∧
      WeltAt (projectSCState footprint s).1 output.image.Y.withIdle
        ((speicherR (output.goalUnit Q).sp0).welt []) := by
  refine ⟨irBild_loaded_entry_prefix built payload (empty 0) loaded, ?_⟩
  change WeltAt (mergedView s.1 footprint) _ _
  rw [mergedView_empty _ _ empty]
  exact (output.loaded_initial_world ((irBild_eq_output built payload).symm ▸ loaded)).withIdle

/-- Every TSO answer to the loaded header read returns the same entry
    frame. The extra answer word has no effect on the loader. -/
theorem irBild_loader_dispatch_all [Kern] {output : Emitted src K options} {bytes : List Runner.B}
    (built : emit src K options = .ok output) (payload : irBild src K options = .ok bytes)
    {s s' : (TSO L0).St} {thread : Nat} {answer : Ans} (empty : s.1.buf thread = [])
    (loaded : BytesAt s.1.m Runner.Prog.IMG bytes)
    (answered : (TSO L0).ans s thread (.rd 8 (BitVec.ofNat 64 Runner.Prog.IMG)) answer s') :
    s' = s ∧
      ∀ resume, t4 = .ask (.rd 8 (BitVec.ofNat 64 Runner.Prog.IMG)) resume →
        resume answer = .next ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩ := by
  have frame := output.loader_frame ((irBild_eq_output built payload).symm ▸ loaded)
  obtain ⟨same, extra, actual⟩ := answered
  refine ⟨same, ?_⟩
  intro resume read
  have exactAnswer : answer = some (BitVec.ofNat 64 output.image.fp0, extra) := by
    simpa only [TSt.view, empty, List.foldl_nil, rdN, frame, Option.map_some] using actual
  rw [exactAnswer]
  have equalResume := (Res.ask.inj read).2
  rw [← equalResume]
  rfl

/-- The ordered start environments used in the goal theorem have exactly
    the words serialized in the image, also after idle extension. -/
theorem Emitted.goal_arguments_encoded (output : Emitted src K options)
    (Q : AxEns (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit)) :
    output.image.args :: output.image.rootArgs =
      (output.goalUnit Q).starts.map (fun start => encodeEnv output.image.Y.withIdle (envR start.2)) := by
  obtain ⟨_, _, _, _, _, _, args, roots⟩ :=
    bild_lage output.emission output.funktionen_voll
      (fun base bound => layU_in output.compiled.unit output.tor base bound)
      (fun base => layU_dis output.compiled.unit output.tor base)
      (fun base => by simp only [layU]; omega)
      (fun base => layU_sync output.compiled.unit output.tor base)
  rw [args, roots, output.goalUnit_starts]
  simp only [List.map_cons, encodeEnv_withIdle, Emitted.starts]

/-- Loaded bytes contain the complete initialized stacks of the goal's
    exact ordered start environments. -/
theorem Emitted.goal_arguments_loaded [Kern] (output : Emitted src K options)
    (Q : AxEns (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit))
    {m : Mem} (loaded : BytesAt m Runner.Prog.IMG output.bytes) :
    ∃ stackBytes, startStackBytes output.image.Ks (FB + FB)
        ((output.goalUnit Q).starts.map (fun start => encodeEnv output.image.Y.withIdle (envR start.2))) =
        some stackBytes ∧ BytesAt m output.image.fp0 stackBytes := by
  obtain ⟨_, _, _, stackBytes, made, _, _, _, memory⟩ :=
    bild_initialized_loaded_u output.initialValid output.emission output.funktionen_voll loaded
  exact ⟨stackBytes, output.goal_arguments_encoded Q ▸ made, memory⟩

private theorem codeAt_spawn_site [Kern] {m : Mem} {scratch : Nat} :
    ∀ {sites : List (Nat × Nat)} {pc : W} {j : Nat} {site : Nat × Nat},
      CodeAt m pc (spawnC scratch sites) → sites[j]? = some site →
        CodeAt m (pc + BitVec.ofNat 64 (16 * (10 * j))) (spawnOne scratch site.1 site.2) := by
  intro sites
  induction sites with
  | nil => intro _ _ _ _ found; simp at found
  | cons first rest ih =>
    intro pc j site code found
    have placed : CodeAt m pc (spawnOne scratch first.1 first.2 ++ spawnC scratch rest) := by
      cases first
      exact code
    cases j with
    | zero =>
      cases found
      simpa only [Nat.mul_zero, BitVec.add_zero] using codeAt_left placed
    | succ j =>
      have next := codeAt_right placed
      rw [spawnOne_len] at next
      have siteCode := ih next (by simpa only [List.getElem?_cons_succ] using found)
      rw [BitVec.add_assoc, ofNat_add64] at siteCode
      have offset : 16 * (10 * (j + 1)) = 16 * 10 + 16 * (10 * j) := by omega
      simpa only [offset] using siteCode

/-- The loaded clone site for boot root `j` contains the instructions for
    its own relocated entry and frame. Logical thread `j + 1` carries the
    same root and arguments at the model's initial memory. -/
theorem Emitted.loaded_boot_site [Kern] (output : Emitted src K options)
    (Q : AxEns (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit))
    {m : Mem} (loaded : BytesAt m Runner.Prog.IMG output.bytes) {j : Nat}
    {start : Σ f : (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit).Fn,
      Env (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit)
        ((Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit).params f)}
    (declared : output.starts[j]? = some start) :
    CodeAt m (BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * (10 * j)))
        (spawnOne (startScratch output.compiled.main)
          (codeBase + 16 * (10 * output.starts.length + startLen + startLen * j))
          (output.image.fp0 + 8 * (output.image.Ks * (j + 1)))) ∧
      (output.bootStart Q).lebt (j + 1) = true ∧
      initRuhe (output.goalUnit Q).starts (j + 1) = ⟨some start.1, envR start.2⟩ := by
  obtain ⟨_, _, _, _, made, _, _, loadedStartup, _⟩ :=
    bild_initialized_loaded_u output.initialValid output.emission output.funktionen_voll loaded
  obtain ⟨_, _, _, placed, code, _, args, roots⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  have startup : BytesAt m codeBase (output.image.code.flatMap encII ++
      ((startStackBytes output.image.Ks (FB + FB) (output.image.args :: output.image.rootArgs)).getD [] ++ [])) := by
    simpa only [made, Option.getD_some, List.append_nil] using loadedStartup
  rw [code, args, roots] at startup
  have ready := (spawn_ready placed startup).1
  have inside := (List.getElem?_eq_some_iff.mp declared).1
  have site := placed.spawn_entry j (by rw [List.length_map]; exact inside)
  have positioned : (⟨output.compiled.main, output.args⟩ :: output.starts)[j + 1]? = some start := declared
  exact ⟨codeAt_spawn_site ready (by simpa only [List.length_map] using site),
    (output.bootStart_frame Q (j + 1) start positioned).1,
    output.goalStart_argument Q (j + 1) start positioned⟩

/-- Only a positive answer to the runner's clone request allocates a
    thread slot. Exited threads keep their old position in the list. -/
def createsThread (event : Ev) : Bool :=
  if event.2.1 = cloneReq then
    match event.2.2 with
    | some (id, _) => decide (0 < id.toInt)
    | none => false
  else false

private theorem processStep_threadSlots {M : MemSys} {act : θ → Res θ}
    {before after : Cfg M θ} {events : List Ev}
    (step : ProcessStep M act before events after) :
    after.ths.length = before.ths.length + events.countP createsThread := by
  cases step with
  | tau _ => simp
  | priv _ _ => simp
  | @ask _ _ _ o _ _ _ _ _ ordinary _ _ =>
    cases o with
    | rd | wr | cas | fp => simp [Mach.lbl]
    | sys q =>
      have distinct : q ≠ cloneReq := by
        intro equal
        subst q
        simp [Op.special] at ordinary
      simp [Mach.lbl, createsThread, distinct]
  | @exit _ _ q _ _ _ number =>
    have distinct : q ≠ cloneReq := by
      intro equal
      subst q
      exact (by decide : cloneReq.nr.toNat ≠ NR_EXIT) number
    simp [createsThread, distinct]
  | @cloneNo _ _ _ _ a _ _ _ _ refused _ =>
    cases a with
    | none => simp [createsThread]
    | some pair =>
      obtain ⟨id, extra⟩ := pair
      simp [createsThread, refused id extra rfl]
  | clone _ _ _ positive _ _ => simp [createsThread, positive]

/-- The actual runner assigns new positions consecutively. The exact
    increase across any continuing prefix is the number of successful
    clone events, even when exits, other system calls and memory steps
    are interleaved. -/
theorem processPrefix_threadSlots {M : MemSys} {act : θ → Res θ}
    {before after : Cfg M θ} {events : List Ev} {steps : Nat}
    (run : ProcessPrefix M act before events steps after) :
    after.ths.length = before.ths.length + events.countP createsThread := by
  induction run with
  | nil => simp
  | cons step _ ih =>
    rw [ih, processStep_threadSlots step, List.countP_append, Nat.add_assoc]

/-- After a spawn instruction has read its entry address and frame, a
    successful clone puts the child at those addresses in the next slot
    and returns the thread ID to the parent's destination operation. -/
theorem bootClone_step {M : MemSys} {before : Cfg M (Res T)} {i : Nat}
    {parent child : T} {id extra : W} {memory : M.St}
    (pending : before.ths[i]? = some (some (.ask (.sys cloneReq) fun answer =>
      opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)))
    (answer : M.ans before.ms i (.sys cloneReq) (some (id, extra)) memory)
    (positive : 0 < id.toInt) :
    let threads := before.ths.set i (some (ret1 parent id)) ++ [some (.next child)]
    ProcessStep M actI before [(i, cloneReq, some (id, extra))] ⟨memory, threads⟩ ∧
      threads[before.ths.length]? = some (some (.next child)) := by
  have nonzero : id ≠ 0 := by
    intro equal
    subst id
    exact (by decide : ¬ (0 < (0 : W).toInt)) positive
  constructor
  · exact .clone pending rfl answer positive (by simp only [opt_some, if_neg nonzero]) rfl
  · rw [List.getElem?_append_right (by rw [List.length_set]), List.length_set, Nat.sub_self]
    rfl

/-- The runner fetches a spawn, reads its operand index and both stack
    words, and reaches the pending clone. These five actual TSO steps
    leave memory unchanged and use the parent's view of its own writes. -/
theorem bootClone_read_prefix {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {parent child : T}
    {dest index pad : BitVec 32}
    (running : before.ths[i]? = some (some (.next parent)))
    (instruction : InsAt (before.ms.1.view i) parent.pc 24 dest index pad)
    (entry : (before.ms.1.view i).rd64 (slot parent.fp (sx index)) = some child.pc)
    (frame : (before.ms.1.view i).rd64 (slot parent.fp (sx index) + 8) = some child.fp) :
    ProcessPrefix (TSO layout) actI before [] 5
      ⟨before.ms, before.ths.set i (some (.ask (.sys cloneReq) fun answer =>
        opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1))⟩ := by
  let onThread (r : Res T) : Cfg (TSO layout) (Res T) :=
    ⟨before.ms, before.ths.set i (some r)⟩
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have read (width : Nat) (address value : W) (resume : Ans → Res T)
      (loaded : rdN (before.ms.1.view i) width address = some value) :
      ProcessStep (TSO layout) actI (onThread (.ask (.rd width address) resume)) []
        (onThread (resume (some (value, 0)))) := by
    have step := ProcessStep.ask (act := actI) (i := i)
      (c := onThread (.ask (.rd width address) resume))
      (List.getElem?_set_self inside) rfl rfl
      (show (TSO layout).ans before.ms i (.rd width address) (some (value, 0)) before.ms from
        ⟨rfl, 0, by rw [loaded]; rfl⟩)
      (t' := resume (some (value, 0))) rfl
    simpa only [onThread, List.set_set, Mach.lbl] using step
  let clone : Res T := .ask (.sys cloneReq) fun answer =>
    opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1
  let readFrame (pc : W) : Res T := rd64 (slot parent.fp (sx index) + 8) fun fp =>
    .ask (.sys cloneReq) fun answer =>
      opt answer fun pair => if pair.1 = 0 then .next ⟨pc, fp⟩ else ret1 parent pair.1
  have started : ProcessStep (TSO layout) actI before [] (onThread (IR.step parent)) :=
    .priv running rfl
  have fetched : ProcessStep (TSO layout) actI (onThread (IR.step parent)) [] (onThread (op 24 parent)) := by
    have loaded : rdN (before.ms.1.view i) 1 parent.pc = some ((24 : B).setWidth 64) := by
      simp only [rdN, instruction.op, Option.map_some]
    exact read 1 parent.pc _ (fun answer => opt answer fun pair =>
      op (pair.1.setWidth 8 |>.setWidth 64).toNat parent) loaded
  have indexed : ProcessStep (TSO layout) actI (onThread (op 24 parent)) []
      (onThread (ld parent (sx index) readFrame)) := by
    have loaded : rdN (before.ms.1.view i) 4 (parent.pc + 8) = some (index.setWidth 64) := by
      simp only [rdN, instruction.f2, Option.map_some]
    simpa [op, f2, rd32, ld, readFrame] using
      read 4 (parent.pc + 8) _ (fun answer => opt answer fun pair =>
        ld parent (sx (pair.1.setWidth 32)) fun pc =>
          rd64 (slot parent.fp (sx (pair.1.setWidth 32)) + 8) fun fp =>
            .ask (.sys cloneReq) fun answer =>
              opt answer fun pair => if pair.1 = 0 then .next ⟨pc, fp⟩ else ret1 parent pair.1) loaded
  have entered : ProcessStep (TSO layout) actI (onThread (ld parent (sx index) readFrame)) []
      (onThread (readFrame child.pc)) :=
    read 8 _ _ (fun answer => opt answer fun pair => readFrame pair.1) entry
  have framed : ProcessStep (TSO layout) actI (onThread (readFrame child.pc)) [] (onThread clone) :=
    read 8 _ _ (fun answer => opt answer fun frame =>
      .ask (.sys cloneReq) fun answer =>
        opt answer fun pair => if pair.1 = 0 then .next ⟨child.pc, frame.1⟩ else ret1 parent pair.1) frame
  exact .cons started (.cons fetched (.cons indexed (.cons entered (.cons framed (.nil _)))))

end Gabbro.Stage0
