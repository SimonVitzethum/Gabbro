module

public import Stage0.Senke.Bild.ImageGoal
public import Stage0.Senke.Welt.Spans.IdleValue
public import Stage0.Senke.Bild.Mehr.StoreBuffer
public import Runner.Beweis.Lader
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Stage0.Senke Runner Runner.IR Runner.Beweis Runner.Mach
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

/-- The immutable instruction extent of the production payload, separated
    from the initialized stacks and mutable program data. -/
theorem Emitted.loaded_code [Kern] (output : Emitted src K options)
    {m : Mem} (loaded : BytesAt m Runner.Prog.IMG output.bytes) :
    BytesAt m codeBase (output.image.code.flatMap encII) := by
  obtain ⟨_, _, _, _, _, _, _, codeAndStacks, _⟩ :=
    bild_initialized_loaded_u output.initialValid output.emission output.funktionen_voll loaded
  exact codeAndStacks.left

/-- In the actual image the code ends exactly where the stack
    reservations begin. This uses the serialized instruction width. -/
theorem Emitted.code_end [Kern] (output : Emitted src K options) :
    codeBase + (output.image.code.flatMap encII).length = output.image.fp0 := by
  obtain ⟨_, _, _, placed, serialized, _, _, _⟩ :=
    bild_lage output.emission output.funktionen_voll
      (fun base bound => layU_in output.compiled.unit output.tor base bound)
      (fun base => layU_dis output.compiled.unit output.tor base)
      (fun base => by simp only [layU]; omega)
      (fun base => layU_sync output.compiled.unit output.tor base)
  rw [flatMap_enc_len, serialized, List.length_append, placed.head, placed.hfp]

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
    {m : Mem} (loaded : BytesAt m codeBase (output.image.code.flatMap encII)) {j : Nat}
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
  obtain ⟨_, _, sites, placed, code, _, _, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  rw [code] at loaded
  have instructions := codeAt_bytes _ codeBase placed.hops loaded
  have ready := codeAt_left (codeAt_left (codeAt_left instructions))
  have inside := (List.getElem?_eq_some_iff.mp declared).1
  have site := placed.spawn_entry j (by rw [List.length_map]; exact inside)
  have positioned : (⟨output.compiled.main, output.args⟩ :: output.starts)[j + 1]? = some start := declared
  exact ⟨codeAt_spawn_site ready (by simpa only [List.length_map] using site),
    (output.bootStart_frame Q (j + 1) start positioned).1,
    output.goalStart_argument Q (j + 1) start positioned⟩

end Gabbro.Stage0
