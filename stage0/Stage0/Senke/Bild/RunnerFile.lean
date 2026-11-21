module

public import Stage0.Senke.Images.Correctness
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Runner Runner.Beweis Runner.IR Runner.Mach Runner.Prog Gabbro.Grammatik
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Stage0.Senke

variable [Kern]

/-- The loaded runner file stays read-only, including with pending writes.
    Buffered stores must be tracked separately because a flush spends the
    permission already checked when its store was issued. -/
structure ImageFileStable (state : imageTSO.St) : Prop where
  file : FileInv state.1.m
  buffers : ∀ i store, store ∈ state.1.buf i → ∀ byte, byte < 8 →
    ∀ offset, offset < image.length →
      BitVec.ofNat 64 (BASE + offset) ≠ store.1 + BitVec.ofNat 64 byte

private theorem fileOutsideWritable {memory : Mem} (file : FileInv memory) {address : W}
    (writable : Mem.all memory.wr address 8 = true) {byte : Nat} (inside : byte < 8)
    {offset : Nat} (loaded : offset < image.length) :
    BitVec.ofNat 64 (BASE + offset) ≠ address + BitVec.ofNat 64 byte := by
  intro overlap
  have forbidden := (file offset loaded).2.2
  rw [overlap, Mem.all_spec writable inside] at forbidden
  cases forbidden

private theorem fileAfterWrite {memory : Mem} (file : FileInv memory) {address : W} {value : Nat}
    (outside : ∀ byte, byte < 8 → ∀ offset, offset < image.length →
      BitVec.ofNat 64 (BASE + offset) ≠ address + BitVec.ofNat 64 byte) :
    FileInv (Mem.write memory address 8 value) := by
  intro offset loaded
  have exactByte := (write_far (v := value) (m := memory) (fun byte inside => outside byte inside offset loaded)).1
  rw [exactByte]
  exact file offset loaded

private theorem ImageFileStable.flush {state after : imageTSO.St}
    (stable : ImageFileStable state) (step : imageTSO.tau state after) : ImageFileStable after := by
  obtain ⟨i, address, value, rest, pending, updated⟩ := step
  have stored : (address, value) ∈ state.1.buf i := by
    rw [pending]
    exact List.mem_cons_self
  refine ⟨?_, ?_⟩
  · rw [updated]
    exact fileAfterWrite stable.file (stable.buffers i (address, value) stored)
  · intro j store member
    apply stable.buffers j store
    simp only [updated, TSt.setBuf] at member
    split at member
    · rename_i same
      subst j
      rw [pending]
      exact List.mem_cons_of_mem _ member
    · exact member

private theorem ImageFileStable.nonSys {state after : imageTSO.St} {i : Nat} {op : Op} {answer : Ans}
    (stable : ImageFileStable state) (quiet : lbl i op answer = [])
    (step : imageTSO.ans state i op answer after) : ImageFileStable after := by
  cases op with
  | rd =>
    have same := step.1.1
    cases same
    exact stable
  | fp =>
    have same := step.1.1
    cases same
    exact stable
  | sys => cases quiet
  | wr address value =>
    obtain ⟨_, _, rfl⟩ | ⟨writable, _, updated⟩ := step.1
    · exact stable
    · refine ⟨?_, ?_⟩
      · rw [updated]
        exact stable.file
      · intro j store member byte inside offset loaded
        simp only [updated, TSt.setBuf] at member
        split at member
        · rename_i same
          subst j
          rcases List.mem_append.mp member with old | new
          · exact stable.buffers i store old byte inside offset loaded
          · have same := List.mem_singleton.mp new
            subst store
            exact fileOutsideWritable stable.file writable inside loaded
        · exact stable.buffers j store member byte inside offset loaded
  | cas address expected value =>
    obtain ⟨_, failed | success⟩ := step.1
    · obtain ⟨_, _, rfl⟩ := failed
      exact stable
    · obtain ⟨old, memory, compared, _, updated⟩ := success
      unfold Mem.cas at compared
      split at compared
      · rename_i permissions
        simp only [Option.some.injEq, Prod.mk.injEq] at compared
        obtain ⟨rfl, rfl⟩ := compared
        refine ⟨?_, ?_⟩
        · rw [updated]
          change FileInv (if _ then _ else _)
          split
          · exact fileAfterWrite stable.file (fun _ inside _ loaded =>
              fileOutsideWritable stable.file (Bool.and_eq_true_iff.mp permissions).2 inside loaded)
          · exact stable.file
        · rw [updated]
          exact stable.buffers
      · cases compared

/-- Ordinary process steps, including atomic updates and asynchronous
    flushes, preserve the executable bytes and every pending write's
    disjointness. Host calls are accounted for by their own contracts. -/
theorem ImageFileStable.silent {θ : Type} {act : θ → Res θ} {before after : Cfg imageTSO θ}
    (stable : ImageFileStable before.ms) (step : ProcessStep imageTSO act before [] after) :
    ImageFileStable after.ms := by
  generalize silence : ([] : List Ev) = events at step
  cases step with
  | tau moved => exact stable.flush moved
  | priv => exact stable
  | ask _ _ _ answered _ => exact stable.nonSys silence.symm answered
  | exit => cases silence
  | cloneNo => cases silence
  | clone => cases silence

/-- A finite silent execution preserves the read-only runner file,
    for either the IR or the actual x86 thread step function. -/
theorem ImageFileStable.silent_prefix {θ : Type} {act : θ → Res θ}
    {before after : Cfg imageTSO θ} {count : Nat}
    (stable : ImageFileStable before.ms) (run : ProcessPrefix imageTSO act before [] count after) :
    ImageFileStable after.ms := by
  generalize silence : ([] : List Ev) = events at run
  induction run with
  | nil => exact stable
  | cons step _ ih =>
    obtain ⟨quiet, rest⟩ := List.append_eq_nil_iff.mp silence.symm
    exact ih (stable.silent (quiet ▸ step)) rest.symm

private theorem fileInv_view_iff {state : imageTSO.St} {i : Nat}
    (outside : ∀ store, store ∈ state.1.buf i → ∀ byte, byte < 8 →
      ∀ offset, offset < image.length →
        BitVec.ofNat 64 (BASE + offset) ≠ store.1 + BitVec.ofNat 64 byte) :
    FileInv (state.1.view i) ↔ FileInv state.1.m := by
  have same (offset : Nat) (loaded : offset < image.length) :
      (state.1.view i).b (BitVec.ofNat 64 (BASE + offset)) = state.1.m.b (BitVec.ofNat 64 (BASE + offset)) ∧
      (state.1.view i).rd (BitVec.ofNat 64 (BASE + offset)) = state.1.m.rd (BitVec.ofNat 64 (BASE + offset)) :=
    foldl_far (state.1.buf i) state.1.m (fun store member byte inside =>
      outside store member byte inside offset loaded)
  have permission : (state.1.view i).wr = state.1.m.wr := foldl_wr _ _
  constructor
  · intro visible offset loaded
    obtain ⟨bytes, read⟩ := same offset loaded
    rw [← bytes, ← read, ← permission]
    exact visible offset loaded
  · intro global offset loaded
    obtain ⟨bytes, read⟩ := same offset loaded
    rw [bytes, read, permission]
    exact global offset loaded

/-- A host contract sees the issuer's TSO view. Because the image memory
    rule keeps all pending stores, preservation of the file in that view
    implies preservation in global memory. Clone is memory-neutral. -/
theorem ImageFileStable.sys {state after : imageTSO.St} {i : Nat} {request : Req} {answer : Ans}
    (stable : ImageFileStable state) (step : imageTSO.ans state i (.sys request) answer after)
    (preserves : request ≠ cloneReq →
      Kern.ans request (state.1.view i) answer (after.1.view i) →
        FileInv (state.1.view i) → FileInv (after.1.view i)) :
    ImageFileStable after := by
  have host := step.2
  change (if request = cloneReq then after = state ∧ ∃ id extra, answer = some (id, extra) ∧ id ≠ 0
    else Kern.ans request (state.1.view i) answer (after.1.view i) ∧ after.1.buf = state.1.buf) at host
  split at host
  · obtain ⟨rfl, _⟩ := host
    exact stable
  · rename_i notClone
    have outside : ∀ j store, store ∈ after.1.buf j → ∀ byte, byte < 8 →
        ∀ offset, offset < image.length →
          BitVec.ofNat 64 (BASE + offset) ≠ store.1 + BitVec.ofNat 64 byte := by
      rw [host.2]
      exact stable.buffers
    have visible := (fileInv_view_iff (stable.buffers i)).mpr stable.file
    exact ⟨(fileInv_view_iff (outside i)).mp (preserves notClone host.1 visible), outside⟩

/-- Both emitted futex operations preserve the actual runner file,
    regardless of pending writes in any thread. -/
theorem ImageFileStable.futex {state after : imageTSO.St} {i : Nat} {address value mode : W}
    {answer : Ans} (stable : ImageFileStable state) (host : ImageFutexAnswers)
    (emitted : mode = 128 ∨ mode = 129)
    (step : imageTSO.ans state i (.sys (futexReq address mode value)) answer after) :
    ImageFileStable after := by
  apply stable.sys step
  intro _ answered visible
  rw [(host.unchanged address mode value answer _ _ emitted answered).1]
  exact visible

/-- The actual emitted frame array and the world start after the mapped
    runner file. This bound is taken from the emitted layout. -/
theorem Emitted.runner_file_before_layout {src : String} {reserve : Nat} {options : Profil.Options}
    (output : Emitted src reserve options) :
    IMG ≤ output.image.fp0 ∧ IMG ≤ output.image.Y.lo := by
  obtain ⟨_, _, _, layout, _, _, _, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  have frameStart := layout.hfp
  have worldStart := layout.hylo
  simp only [codeBase] at frameStart
  omega

private theorem fileByte_before_image {offset : Nat} (loaded : offset < image.length) :
    (BitVec.ofNat 64 (BASE + offset)).toNat < IMG :=
  Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_trans (Nat.add_lt_add_left loaded BASE) image_fits)

/-- A returning plain gate preserves the mapped runner file by confining
    its writes to the emitted program's world. The agreement comes from
    the gate contract on the actual answer in the issuer's TSO view. -/
theorem ImageFileStable.plain_gate {D : Deklaration} {layout : Gabbro.Stage0.Senke.Lay D}
    {state after : imageTSO.St} {i : Nat} {request : Req} {answer : Ans}
    (stable : ImageFileStable state) (step : imageTSO.ans state i (.sys request) answer after)
    (above : IMG ≤ layout.lo)
    (kernelFrame : request ≠ cloneReq →
      Kern.ans request (state.1.view i) answer (after.1.view i) →
        KernW layout (state.1.view i) (after.1.view i)) :
    ImageFileStable after := by
  apply stable.sys step
  intro ordinary answered visible offset loaded
  obtain ⟨read, write, bytes⟩ := kernelFrame ordinary answered
  rw [read, write, bytes _ (fun inside => (Nat.not_le_of_lt (fileByte_before_image loaded)) (above.trans inside.1))]
  exact visible offset loaded

/-- The actual loader provides the read-only bytes. Empty initial buffers
    initialize the pending-write invariant without a host assumption. -/
theorem MappedImage.runnerFileStable {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {start : Cfg imageTSO Runner.X86.X}
    (mapped : MappedImage output start) : ImageFileStable start.ms := by
  refine ⟨mapped.runnerFile, ?_⟩
  intro i store pending
  rw [mapped.emptyBuffers i] at pending
  cases pending

/-- Before a slot has been allocated, it has no private TSO writes.
    Retired slots still belong to the allocated prefix. -/
def ImageIdleBuffers {θ : Type} (c : Cfg imageTSO θ) : Prop :=
  ∀ i, c.ths.length ≤ i → c.ms.1.buf i = []

private theorem other_buffer {before after : imageTSO.St} {owner other : Nat}
    {request : Op} {answer : Ans} (different : other ≠ owner)
    (answered : imageTSO.ans before owner request answer after) :
    after.1.buf other = before.1.buf other := by
  cases request with
  | rd => exact congrArg (fun s : imageTSO.St => s.1.buf other) answered.1.1
  | fp => exact congrArg (fun s : imageTSO.St => s.1.buf other) answered.1.1
  | wr =>
    obtain ⟨_, _, rfl⟩ | ⟨_, _, updated⟩ := answered.1
    · rfl
    · rw [updated]
      simp only [TSt.setBuf, ite_eq_right different]
  | cas =>
    obtain ⟨_, refused | accepted⟩ := answered.1
    · obtain ⟨_, _, rfl⟩ := refused
      rfl
    · obtain ⟨_, _, _, _, updated⟩ := accepted
      rw [updated]
  | sys request =>
    have host := answered.2
    change (if request = cloneReq then after = before ∧ ∃ id extra, answer = some (id, extra) ∧ id ≠ 0
      else Kern.ans request (before.1.view owner) answer (after.1.view owner) ∧
        after.1.buf = before.1.buf) at host
    split at host
    · rw [host.1]
    · rw [host.2]

/-- Every actual process step preserves the empty buffer at future
    slots. A successful clone can only extend the allocated prefix. -/
theorem ImageIdleBuffers.step {θ : Type} {act : θ → Res θ}
    {before after : Cfg imageTSO θ} {events : List Ev}
    (empty : ImageIdleBuffers before) (step : ProcessStep imageTSO act before events after) :
    ImageIdleBuffers after := by
  intro future unallocated
  have keep {owner : Nat} {thread : θ} {target : imageTSO.St} {request : Op} {answer : Ans}
      (found : before.ths[owner]? = some (some thread)) (outside : before.ths.length ≤ future)
      (answered : imageTSO.ans before.ms owner request answer target) : target.1.buf future = [] := by
    have different : future ≠ owner :=
      fun equal => Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp found).1 (equal ▸ outside)
    exact (other_buffer different answered).trans (empty future outside)
  cases step with
  | tau flushed =>
    obtain ⟨owner, _, _, _, queued, updated⟩ := flushed
    have clear := empty future unallocated
    have different : future ≠ owner := by
      intro same
      subst owner
      rw [clear] at queued
      cases queued
    rw [updated]
    simpa only [TSt.setBuf, ite_eq_right different] using clear
  | priv | exit =>
    exact empty future (by simpa only [List.length_set] using unallocated)
  | ask found _ _ answered _ =>
    exact keep found (by simpa only [List.length_set] using unallocated) answered
  | cloneNo found _ answered _ _ =>
    exact keep found (by simpa only [List.length_set] using unallocated) answered
  | @clone owner _ _ _ _ _ _ _ found _ answered _ _ _ =>
    have outside : before.ths.length ≤ future := by
      simp only [List.length_append, List.length_set, List.length_singleton] at unallocated
      exact (Nat.le_succ _).trans unallocated
    exact keep found outside answered

/-- Every future thread in a real run retains an empty buffer up to its
    allocation. The result covers both the runner and its IR process. -/
theorem ImageIdleBuffers.follow {θ : Type} {act : θ → Res θ}
    {before after : Cfg imageTSO θ} {events : List Ev} {count : Nat}
    (empty : ImageIdleBuffers before) (path : ProcessPrefix imageTSO act before events count after) :
    ImageIdleBuffers after := by
  induction path with
  | nil => exact empty
  | cons step _ ih => exact ih (empty.step step)

/-- The load establishes the future-thread buffer invariant. -/
theorem MappedImage.idle_buffers {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {start : Cfg imageTSO Runner.X86.X}
    (mapped : MappedImage output start) : ImageIdleBuffers start :=
  fun i _ => mapped.emptyBuffers i

/-- The next allocated slot sees exactly the shared memory, without
    forwarding writes from another thread's buffer. -/
theorem ImageIdleBuffers.fresh_view {θ : Type} {before : Cfg imageTSO θ}
    (empty : ImageIdleBuffers before) :
    before.ms.1.view before.ths.length = before.ms.1.m := by
  simp only [TSt.view, empty _ (Nat.le_refl _), List.foldl_nil]

end Gabbro.Stage0
