module

public import Grammatik.Logik.Vertraege.Pruefer.Goal
public import Grammatik.Logik.Fortschritt.KostenG
public import Grammatik.Zielsatz.Atomar.BeweisAtomar

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

variable {D : Deklaration}

/-- A designated entry is the first declared root, cannot occur at
    another root, and cannot be targeted by an ordinary call. The
    indirect gate refuses every signature that could select this entry. -/
def oneShotEntryB [DecidableEq D.Fn] (E : Einheit D) (functions : List D.Fn) (entry : D.Fn) : Bool :=
  E.starts.head?.any (fun root => decide (root.1 = entry)) &&
  (E.starts.drop 1 ++ E.gestartet).all (fun root => decide (root.1 ≠ entry)) &&
  functions.all (fun fn =>
    rufeE (fun callee => decide (callee ≠ entry)) (fun signature => !(D.passt entry signature))
      true (E.P.rumpf fn))

theorem oneShotEntry_parts [DecidableEq D.Fn] {E : Einheit D} {functions : List D.Fn} {entry : D.Fn}
    (checked : oneShotEntryB E functions entry = true) :
    (∃ root, E.starts.head? = some root ∧ root.1 = entry) ∧
    (∀ root ∈ E.starts.drop 1 ++ E.gestartet, root.1 ≠ entry) ∧
    (∀ fn ∈ functions, rufeE (fun callee => decide (callee ≠ entry))
      (fun signature => !(D.passt entry signature)) true (E.P.rumpf fn) = true) := by
  obtain ⟨top, calls⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨head, other⟩ := Bool.and_eq_true_iff.mp top
  refine ⟨?_, fun root member => of_decide_eq_true (List.all_eq_true.mp other root member),
    fun fn member => List.all_eq_true.mp calls fn member⟩
  cases found : E.starts.head? with
  | none => simp only [found, Option.any, Bool.false_eq_true] at head
  | some root => exact ⟨root, rfl, of_decide_eq_true (by simpa only [found, Option.any] using head)⟩

/-- The startup thread receives the declared initial memory. Every
    worker has a prepared frame and remains dormant. -/
abbrev entryStart (E : Einheit D) : FadenMaschine D.mitRuhe :=
  FadenStart E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts) (fun thread => decide (thread = 0))

/-- A prefix before activating any worker consists of actual GX steps
    by the sole startup thread. It may call ordinary functions. -/
inductive EntryPrefix [DecidableEq D.Fn] (E : Einheit D) (O : Orakel D) (passes : Nat) : FadenMaschine D.mitRuhe → Prop
  | start : EntryPrefix E O passes (entryStart E)
  | step {before : FadenMaschine D.mitRuhe} (after : RufMaschineG D.mitRuhe) :
      EntryPrefix E O passes before →
      RufSchrittGX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws) before.m 0 after →
      EntryPrefix E O passes { before with m := after }

theorem EntryPrefix.only_entry [DecidableEq D.Fn] {E : Einheit D} {O : Orakel D} {passes : Nat}
    {state : FadenMaschine D.mitRuhe} (run : EntryPrefix E O passes state) :
    (∀ thread, state.lebt thread = true ↔ thread = 0) ∧ (∀ thread, state.wartet thread = []) := by
  induction run with
  | start =>
    refine ⟨?_, fun _ => rfl⟩
    intro thread
    change decide (thread = 0) = true ↔ thread = 0
    exact ⟨of_decide_eq_true, decide_eq_true⟩
  | step _ _ _ prior => exact prior

theorem EntryPrefix.reachable [DecidableEq D.Fn] {E : Einheit D} {O : Orakel D} {passes : Nat}
    {state : FadenMaschine D.mitRuhe} (run : EntryPrefix E O passes state) :
    FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws) (entryStart E) state := by
  induction run with
  | start => exact .start
  | @step before after earlier step reached =>
    have only := earlier.only_entry
    exact .schritt _ _ reached (.lauf before 0 after ((only.1 0).mpr rfl) (only.2 0) step)

/-- The entry can update the shared store but leaves every dormant
    worker's prepared function and saved arguments untouched. -/
theorem EntryPrefix.dormant_thread [DecidableEq D.Fn] {E : Einheit D} {O : Orakel D} {passes : Nat}
    {state : FadenMaschine D.mitRuhe} (run : EntryPrefix E O passes state)
    {worker : Faden} (different : worker ≠ 0) :
    state.m.faeden worker = (entryStart E).m.faeden worker := by
  induction run with
  | start => rfl
  | step _ _ moved previous => exact (gx_fremd moved worker different).trans previous

/-- Activate one frame reserved by startup. The machine store is
    inherited from the state immediately before activation. -/
def activateBootWorker (before : FadenMaschine D) (worker : Faden) : FadenMaschine D :=
  { before with
    lebt := fun thread => if thread = worker then true else before.lebt thread
    rang := fun thread => if thread = worker then before.rang 0 + 1 else before.rang thread
    uhr := before.uhr + 1 }

theorem activateBootWorker_step {P : Programm D} {O : Orakel D} {passes : Nat}
    {Tg : D.Tab ⊕ D.Glob → Prop} {before : FadenMaschine D} {worker : Faden}
    (live : before.lebt 0 = true) (ready : before.wartet 0 = []) (dormant : before.lebt worker = false) :
    FadenSchrittX P O passes Tg before (activateBootWorker before worker) :=
  .kind before 0 worker live ready dormant

/-- Boot creates worker slots one at a time in the order of the image's
    start list. Each activation keeps the store and all prepared frames. -/
def activateBootWorkers (before : FadenMaschine D) (workers : List Faden) : FadenMaschine D :=
  workers.foldl activateBootWorker before

theorem activateBootWorkers_fields (before : FadenMaschine D) (workers : List Faden) :
    let after := activateBootWorkers before workers
    after.m = before.m ∧ after.wartet = before.wartet ∧
      ∀ thread, after.lebt thread = true ↔ thread ∈ workers ∨ before.lebt thread = true := by
  induction workers generalizing before with
  | nil =>
    intro after
    exact ⟨rfl, rfl, fun thread => by simp [after, activateBootWorkers]⟩
  | cons worker rest ih =>
    obtain ⟨memory, waiting, live⟩ := ih (activateBootWorker before worker)
    refine ⟨memory, waiting, fun thread => ?_⟩
    change (activateBootWorkers (activateBootWorker before worker) rest).lebt thread = true ↔ _
    rw [live, List.mem_cons]
    by_cases same : thread = worker
    · simp only [activateBootWorker, same, ite_true, or_true, true_or]
    · simp only [activateBootWorker, same, ite_false, false_or]

/-- Every startup activation is an actual GX transition, even when
    multiple occurrences of the same function have distinct arguments. -/
theorem activateBootWorkers_reachable {P : Programm D} {O : Orakel D} {passes : Nat}
    {Tg : D.Tab ⊕ D.Glob → Prop} {start before : FadenMaschine D} (workers : List Faden)
    (reached : FadenErreichbarX P O passes Tg start before)
    (entry : before.lebt 0 = true) (waiting : before.wartet 0 = [])
    (unique : workers.Nodup) (dormant : ∀ thread ∈ workers, before.lebt thread = false) :
    FadenErreichbarX P O passes Tg start (activateBootWorkers before workers) := by
  induction workers generalizing before with
  | nil => exact reached
  | cons worker rest ih =>
    obtain ⟨absent, remaining⟩ := List.nodup_cons.mp unique
    have head := dormant worker List.mem_cons_self
    have step := activateBootWorker_step (P := P) (O := O) (passes := passes) (Tg := Tg)
      entry waiting head
    change FadenErreichbarX P O passes Tg start (activateBootWorkers (activateBootWorker before worker) rest)
    refine ih (.schritt _ _ reached step) (by simp only [activateBootWorker, entry, ite_self])
      waiting remaining ?_
    · intro thread member
      have different : thread ≠ worker := fun equal => absent (equal ▸ member)
      simpa only [activateBootWorker, different, ite_false] using dormant thread (List.mem_cons_of_mem _ member)

/-- When the once-only entry returns, the first worker activates in
    the store it left. Its code and initial arguments are still the
    declared ones, and the complete startup prefix is a GX execution. -/
theorem EntryPrefix.activate_after_return [DecidableEq D.Fn] {E : Einheit D} {O : Orakel D} {passes : Nat}
    {before : FadenMaschine D.mitRuhe} (run : EntryPrefix E O passes before)
    (returned : FertigG before.m 0) {worker : Faden} {start : Σ f : D.Fn, Env D (D.params f)}
    (different : worker ≠ 0) (declared : E.starts[worker]? = some start) :
    let after := activateBootWorker before worker
    FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (entryStart E) after ∧
    FertigG after.m 0 ∧ after.lebt worker = true ∧ after.m.speicher = before.m.speicher ∧
    after.m.faeden worker = (entryStart E).m.faeden worker ∧
    initRuhe E.starts worker = ⟨some start.1, envR start.2⟩ := by
  intro after
  have only := run.only_entry
  have dormant : before.lebt worker = false := Bool.eq_false_iff.mpr (fun live => different ((only.1 worker).mp live))
  refine ⟨.schritt _ _ run.reachable (activateBootWorker_step ((only.1 0).mpr rfl) (only.2 0) dormant),
    returned, ?_, rfl, run.dormant_thread different, ?_⟩
  · simp only [after, activateBootWorker, ite_true]
  · simp only [initRuhe, declared]

/-- Startup can activate the complete ordered worker list after return.
    It consumes the same entry prefix and preserves each worker's own
    declared frame, even when several roots name the same function. -/
theorem EntryPrefix.activate_declared_workers [DecidableEq D.Fn] {E : Einheit D} {O : Orakel D} {passes : Nat}
    {before : FadenMaschine D.mitRuhe} (run : EntryPrefix E O passes before)
    (returned : FertigG before.m 0) :
    let workers := List.range' 1 (E.starts.length - 1)
    let after := activateBootWorkers before workers
    FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (entryStart E) after ∧
    FertigG after.m 0 ∧ after.m.speicher = before.m.speicher ∧
    ∀ thread, thread ∈ workers ↔
      thread ≠ 0 ∧ after.lebt thread = true ∧
        after.m.faeden thread = (entryStart E).m.faeden thread ∧
        ∃ root, E.starts[thread]? = some root ∧ initRuhe E.starts thread = ⟨some root.1, envR root.2⟩ := by
  intro workers after
  have only := run.only_entry
  have bounds (thread : Faden) (member : thread ∈ workers) : 1 ≤ thread ∧ thread < 1 + (E.starts.length - 1) :=
    List.mem_range'_1.mp member
  have positive (thread : Faden) (member : thread ∈ workers) : thread ≠ 0 := by
    exact Nat.ne_of_gt ((bounds thread member).1 : 0 < thread)
  have distinct : workers.Nodup := List.nodup_range'
  have dormant (thread : Faden) (member : thread ∈ workers) : before.lebt thread = false :=
    Bool.eq_false_iff.mpr (fun live => positive thread member ((only.1 thread).mp live))
  obtain ⟨machine, _, live⟩ := activateBootWorkers_fields before workers
  refine ⟨activateBootWorkers_reachable workers run.reachable ((only.1 0).mpr rfl) (only.2 0) distinct dormant,
    machine.symm ▸ returned, congrArg RufMaschineG.speicher machine, fun thread => ?_⟩
  constructor
  · intro member
    have different := positive thread member
    have declared : thread < E.starts.length := by
      have lower : 1 ≤ (thread : Nat) := (bounds thread member).1
      have upper : (thread : Nat) < 1 + (E.starts.length - 1) := (bounds thread member).2
      omega
    have found := List.getElem?_eq_getElem declared
    exact ⟨different, (live thread).mpr (.inl member),
      machine.symm ▸ run.dormant_thread different,
      E.starts[thread], found, by simp only [initRuhe, found]⟩
  · rintro ⟨different, started, _, _⟩
    exact ((live thread).mp started).resolve_right (fun old => different ((only.1 thread).mp old))

/-- The whole goal applies throughout the actual model prefix, starting
    from the declared store, before any cloned worker can take a step. -/
theorem EntryPrefix.goal [DecidableEq D.Fn] {E : Einheit D} {O : Orakel D} {passes : Nat}
    {state : FadenMaschine D.mitRuhe}
    (run : EntryPrefix E O passes state)
    (functions : Aufzaehlung D.Fn) (locks : Aufzaehlung D.Lock) (carriers : Aufzaehlung (D.Tab ⊕ D.Glob))
    (accepted : akzeptiertX_pruefer.akzeptiert E functions.1 locks.1 carriers.1 = true)
    (calls : CallSitePflicht E) (posts : PostDeckt E) (foreign : ForeignVertrag E O)
    (hardware : HardwareAnnahmenHw O E.Q) :
    ZielFX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws) (entryStart E).m
      (E.arenen.map (·.mitRuhe)) state := by
  exact gabbro_ziel akzeptiertX_pruefer _ E functions locks carriers accepted
    (nutzerPflicht_of_akzeptiert functions locks accepted) calls posts O foreign hardware
    passes _ _ (laufzeit_initRuhe E) _ _ run.reachable

end Gabbro.Grammatik.Zielsatz
