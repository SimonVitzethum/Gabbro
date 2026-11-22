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
