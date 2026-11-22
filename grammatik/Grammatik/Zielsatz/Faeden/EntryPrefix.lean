module

public import Grammatik.Logik.Vertraege.Pruefer.Goal
public import Grammatik.Logik.Fortschritt.KostenG

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
def entryStart (E : Einheit D) : FadenMaschine D.mitRuhe :=
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
    exact decide_eq_true_eq
  | step _ _ _ prior => exact prior

theorem EntryPrefix.reachable [DecidableEq D.Fn] {E : Einheit D} {O : Orakel D} {passes : Nat}
    {state : FadenMaschine D.mitRuhe} (run : EntryPrefix E O passes state) :
    FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws) (entryStart E) state := by
  induction run with
  | start => exact .start
  | @step before after earlier step reached =>
    have only := earlier.only_entry
    exact .schritt _ _ reached (.lauf before 0 after ((only.1 0).mpr rfl) (only.2 0) step)

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
