/-
  Audit 46, probe F1: every lock successor world keeps `M.speicher` (no Rahmen).

  Claim (pattern c-adjacent, filed as informational): the new-step frame inside
  `kette_zwei_schritt` (KetteMehrfadenC.lean) closes by `rfl` because BOTH
  worlds are built over the SAME `M.speicher` -- `vor` by `hvor` (the last
  machine world is `M.speicher.welt ...`), `nach` by `hnach` (the appended
  world is `M.speicher.welt ...`). The `Rahmen` halves are slot/global
  equalities over one fixed memory, so the frame duty is vacuous: it can hold
  only because no lock step ever writes. `blatt` steps (memory-changing,
  through `execStmt`) stay owed -- booked in the file CUTS.

  Demonstrated below, from the DEFINITIONS only (no import of the audited
  file's theorems needed beyond the shared shape): for ANY memory `s` and any
  two traces, `Rahmen` between `s.welt e1` and `s.welt e2` holds by `rfl` at
  each projection -- the frame proof never inspects which lock event fired.
-/
import Grammatik.Maschine

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- Any two worlds over the SAME memory satisfy `Rahmen` for ANY footprint:
    the frame proof is `rfl` at each projection and never reads the events. -/
theorem audit46_lock_frame_is_rfl
    (s : Speicher D) (e1 e2 : List (Ereignis D))
    (W : D.Tab → Bool) (G : D.Glob → Bool) :
    Rahmen W G (s.welt e1) (s.welt e2) := by
  refine ⟨?_, ?_⟩
  · intro t _ k fld
    rfl
  · intro x _
    rfl

/-- The two lock successor shapes from `LockSchrittGedecktBei` share their
    memory with the prefix machine by CONSTRUCTION: both are `M.speicher.welt`,
    so the frame between them is the lemma above, never `execStmt`. -/
example (M : GenMaschine D) (f0 : Faden) (L : D.Lock)
    (W : D.Tab → Bool) (G : D.Glob → Bool) :
    Rahmen W G (M.speicher.welt (M.spuren f0))
      (M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f0)) :: M.spuren f0)) :=
  audit46_lock_frame_is_rfl M.speicher _ _ W G

/-
CUTS:
- This probe shows the lock-step frame is definitionally vacuous; it does not
  claim anything about `blatt` steps, whose frame must go through `execStmt`
  (`blatt_rahmen_schritt`) and is NOT covered by `kette_zwei_schritt`.
- No premise is discarded: every binder above is used by the proof.
-/
#print axioms Gabbro.Grammatik.audit46_lock_frame_is_rfl
