/-
  Lane-21 audit probe 3: the OLD event-to-world fold cannot change memory.

  Claim under test (pattern (c)): `weltenFalte` / `maschinenWelten` (§3) is
  documented as "event-to-world: the worlds a real run produces", but every
  world it produces carries the start world's slots and globals
  (`maschinenWelten_speicher_gleich` in the same file proves exactly this).
  That is: as a semantics it cannot change memory. The generated machine
  (§§7-11) escapes this shape by going through `execStmt`; this probe pins
  the negative fact for the OLD fold so the two are not confused.
-/
import Grammatik.Maschine

open Gabbro.Grammatik

variable {D : Deklaration}

/-- Any world of the OLD fold carries the start memory: restatement of the
    in-file theorem, kept here as the audit's checked witness that the OLD
    fold is memory-constant. -/
theorem audit21_old_fold_keeps_slots (M : MaschinenLauf (D := D))
    (W : World D) (hW : W ∈ maschinenWelten M) :
    W.slots = M.start.slots ∧ W.globs = M.start.globs :=
  maschinenWelten_speicher_gleich M W hW

/-- Corollary: no OLD-fold world differs in memory from the start world. -/
theorem audit21_old_fold_no_move (M : MaschinenLauf (D := D))
    (W : World D) (hW : W ∈ maschinenWelten M) :
    W.speicher = M.start.speicher := by
  obtain ⟨hslots, hglobs⟩ := maschinenWelten_speicher_gleich M W hW
  calc W.speicher = ⟨W.slots, W.globs⟩ := rfl
    _ = ⟨M.start.slots, M.start.globs⟩ := by rw [hslots, hglobs]
    _ = M.start.speicher := rfl

/-
CUTS:
- Positive direction (generated worlds DO move memory) is proved in-file by
  `gen_write_glob_moves` / `gen_welt_speicher_bewegt`; not re-demonstrated
  here (needs `execStmt` fireability witnesses).
- The audit judgement (OLD fold is not a semantics) follows from the
  `rfl`-level fact above plus the task's rule 4(c); Lean checks the fact,
  not the judgement.
-/
#print axioms audit21_old_fold_keeps_slots
#print axioms audit21_old_fold_no_move
