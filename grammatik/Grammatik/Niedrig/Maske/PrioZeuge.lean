/-
  File:      Grammatik/Niedrig/Maske/PrioZeuge.lean
  Subject:   WITNESS FOR PRIORITY NESTING (L7b): one core; thread level 0;
    a level-1 handler enters; a level-3 handler preempts it; a level-2
    attempt is refused (not above 3); the level-3 handler leaves; now
    level-2 may enter; all leave; the final state is the initial state,
    pointwise by `rfl`. The entry mask bit is witnessed for both values.
-/
module

public import Grammatik.Niedrig.Maske.PrioSaetze

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Maske

/-- The fixture mask: one unmasked core, nothing running. -/
def wMask0 : CoreMask :=
  { zustand := fun _ =>
    { maskiert := false
      tiefe := 0
      stapel := [] } }

/-- The fixture start: thread level 0 with an empty stack. -/
def w0 : PrioMaske :=
  { maske := wMask0
    prio := anfangPrio }

/-- Level 1 enters with the mask left clear. -/
def w1 : PrioMaske :=
  erhoeheNach w0 0 1 false

/-- Step one: the level-1 handler enters. -/
theorem wSchritt1 : PrioStep (PrioEvent.erhoehe 0 1 false) w0 w1 :=
  PrioStep.erhoehe w0 0 1 false rfl (by decide) (by decide)

/-- Level 3 preempts level 1. -/
def w2 : PrioMaske :=
  erhoeheNach w1 0 3 false

/-- Step two: the level-3 handler preempts. -/
theorem wSchritt2 : PrioStep (PrioEvent.erhoehe 0 3 false) w1 w2 :=
  PrioStep.erhoehe w1 0 3 false rfl (by decide) (by decide)

/-- Refused: level 2 is not above the running level 3. -/
theorem wVerweigert2 (s' : PrioMaske) :
    ¬ PrioStep (PrioEvent.erhoehe 0 2 false) w2 s' :=
  fun h => keinEintrittKlein w2 s' 0 2 false (by decide) h

/-- Level 3 leaves, back to level 1. -/
def w3 : PrioMaske :=
  senkeNach w2 0 1 [0]

/-- Step three: the level-3 handler leaves. -/
theorem wSchritt3 : PrioStep (PrioEvent.senke 0) w2 w3 :=
  PrioStep.senke w2 0 1 [0] rfl

/-- Level 2 enters over level 1. -/
def w4 : PrioMaske :=
  erhoeheNach w3 0 2 false

/-- Step four: level 2 may now enter. -/
theorem wSchritt4 : PrioStep (PrioEvent.erhoehe 0 2 false) w3 w4 :=
  PrioStep.erhoehe w3 0 2 false rfl (by decide) (by decide)

/-- Level 2 leaves, back to level 1. -/
def w5 : PrioMaske :=
  senkeNach w4 0 1 [0]

/-- Step five: level 2 leaves. -/
theorem wSchritt5 : PrioStep (PrioEvent.senke 0) w4 w5 :=
  PrioStep.senke w4 0 1 [0] rfl

/-- Level 1 leaves, back to thread level. -/
def w6 : PrioMaske :=
  senkeNach w5 0 0 []

/-- Step six: level 1 leaves. -/
theorem wSchritt6 : PrioStep (PrioEvent.senke 0) w5 w6 :=
  PrioStep.senke w5 0 0 [] rfl

/-- Entering with `maskNeu = true` sets the mask bit (by `rfl`). -/
theorem wMaskeWahr :
    ((erhoeheNach w0 0 1 true).maske.zustand 0).maskiert = true :=
  rfl

/-- Entering with `maskNeu = false` leaves the core unmasked (by `rfl`). -/
theorem wMaskeFalsch :
    ((erhoeheNach w0 0 1 false).maske.zustand 0).maskiert = false :=
  rfl

/-- The end state is the initial state, pointwise. -/
theorem wEndePrio :
    ((w6.prio 0).aktuell = 0 ∧ (w6.prio 0).unterbrochen = [] ∧
      (w6.maske.zustand 0).maskiert = false) :=
  ⟨rfl, rfl, rfl⟩

#print axioms Gabbro.Grammatik.Niedrig.Maske.wSchritt1
#print axioms Gabbro.Grammatik.Niedrig.Maske.wVerweigert2
#print axioms Gabbro.Grammatik.Niedrig.Maske.wEndePrio

end Gabbro.Grammatik.Niedrig.Maske
