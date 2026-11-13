/-
  File:      stage0/Stage0/Senke/Bild/Gleich/LesegleichEig.lean
  Subject:   Properties of the read-erasure equivalence (package P0): what the erasure keeps. The write accesses of a
             trace are unchanged (`schreib_spurOhneLese`: the race and lock legs of `Ziel`, which look at writes, see
             the same writes in both traces), and every kept event -- a write, taking a lock, an answer from outside
             -- is seen by `≈` (`weltGleich_nicht_*`): `≈` equates exactly what differs by reads.
-/
module
public import Stage0.Senke.Bild.Gleich.Lesegleich
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiG
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## 1. The write accesses -/

/-- **The write accesses of a trace are unchanged by the erasure** (only reads may vanish): the race and lock legs of
    `Ziel` that look at writes see the same writes in both traces. -/
theorem schreib_spurOhneLese (c : D.Tab ⊕ D.Glob) : ∀ s : List (Ereignis D),
    (c, true) ∈ (spurOhneLese s).filterMap zugriffVon ↔ (c, true) ∈ s.filterMap zugriffVon
  | [] => Iff.rfl
  | e :: s => by
      have ih := schreib_spurOhneLese c s
      cases e with
      | zugriff t w Λ hl =>
          cases w
          · rw [spurOhneLese_cons_lese (.zugriff t false Λ hl) rfl s, ih]
            show _ ↔ (c, true) ∈ (Sum.inl t, false) :: s.filterMap zugriffVon
            rw [List.mem_cons]
            constructor
            · exact Or.inr
            · rintro (h | h)
              · simp at h
              · exact h
          · rw [spurOhneLese_cons_bleibt (.zugriff t true Λ hl) rfl s]
            show (c, true) ∈ (Sum.inl t, true) :: (spurOhneLese s).filterMap zugriffVon ↔
              (c, true) ∈ (Sum.inl t, true) :: s.filterMap zugriffVon
            rw [List.mem_cons, List.mem_cons, ih]
      | gzugriff g w Λ hl =>
          cases w
          · rw [spurOhneLese_cons_lese (.gzugriff g false Λ hl) rfl s, ih]
            show _ ↔ (c, true) ∈ (Sum.inr g, false) :: s.filterMap zugriffVon
            rw [List.mem_cons]
            constructor
            · exact Or.inr
            · rintro (h | h)
              · simp at h
              · exact h
          · rw [spurOhneLese_cons_bleibt (.gzugriff g true Λ hl) rfl s]
            show (c, true) ∈ (Sum.inr g, true) :: (spurOhneLese s).filterMap zugriffVon ↔
              (c, true) ∈ (Sum.inr g, true) :: s.filterMap zugriffVon
            rw [List.mem_cons, List.mem_cons, ih]
      | nimmt L hl =>
          rw [spurOhneLese_cons_bleibt (.nimmt L hl) rfl s]
          exact ih
      | gibt L =>
          rw [spurOhneLese_cons_bleibt (.gibt L) rfl s]
          exact ih
      | fremd q =>
          rw [spurOhneLese_cons_bleibt (.fremd q) rfl s]
          exact ih


/-! ## 2. What `≈` does NOT equate: every kept event is seen -/

/-- **A kept event is never erased**: a world is not `≈` to itself with one more non-read event on top. -/
theorem weltGleich_nicht_merke (σ : World D) (e : Ereignis D) (he : istLeseEv e = false) :
    ¬ WeltGleich σ (σ.merke [e]) := by
  intro h
  have hl := congrArg List.length h.spur
  have e' : spurOhneLese (σ.merke [e]).spur = e :: spurOhneLese σ.spur := spurOhneLese_cons_bleibt e he σ.spur
  rw [e', List.length_cons] at hl
  omega

/-- An answer from outside (`fremd`) is seen. -/
theorem weltGleich_nicht_fragt (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : ¬ WeltGleich σ (σ.fragt q) :=
  weltGleich_nicht_merke σ (.fremd q) rfl

/-- Taking a lock is seen. -/
theorem weltGleich_nicht_nimmt (σ : World D) (L : D.Lock) : ¬ WeltGleich σ (σ.nimmt L) :=
  weltGleich_nicht_merke σ (.nimmt L σ.haelt) rfl

/-- A write is seen (also when it stores the value already there). -/
theorem weltGleich_nicht_schreibSlot (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) : ¬ WeltGleich σ (σ.schreibSlot t Λ k f v) := by
  intro h
  have hl := congrArg List.length h.spur
  have e' : spurOhneLese (σ.schreibSlot t Λ k f v).spur =
      Ereignis.zugriff t true Λ σ.haelt :: spurOhneLese σ.spur :=
    spurOhneLese_cons_bleibt (.zugriff t true Λ σ.haelt) rfl σ.spur
  rw [e', List.length_cons] at hl
  omega

end Gabbro.Stage0.Senke.BildLauf
