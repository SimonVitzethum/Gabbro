/-
  File:      Grammatik/Bibliothek.lean
  Subject:   LIBRARY CALLS (lane E2, PLAN-ERWEITUNG.md section 6) -- a
             run-time library function is an `Ax` whose parameter list is
             the ordinary parameters with the payload type appended.
             No new statement constructor: the call IS an `axiomCall`.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

/-- A run-time library function (PLAN-ERWEITUNG.md section 6, lane E2):
    ordinary parameters, a payload type (a table or tree type on the
    checker side; one more parameter here), and declared effects. -/
structure BibliotheksFunktion (D : Deklaration) where
  params : List Ty
  nutzlast : Ty
  schreibt : D.Tab → Bool
  gschreibt : D.Glob → Bool

/-- The axiom serving a library function: its parameter list is the
    ordinary parameters with the payload appended, it returns nothing,
    and its declared effects agree with the library function's. -/
def DientBibliothek (D : Deklaration) (L : BibliotheksFunktion D)
    (a : D.Ax) : Prop :=
  D.aparams a = L.params ++ [L.nutzlast] ∧ D.aerg a = none ∧
  (∀ t, D.aschreibt a t = L.schreibt t) ∧
  ∀ g, D.agschreibt a g = L.gschreibt g

/-!
CUTS:
- Only the declaration shape above; the obligation equivalence
  (`bibliotheksruf_ist_ax`) and its rule-13 witness are still owed.
-/

end Gabbro.Grammatik
