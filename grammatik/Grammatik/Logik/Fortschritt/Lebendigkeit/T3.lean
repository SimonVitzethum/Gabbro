/- Part 3 of 3 of `Lebendigkeit` (split by instrumente/teile/lean-teilen.py; the umbrella `Lebendigkeit.lean` imports all parts). -/
module
public import Grammatik.Logik.Fortschritt.Lebendigkeit.T2
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}


end Gabbro.Grammatik

/-! ## CUTS

  Proved (no premise beyond those named in the theorems):
  * `wartezeit_kern`, `wartezeit_schranke` -- the waiting bound on every
    scheduled run of G, with the bound `wartezeit` recursive over ranks.
  * `sperre_schritt`, `schritt_sperre_art`, `nimmt_an_sperre` -- G takes a lock
    only at a `locks` head of that lock, and only while it is free.
  * `abschnittAktiv_aus` -- a lock holder is never stuck except at a `locks`
    head, from progress and `HardwareImAbschnitt`.

  * `Haltezeit` is a premise here and a theorem of the checked program
    (`haltezeit_aus`, Halten/Haltezeit.lean, since 2026-11-13).

  NOT proved, named:
  * `Anwaerter` is a premise on the run; its static source (the threads whose
    call graph reaches `locks L`) is computed in the measurement, not
    proved to cover the run.
  * `LaufzeitAnnahme` and `HardwareImAbschnitt` are assumptions by design.
  * The bound counts SCHEDULER steps (G steps plus stutters), not cycles.
-/

#print axioms Gabbro.Grammatik.sperre_schritt
#print axioms Gabbro.Grammatik.schritt_sperre_art
#print axioms Gabbro.Grammatik.wartezeit_kern
#print axioms Gabbro.Grammatik.wartezeit_schranke

