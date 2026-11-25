/-
  File:      Core/Ziel/Review/Slice/NonTrivial.lean
  Subject:   NON-TRIVIALITY of the slice goal (Durchstich step 4): outside F_klein, and
             without acceptance, the legs fail — the slice goal says something.

  * Outside the slice: the atomic update `tausche` is not a slice instruction, although
    it shares the memory classes of the slice (`klein_aussen_verletzt`). Its class
    duty is violable: the lost update implements the same class but drops the value it
    read, breaking the simulation (`klein_simulation_verletzbar`, i.e. the existing
    `atomarSim_nichtTrivial`). Only the checker's refusal keeps it out of a program.
  * Without acceptance: `staleEinheit` is refused (`klein_nicht_akzeptiert`, i.e. the
    existing `stale_nicht_akzeptiert`), and it violates a leg every accepted unit owes:
    the authority duty `RegelLokal` (`klein_regel_verletzt_ohne_akzeptanz`, i.e. the
    existing `unbefugt_nicht_regel_lokal`). Hence the acceptance premise of
    `DurchstichKleinAussage` is not decoration.
-/
module

public import Core.Ziel.Review.Slice.Fragment
public import Core.Ast.Semantik.Runtime.Atom.Aussagen
public import Core.Ast.Semantik.Runtime.Klasse.Schritt
public import Core.Annahme.Annahme
public import Core.Annahme.Lokal

@[expose] public section

namespace Gabbro.Core.Ziel.Review.Slice

open Gabbro.Core
open Gabbro.Core.Ast.Semantik

/-- Outside the slice: the atomic update shares the memory classes but is excluded. -/
theorem klein_aussen_verletzt :
    ∃ z : Zugriffsform,
      ¬ KleinBefehl (.zugriff z) ∧ z.klasse = .rmw Speicher.Modus.na := by
  refine ⟨.tausche 0 0 0 0 (Ast.Ty.int 0 0) Speicher.Modus.na, ?_, rfl⟩
  simp only [KleinBefehl, not_false_eq_true]

/-- The simulation leg is violable at the excluded class: the lost update reads like
    an atomic update but binds `0`, so it is not faithful to the class step. -/
theorem klein_simulation_verletzbar :
    ∃ F : Schrittform, F.klasse.liest = true ∧ ¬ AtomarTreu F F.verloren :=
  atomarSim_nichtTrivial

/-- Without acceptance a leg fails: the refused unit breaks the authority duty. -/
theorem klein_regel_verletzt_ohne_akzeptanz :
    ¬ Annahme.RegelLokal Annahme.staleEinheit () :=
  Annahme.unbefugt_nicht_regel_lokal

/-- The refused unit exists, so the acceptance premise of the slice goal matters. -/
theorem klein_nicht_akzeptiert : ¬ Annahme.Akzeptiert Annahme.staleEinheit :=
  Annahme.stale_nicht_akzeptiert

end Gabbro.Core.Ziel.Review.Slice
