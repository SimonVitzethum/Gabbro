module

public import Core.Beobachtung.Fluss.Beschriftung.Beweise.Entscheidung
public import Core.Beobachtung.Fluss.Beschriftung.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Beobachtung

theorem endlicheFlussAussage_erfuellbar :
    ∃ t : EndlicheBeschriftung, gutFragment.pruefeFluss t = true ∧
      oeffentlich (t.deutung.lokal 0 0) = false ∧
      (rahmenGeheim false).sicht t.deutung = (rahmenGeheim true).sicht t.deutung ∧
      rahmenGeheim false ≠ rahmenGeheim true := by
  let t : EndlicheBeschriftung :=
    ⟨fun pc => if 1 ≤ pc then [geheim] else [], fun _ => [geheim], ∅⟩
  have gleich : t.deutung = gutBeschriftung := by
    simp only [t, EndlicheBeschriftung.deutung, gutBeschriftung, Beschriftung.mk.injEq]
    refine ⟨?_, ?_, trivial⟩
    · funext pc s
      cases s with
      | zero =>
        by_cases h : 1 ≤ pc <;>
          simp only [t, EndlicheBeschriftung.deutung, etikettAn, gutBeschriftung,
            true_and, h, if_true, if_false, List.getElem?_cons_zero,
            List.getElem?_nil, Option.getD_some, Option.getD_none]
      | succ s =>
        simp only [t, EndlicheBeschriftung.deutung, etikettAn, gutBeschriftung,
          Nat.succ_ne_zero, false_and, if_false]
        split <;> rfl
    · funext pc i
      cases i <;> rfl
  refine ⟨t, endlicheFlussAussage_beweis _ _ |>.mpr (gleich.symm ▸ gut_akzeptiert),
    geheim_verborgen, sicht_geheim t.deutung geheim_verborgen _ _, ?_⟩
  intro eq
  have h := congrArg Rahmen.lokale eq
  cases h

end Gabbro.Core.Ast.Semantik
