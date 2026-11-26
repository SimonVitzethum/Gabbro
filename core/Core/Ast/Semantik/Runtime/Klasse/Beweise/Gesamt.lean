/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/Gesamt.lean
  Subject:   THE PINNED STATEMENT OF ALL SEVEN CLASS DUTIES, CLOSED (MK-03). `KlassenAussagen` collects one
              statement per effect class: simulation, step-level information flow, bounds, safety, progress,
              locality, non-triviality and cost with hold. Each conjunct is proved in its own module; this file only assembles
              them, once for every class. Information flow is the step-level statement
              `KlassenSchrittNIAussage`: two steps of the same class form from publicly equal states end
              publicly equal. The run-level form was not derivable from its premises and is gone from the
              model; its generic run composition stays in the fragment NI machinery.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.NISichtbar
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Schranken
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Sicherheit
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Kosten

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Beobachtung

/-- **All seven duties of every class** (`KlassenAussagen`), assembled from the per-duty proofs:
    `klassenSim`, `klassenSchrittNI`, `klassenSchranken`, `klassenSicherheit`, `klassenFortschritt`,
    `klassenLokal`, `klassenNichtTrivial` and `klassenKosten`. -/
theorem klassenAussagen : KlassenAussagen := by
  intro k
  exact ⟨klassenSim k, klassenSchrittNI k, klassenSchranken k,
    klassenSicherheit k, klassenFortschritt k, klassenLokal k, klassenNichtTrivial k,
    klassenKosten k⟩

end Gabbro.Core.Ast.Semantik
