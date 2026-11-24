module

public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment)

/-- The selected loader row yields the canonical initial state of this fragment. -/
theorem fragment_geladen (p : Fragment) (plattform : Plattform) {h : Umgebung}
    {s : AussenStart} (hardware : Hardware (p.einheit plattform).katalog h)
    (zul : (p.einheit plattform).ZulStart h s) :
    (p.einheit plattform).laden s (h.lade (p.einheit plattform).bild) =
      some (I.start (p.einheit plattform) s).2 := by
  have gueltig : Ast.Semantik.bild.gueltig h.ziel := hardware.ziel.symm ▸ zul.1
  have zeile := hardware.lader Ast.Semantik.bild gueltig
  have start : (h.lade Ast.Semantik.bild).starts 0 = some 0 := lader_start zeile 0
  have byte : (h.lade Ast.Semantik.bild).bytes 0 = some 0 := (zeile.2.1 0 0 rfl).2
  change Ast.Semantik.laden p.eingang plattform s (h.lade Ast.Semantik.bild) = _
  rw [Ast.Semantik.laden, if_pos ⟨start, byte⟩]
  rfl

theorem fragment_lader_ni (p : Fragment) (plattform : Plattform)
    (quelle : StartFlussLokal (p.einheit plattform)) : LaderNIPflicht (p.einheit plattform) := by
  intro h₁ h₂ s₁ s₂ hw₁ hw₂ zul₁ zul₂ _ start
  rw [LaderSicht, LaderSicht, fragment_geladen p plattform hw₁ zul₁,
    fragment_geladen p plattform hw₂ zul₂]
  exact congrArg some (funext (quelle s₁ s₂ start).2.2.1)

end Gabbro.Core.Beobachtung
