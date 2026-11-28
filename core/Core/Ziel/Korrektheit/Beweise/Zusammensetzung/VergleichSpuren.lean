module

public import Core.Ziel.Korrektheit.Beweise2.ZielNI
public import Core.Ziel.Korrektheit.Beweise2.Spracheinheit
import Core.Linken.NI

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

theorem vergleichSpuren_herkunft {E : Ast.Semantik.Einheit} (herkunft : EinheitHerkunft E)
    (accepted : Annahme.Quelle.Akzeptiert E) :
    ∀ {H₁ H₂ : Katalog.Umgebung} {ρ₁ ρ₂ : Maschine.Lauf E},
      Beobachtung.Vergleich E H₁ H₂ ρ₁ ρ₂ →
      Beobachtung.NiedrigAequiv E (Beobachtung.NiedrigeBeob E ρ₁) (Beobachtung.NiedrigeBeob E ρ₂) := by
  cases herkunft with
  | quelle P t => exact Linken.vergleichSpuren_quelle P t accepted
  | mitInvarianten P u =>
    let p := Ast.Semantik.programmMitInvarianten u
    apply Linken.nichtinterferent_zu_vergleich
    by_cases rein : p.Rein
    · exact Beobachtung.fragment_nichtinterferent p P rein accepted.regeln
    · have classes : p.KlassenRein := Ast.Semantik.programm_klassenrein u.baum
      exact zugriffNIFragment p P ⟨classes, rein⟩ accepted.regeln
  | verlinkt plan p linked => exact Linken.vergleichSpuren_verlinkt plan p linked accepted

/-- Source acceptance supplies the whole-unit origin for every admitted comparison. -/
theorem vergleichSpuren : VergleichSpurenAussage := by
  intro E accepted
  exact vergleichSpuren_herkunft (akzeptiert_herkunft accepted) accepted

end Gabbro.Core.Ziel.Korrektheit
