module

public import Core.Ziel.Korrektheit.Beweise2.ZielNI
public import Core.Ziel.Korrektheit.Beweise2.Spracheinheit
import Core.Ziel.Korrektheit.Beweise.Zusammensetzung.BegleitZusammensetzung
import Core.Ziel.Korrektheit.Beweise.Zusammensetzung.NICounterexample
import Core.Beobachtung.Fluss.Beschriftung.Leck
import Core.Linken.NI
import Core.Sicherheit.Laufkonstruktion

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core Beobachtung Katalog

/-- The comparison-trace obligation outside the image of the three unit constructions.
    Source acceptance binds the ideal rule projections. A proof here would need to
    control the implementation loader, steps, and low projections of the actual unit. -/
def VergleichSpurenOhneHerkunftAussage : Prop :=
  ∀ (E : Ast.Semantik.Einheit), Annahme.Quelle.Akzeptiert E → ¬ EinheitHerkunft E →
    ∀ {H₁ H₂ : Katalog.Umgebung} {ρ₁ ρ₂ : Maschine.Lauf E},
      Beobachtung.Vergleich E H₁ H₂ ρ₁ ρ₂ →
      Beobachtung.NiedrigAequiv E (Beobachtung.NiedrigeBeob E ρ₁) (Beobachtung.NiedrigeBeob E ρ₂)

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

/-- Whole-unit constructions account for all the checked cases of the comparison obligation. -/
theorem vergleichSpuren_iff_ohneHerkunft :
    VergleichSpurenAussage ↔ VergleichSpurenOhneHerkunftAussage := by
  constructor
  · intro all E accepted _
    exact all E accepted
  · intro rest E accepted H₁ H₂ ρ₁ ρ₂ vergleich
    by_cases herkunft : EinheitHerkunft E
    · exact vergleichSpuren_herkunft herkunft accepted vergleich
    · exact rest E accepted herkunft vergleich

private def mitBootEingabe (E : Ast.Semantik.Einheit) (label : Nat → Etikett)
    (laden : AussenStart → Ladung → Option Ast.Semantik.Zustand) : Ast.Semantik.Einheit :=
  { E with laden, etiketten := { E.etiketten with bootByte := label } }

private theorem akzeptiert_mit_bootEingabe {E : Ast.Semantik.Einheit}
    (accepted : Annahme.Quelle.Akzeptiert E)
    (label : Nat → Etikett) (laden : AussenStart → Ladung → Option Ast.Semantik.Zustand)
    (startFluss : StartFlussLokal (mitBootEingabe E label laden)) :
    Annahme.Quelle.Akzeptiert (mitBootEingabe E label laden) := by
  let E' := mitBootEingabe E label laden
  let ideal (ρ : Maschine.I.Lauf E') : Maschine.I.Lauf E :=
    ⟨ρ.start, ρ.umgebung, ρ.hw, ρ.zeit, ρ.belegt⟩
  have laeuft (ρ : Maschine.I.Lauf E') (run : Maschine.I.Laeufe E' ρ) :
      Maschine.I.Laeufe E (ideal ρ) := run
  obtain ⟨⟨⟨catalog, authority, outside, flow, bounds, waits, isolation⟩, binding⟩, clauses, guards⟩ :=
    accepted
  refine ⟨⟨⟨catalog, authority, ?_, ⟨startFluss, flow.2⟩, ?_, waits, isolation⟩, binding⟩, ?_, ?_⟩
  · exact ⟨outside.1, ⟨outside.2.1, fun ρ run => outside.2.2 (ideal ρ) (laeuft ρ run)⟩⟩
  · exact ⟨fun {ρ} run => bounds.start (η := ideal ρ) (laeuft ρ run),
      fun i {ρ} run => bounds.regel i (η := ideal ρ) (laeuft ρ run),
      fun {ρ} run => bounds.protokoll (η := ideal ρ) (laeuft ρ run), bounds.bezug⟩
  · exact fun ρ run => clauses (ideal ρ) (laeuft ρ run)
  · exact ⟨fun ρ run => guards.1 (ideal ρ) (laeuft ρ run),
      fun ρ run => guards.2.1 (ideal ρ) (laeuft ρ run),
      fun ρ run => guards.2.2 (ideal ρ) (laeuft ρ run)⟩

private def bootBasis : Ast.Semantik.Einheit := einheitVon .x86_64 trivialUnit

private def bootLeck : Ast.Semantik.Einheit :=
  mitBootEingabe bootBasis (fun _ => Ast.Semantik.geheim) fun s image =>
    if (s.inputBytes 0).isSome then none else bootBasis.laden s image

private theorem bootLeck_akzeptiert : Annahme.Quelle.Akzeptiert bootLeck := by
  have accepted : Annahme.Quelle.Akzeptiert bootBasis :=
    (Annahme.Quelle.akzeptiert_elaboriert_iff .x86_64 trivialUnit).2 (trivialUnit_akzeptiert .x86_64)
  apply akzeptiert_mit_bootEingabe accepted
  intro s₁ s₂ low
  let angepasst : AussenStart := { s₂ with inputBytes := s₁.inputBytes }
  have basisLow : NiedrigGleich bootBasis s₁ angepasst := by
    exact congrArg (fun p =>
      (p.1, p.2.1, p.2.2.1, (fun a => (sichtbar (bootBasis.etiketten.bootByte a)
        (s₁.inputBytes a)).join), p.2.2.2.2)) low
  exact (Annahme.akzeptiert_fluss accepted.regeln).1 s₁ angepasst basisLow

private theorem bootLeck_ohneHerkunft : ¬ EinheitHerkunft bootLeck := by
  have boot_oeffentlich {E : Ast.Semantik.Einheit} (herkunft : EinheitHerkunft E) :
      oeffentlich (E.etiketten.bootByte 0) = true := by
    cases herkunft <;> exact Ast.Semantik.oeffentlich_leer
  intro herkunft
  exact Bool.false_ne_true (Ast.Semantik.geheim_verborgen.symm.trans (boot_oeffentlich herkunft))

private theorem bootLeck_vergleich :
    ∃ (H : Umgebung) (ρ₁ ρ₂ : Maschine.Lauf bootLeck),
      Vergleich bootLeck H H ρ₁ ρ₂ ∧
      ¬ NiedrigAequiv bootLeck (NiedrigeBeob bootLeck ρ₁) (NiedrigeBeob bootLeck ρ₂) := by
  let H := Sicherheit.Laufkonstruktion.umgebung Sicherheit.Laufkonstruktion.leer
  have hw : Hardware bootLeck.katalog H :=
    Sicherheit.Laufkonstruktion.erlaubt Sicherheit.Laufkonstruktion.leer
  obtain ⟨start, zul⟩ := zulStart_erfuellbar hw Sicherheit.Laufkonstruktion.bild_gueltig
  let region : Strecke := ⟨0, 1⟩
  let s₁ := { start with regions := [region], inputBytes := fun _ => none }
  let s₂ := { s₁ with inputBytes := fun a => if a = 0 then some 0 else none }
  have regions : ∀ r ∈ [region], r.von < r.bis ∧
      r.bis ≤ 2 ^ bootLeck.katalog.plattform.ziel.physicalBits ∧
      ∀ e d, bootLeck.katalog.plattform.geraet e = some d → d.bus = .mmio → r.getrennt d.window := by
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    refine ⟨Nat.zero_lt_succ _, by change 1 ≤ 2 ^ (52 : Nat); omega, ?_⟩
    intro endpoint device selected mmio
    cases endpoint <;> cases selected
    · cases mmio
    · exact Or.inl (by change 1 ≤ 0x10000000; omega)
  obtain ⟨image, core, assignments, fits, _, _, _, outside⟩ := zul
  have zul₁ : bootLeck.ZulStart H s₁ :=
    ⟨image, core, assignments, fits, List.pairwise_singleton _ _, regions,
      (fun _ _ absent => nomatch absent), outside⟩
  have zul₂ : bootLeck.ZulStart H s₂ := by
    refine ⟨image, core, assignments, fits, List.pairwise_singleton _ _, regions, ?_, outside⟩
    intro a byte present
    change (if a = 0 then some 0 else none) = some byte at present
    split at present
    · rename_i address
      subst a
      exact ⟨region, List.mem_cons_self, Nat.le_refl _, Nat.zero_lt_succ _⟩
    · cases present
  have low : NiedrigGleich bootLeck s₁ s₂ := by
    unfold NiedrigGleich startProjektion
    apply congrArg (fun bytes => (s₁.bootCore, s₁.assignment, s₁.regions, bytes,
      niedereAussensicht bootLeck.etiketten s₁.outside))
    funext a
    change (sichtbar Ast.Semantik.geheim (s₁.inputBytes a)).join =
      (sichtbar Ast.Semantik.geheim (s₂.inputBytes a)).join
    simp only [sichtbar, Ast.Semantik.geheim_verborgen, Bool.false_eq_true, if_false]
  have loaded : bootLeck.laden s₁ (H.lade bootLeck.bild) = some (Maschine.I.start bootBasis s₁).2 := by
    change bootBasis.laden s₁ (H.lade bootBasis.bild) = _
    exact Beobachtung.fragment_geladen (Ast.Semantik.fragment Ast.Category.unit trivialUnit) .x86_64 hw zul₁
  have failed : bootLeck.laden s₂ (H.lade bootLeck.bild) = none := rfl
  obtain ⟨ρ₁, ρ₂, vergleich, mismatch⟩ :=
    vergleich_mit_ladefehler hw hw zul₁ zul₂ rfl low loaded failed
  exact ⟨H, ρ₁, ρ₂, vergleich, mismatch⟩

theorem VergleichSpurenOhneHerkunftAussage.erfuellbar :
    ∃ (E : Ast.Semantik.Einheit) (H₁ H₂ : Umgebung) (ρ₁ ρ₂ : Maschine.Lauf E),
      Annahme.Quelle.Akzeptiert E ∧ ¬ EinheitHerkunft E ∧ Vergleich E H₁ H₂ ρ₁ ρ₂ := by
  obtain ⟨H, ρ₁, ρ₂, vergleich, _⟩ := bootLeck_vergleich
  exact ⟨bootLeck, H, H, ρ₁, ρ₂, bootLeck_akzeptiert, bootLeck_ohneHerkunft, vergleich⟩

/-- The actual loader can disclose a private boot byte despite the checked ideal provenance. -/
theorem vergleichSpurenOhneHerkunft_widerlegt : ¬ VergleichSpurenOhneHerkunftAussage := by
  intro ni
  obtain ⟨_, _, _, vergleich, mismatch⟩ := bootLeck_vergleich
  exact mismatch (ni bootLeck bootLeck_akzeptiert bootLeck_ohneHerkunft vergleich)

end Gabbro.Core.Ziel.Korrektheit
