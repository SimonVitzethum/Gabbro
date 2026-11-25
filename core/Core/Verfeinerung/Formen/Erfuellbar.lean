module

public import Core.Annahme.HostedLauf
public import Core.Verfeinerung.Formen.Abdeckung

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Annahme Katalog

/-- An accepted unit with a catalogue request meets the shared and per-form
    obligations and has a concrete run on an admitted hardware history. -/
theorem sim_akzeptierter_lauf_erfuellbar :
    ∃ E : Hosted.Modell, Akzeptiert E ∧ SimBasisPflichten E ∧
      (∀ f, RegelSimulation E f) ∧ ∃ h ρ, Maschine.Laeufe E h ρ := by
  have basis : SimBasisPflichten Hosted.einheit := by
    apply SimBasisPflichten.aus_gleichen_regeln rfl (fun _ _ _ _ => rfl) (fun _ _ _ _ _ _ rule => rule)
    intro f c s w p u rule
    change Hosted.regel c s w [p] u at rule
    rcases rule.2 with ⟨same, _, _⟩ | ⟨same, _, _⟩ <;>
      cases (List.cons.inj same).1 <;>
      exact ⟨fun _ empty => (List.not_mem_nil empty).elim, fun _ empty => (List.not_mem_nil empty).elim⟩
  have forms : ∀ f, RegelSimulation Hosted.einheit f := fun _ =>
    ⟨RegelSimSchritt.aus_gleicher_regel rfl (fun _ _ _ _ _ rule => rule), RegelStotterSchranke.null rfl⟩
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (Hosted.erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, run, _, _⟩ := Maschine.lauf_mit_hw Hosted.einheit (Hosted.erlaubt []) zul (Hosted.konform [])
  exact ⟨Hosted.einheit, Hosted.akzeptiert, basis, forms, Hosted.umgebung [], ρ, run⟩

end Gabbro.Core.Maschine.I

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog

/-- All step premises can hold jointly, for every frame-only instruction and therefore
    for each frame-only family packet. The chosen tick executes the instruction at the
    canonical initial cut of a singleton fragment. -/
theorem sim_formvoraussetzungen_erfuellbar (b : Befehl) (priv : b.Privat) :
    let E := (Fragment.einzel b).einheit .x86_64
    ∃ h s hw,
      Hardware E.katalog h ∧ E.ZulStart h s ∧ hw.konform E.katalog h ∧
      let z := (I.start E s).2
      I.Zustandsbezug E z z ∧ (hw.angebot 0).crash = false ∧ KannSchreiten hw 0 eintritt z ∧
      E.system.kopf z eintritt = some b ∧
      (E.system.regel b).impl eintritt z () [plan] (b.nach eintritt z) ∧
      FuehrtSchrittAus E.einrichtung 0 eintritt z (b.nach eintritt z) plan ⟨[], []⟩ (b.nach eintritt z) := by
  let E := (Fragment.einzel b).einheit .x86_64
  have image : E.bild.gueltig E.katalog.plattform.ziel := Sicherheit.Laufkonstruktion.bild_gueltig
  have hardware := Hosted.erlaubt []
  obtain ⟨s, zul⟩ := zulStart_erfuellbar hardware image
  obtain ⟨k, assigned⟩ := zul.2.2.1 0 (Nat.zero_lt_succ _)
  have kZero : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (zul.2.2.2.1 0 k assigned).2)
  rw [kZero] at assigned
  have ready : KannSchreiten (Hosted.hardware []) 0 eintritt (I.start E s).2 := by
    refine ⟨0, rfl, ?_, rfl⟩
    change (if some 0 = s.assignment 0 then some eintritt else none) = some eintritt
    rw [assigned, ite_eq_left rfl]
  exact ⟨Hosted.umgebung [], s, Hosted.hardware [], hardware, zul, Hosted.konform [],
    ⟨I.ProtokollBezug.refl _, rfl⟩, rfl, ready, rfl,
    (b.impl_privat priv eintritt (I.start E s).2 () [plan] (b.nach eintritt (I.start E s).2)).2 ⟨rfl, rfl⟩,
    b.vollzug _ _ _ _⟩

end Gabbro.Core.Ast.Semantik
