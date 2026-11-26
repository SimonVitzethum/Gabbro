module

public import Core.Annahme.HostedLauf
public import Core.Verfeinerung.Formen.Abdeckung

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Annahme Katalog

/- The joint witness for an accepted unit with its simulation obligations and a concrete
   run is removed: the hosted unit that carried it is not accepted under the MK-17
   isolation row (its `frage` rule breaks every channel-free plan), and no replacement
   witness is supplied here. The per-form step premises below do not need acceptance. -/

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
      FuehrtSchrittAus E.einrichtung 0 eintritt z (b.nach eintritt z) plan ⟨[], []⟩
        (b.maschinennach eintritt z (b.nach eintritt z)) := by
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
    b.vollzug _ _ _ _ priv⟩

end Gabbro.Core.Ast.Semantik
