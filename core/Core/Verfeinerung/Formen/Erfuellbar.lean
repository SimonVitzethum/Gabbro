module

public import Core.Annahme.HostedLauf
public import Core.Verfeinerung.Formen.Abdeckung

@[expose] public section

namespace Gabbro.Core.Maschine.I

open Gabbro.Core.Annahme Katalog

open Hosted in
/-- The run accounting covers a real arrival after the question is issued, with
    the same question instance and reply in the matched ideal answer book. -/
theorem antwortabgleich_erfuellbar :
    ∃ (ρ : Maschine.Lauf Hosted.einheit) (η : Lauf Hosted.einheit)
      (k : Maschine.Schnitt Hosted.einheit ρ) (a : AntwortEreignis),
      Maschine.Laeufe Hosted.einheit (umgebung []) ρ ∧ Laeufe Hosted.einheit η ∧
      Sim Hosted.einheit ρ η ∧ Antwortabgleich ρ η ∧
      (η.zeit.zustand (Zeitlauf.schnittBild ρ.zeit η.zeit k).val).antworten = [a] := by
  obtain ⟨s, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, _, _, run, _, _, _, _, _, _, ev0, ev1, ev2, _⟩ := konkreter_lauf zul []
  have basis : SimBasisPflichten Hosted.einheit := by
    apply SimBasisPflichten.aus_gleichen_regeln rfl (fun _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ step => step)
    intro _ _ _ _ p _ step
    rcases step.2 with ⟨plans, _, _⟩ | ⟨plans, _, _⟩
    · cases (List.cons.inj plans).1
      exact ⟨fun _ mem => (List.not_mem_nil mem).elim, fun _ mem _ => (List.not_mem_nil mem).elim⟩
    · cases (List.cons.inj plans).1
      exact ⟨fun _ mem => (List.not_mem_nil mem).elim, fun _ mem _ => (List.not_mem_nil mem).elim⟩
  have forms : ∀ f, RegelSimulation Hosted.einheit f :=
    fun _ => ⟨RegelSimSchritt.aus_gleicher_regel rfl (fun _ _ _ _ _ step => step), RegelStotterSchranke.null rfl⟩
  obtain ⟨η, valid, sim, answers⟩ := sim_im_lauf_mit_antwortabgleich (basis.mit_formen forms) run
  let k : Maschine.Schnitt Hosted.einheit ρ := ⟨3, Or.inr ⟨2, _, rfl, ev2⟩⟩
  obtain ⟨_, _, _, book, _, _, _⟩ := answers k
  refine ⟨ρ, η, k, angekommen s [], run, valid, sim, answers, book.trans ?_⟩
  change Zeitlauf.praefix (fun n => (ρ.zeit.spur n).elim [] (Antwortspur ∘ Prod.snd)) 3 = _
  rw [Zeitlauf.praefix, Zeitlauf.praefix, Zeitlauf.praefix, ev0, ev1, ev2]
  rfl

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
      (E.system.regel b).impl eintritt z () [b.plan (z.lokal eintritt) 0] (b.nach eintritt z) ∧
      FuehrtSchrittAus E.einrichtung 0 eintritt z (b.nach eintritt z) (b.plan (z.lokal eintritt) 0) ⟨[], []⟩
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
    (b.impl_privat priv eintritt (I.start E s).2 () [_] (b.nach eintritt (I.start E s).2)).2 ⟨rfl, rfl⟩,
    b.vollzug _ _ _ _ priv⟩

end Gabbro.Core.Ast.Semantik
