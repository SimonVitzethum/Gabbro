/-
  File:      core/Core/Ziel/Korrektheit/Beweise/BegleitVerfeinerung.lean
  Subject:   COMPANION LEMMAS for the pinned statements of `Core/Ziel/Korrektheit/Verfeinerung.lean`
             (refinement layer, M7/M8): for every `…Aussage` an `X.erfuellbar` (the premises hold jointly)
             and an `X.nichtTrivial` (the statement is sharp: a weaker form fails, or a refused object
             violates it). No statement is changed. The universal legs share the empty unit on x86-64,
             which is accepted by the guard-free-fragment rule and has a fair run; the refused-object
             witnesses reuse the falsifiability configuration, the starvation run and the loader gap.
-/
module

public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Ziel.Korrektheit.Beweise.BegleitMaschine
public import Core.Ziel.Korrektheit.Beweise.Falsifizierbar
public import Core.Ziel.Korrektheit.Beweise.FortschrittAkzeptiert
public import Core.Ast.LowLevel.Proofs.EnvironmentSatisfiability
public import Core.Verfeinerung.Erfuellbar
public import Core.Fortschritt.Verhungern
public import Core.Annahme.Annahme
public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Fortschritt
open Katalog

/-- The empty source unit is accepted: its fragment has no clauses and its two instructions
    (`starte`, `ende`) carry no guard, so the guard-free-fragment rule applies. -/
private theorem trivial_akzeptiert :
    Annahme.Akzeptiert (einheitVon Plattform.x86_64 trivialUnit) := by
  unfold einheitVon Ast.Semantik.elaborieren
  apply Ast.Semantik.Fragment.akzeptiert_ohne_bedarf
  · rfl
  · intro b present frame
    change b ∈ ([Ast.Semantik.Befehl.starte Ast.Semantik.mainName,
      Ast.Semantik.Befehl.ende] : List Ast.Semantik.Befehl) at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl

/-- The shared premise bundle of the three universal refinement statements: the empty unit is
    accepted, admits a run and admits a fair hardware history on x86-64. -/
private theorem trivial_erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit) (H : Umgebung) (hw : HwLauf)
      (ρ : Maschine.Lauf (einheitVon P t)),
      Annahme.Akzeptiert (einheitVon P t) ∧
      Maschine.Laeufe (einheitVon P t) H ρ ∧
      FairLaeufe (einheitVon P t).katalog H hw := by
  obtain ⟨H, s, hw, zul, hwhw, fair, z, geladen, gut⟩ := trivial_start_bereit
  obtain ⟨ρ, run, startEq, hwEq⟩ := fairer_lauf _ zul fair
  exact ⟨Plattform.x86_64, trivialUnit, H, hw, ρ, trivial_akzeptiert, run, fair⟩

/-- The premises of whole-run refinement hold jointly: an accepted elaborated unit has a run.
    Feeds: `trivial_erfuellbar`. -/
theorem VerfeinerungAkzeptiertAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit) (H : Umgebung) (ρ : Maschine.Lauf (einheitVon P t)),
      Annahme.Akzeptiert (einheitVon P t) ∧ Maschine.Laeufe (einheitVon P t) H ρ := by
  obtain ⟨P, t, H, hw, ρ, akz, run, fair⟩ := trivial_erfuellbar
  exact ⟨P, t, H, ρ, akz, run⟩

/-- The acceptance premise is load-bearing: a refused unit has a run that no ideal run matches.
    Feeds: `simRefutierbar`. -/
theorem VerfeinerungAkzeptiertAussage.nichtTrivial : SimRefutierbarAussage :=
  simRefutierbar

/-- The premises of the cut guarantee hold jointly: an accepted elaborated unit has a run and
    hence a cut at tick zero. Feeds: `trivial_erfuellbar`. -/
theorem ZielFXAkzeptiertAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit) (H : Umgebung) (ρ : Maschine.Lauf (einheitVon P t))
      (k : Maschine.Schnitt (einheitVon P t) ρ),
      Annahme.Akzeptiert (einheitVon P t) ∧ Maschine.Laeufe (einheitVon P t) H ρ := by
  obtain ⟨P, t, H, hw, ρ, akz, run, fair⟩ := trivial_erfuellbar
  exact ⟨P, t, H, ρ, ⟨0, Or.inl rfl⟩, akz, run⟩

/-- The run premise is load-bearing: a run that does not start from the loader state fails
    `ZielFX` at its initial cut. Feeds: `Zeitlauf.existiert`, `trivialeEinheit`. -/
theorem ZielFXAkzeptiertAussage.nichtTrivial :
    ∃ (E : Maschine.Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit)
      (H : Umgebung) (ρ : Maschine.Lauf E) (k : Maschine.Schnitt E ρ),
      ¬ Maschine.ZielFX E H ρ k := by
  let E := Annahme.trivialeEinheit
  let s : AussenStart := ⟨0, fun _ => none, [], fun _ => none, AussenSicht.leer⟩
  let H := Umgebung.referenz E.katalog 1 (fun _ _ => AussenSicht.leer)
  let hw := Umgebung.referenzLauf E.katalog 1 (fun _ _ => AussenSicht.leer)
  let z : Zustand Unit Unit Unit Unit Unit Unit := (I.start E s).2
  obtain ⟨zeit, init⟩ := Zeitlauf.existiert (Lauffolge E hw) (some z)
  refine ⟨E, H, ⟨s, hw, zeit⟩, ⟨0, Or.inl rfl⟩, ?_⟩
  intro gut
  have h0 := gut.1.2.2.2
  rw [init] at h0
  change some z = none at h0
  cases h0

/-- The premises of progress hold jointly: an accepted elaborated unit has a run on a hardware-fair
    history. Feeds: `trivial_erfuellbar`. -/
theorem FortschrittAkzeptiertAussage.erfuellbar :
    ∃ (P : Plattform) (t : Ast.Unit) (H : Umgebung) (hw : HwLauf)
      (ρ : Maschine.Lauf (einheitVon P t)),
      Annahme.Akzeptiert (einheitVon P t) ∧ Maschine.Laeufe (einheitVon P t) H ρ ∧
        FairLaeufe (einheitVon P t).katalog H hw := by
  obtain ⟨P, t, H, hw, ρ, akz, run, fair⟩ := trivial_erfuellbar
  exact ⟨P, t, H, hw, ρ, akz, run, fair⟩

/-- The no-hang leg is load-bearing: the starvation run has a continuously enabled, dispatched
    context that is never discharged. Feeds: `hang_B`. -/
theorem FortschrittAkzeptiertAussage.nichtTrivial :
    ∃ (E : Maschine.Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit)
      (ρ : Maschine.Lauf E) (η : I.Lauf E) (c : Kontext), I.Haengt E ρ η c :=
  ⟨E_w dispatch2, ρAB, ηAB, B, hang_B⟩

/-- The per-form duty is discriminating: some rule's implementation step the ideal rule refuses.
    Feeds: `regelSimDiskriminiert`. -/
theorem RegelSimDiskriminiertAussage.erfuellbar : RegelSimDiskriminiertAussage :=
  regelSimDiskriminiert

/-- The duty is achievable: some rule satisfies it, so the discrimination statement is not
    vacuously true because every rule fails the duty. Feeds: `fortschritt_erfuellbar`. -/
theorem RegelSimDiskriminiertAussage.nichtTrivial :
    ∃ (E : Maschine.Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit) (f : Unit),
      I.RegelSimSchritt E f := by
  obtain ⟨E, pflicht, rest⟩ := Gabbro.Core.Maschine.I.fortschritt_erfuellbar
  exact ⟨E, (), pflicht.abgleich.regel ()⟩

/-- Whole-run simulation separates ideal runs: one ideal run matches and another does not.
    Feeds: `simTrennt`. -/
theorem SimTrenntAussage.erfuellbar : SimTrenntAussage :=
  simTrennt

/-- Separation is not universal: a matched run need not have a non-matching ideal run. Feeds:
    `fortschritt_erfuellbar`. -/
theorem SimTrenntAussage.nichtTrivial :
    ∃ (E : Maschine.Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit)
      (H : Umgebung) (ρ : Maschine.Lauf E) (η₁ η₂ : I.Lauf E),
      Maschine.Laeufe E H ρ ∧ I.Laeufe E η₁ ∧ I.Sim E ρ η₁ ∧
        I.Laeufe E η₂ ∧ I.Sim E ρ η₂ := by
  obtain ⟨E, pflicht, H, ρ, η, run, fair, ideal, matched, sim, fx, progress, nohang, klassen,
    label, before, after, at0, at1, state, state', config⟩ :=
      Gabbro.Core.Maschine.I.fortschritt_erfuellbar
  exact ⟨E, H, ρ, η, η, run, ideal, sim, ideal, sim⟩

/-- Refinement refuses an implementation run: some run has no matching ideal run. Feeds:
    `simRefutierbar`. -/
theorem SimRefutierbarAussage.erfuellbar : SimRefutierbarAussage :=
  simRefutierbar

/-- Refinement is achievable: some run has a matching ideal run, so the refutation statement is
    not vacuously true because no run is ever matched. Feeds: `fortschritt_erfuellbar`. -/
theorem SimRefutierbarAussage.nichtTrivial :
    ∃ (E : Maschine.Einheit Unit Unit Unit Unit Bool Unit Unit Unit Unit)
      (H : Umgebung) (ρ : Maschine.Lauf E) (η : I.Lauf E),
      Maschine.Laeufe E H ρ ∧ I.Laeufe E η ∧ I.Sim E ρ η := by
  obtain ⟨E, pflicht, H, ρ, η, run, fair, ideal, matched, sim, fx, progress, nohang, klassen,
    label, before, after, at0, at1, state, state', config⟩ :=
      Gabbro.Core.Maschine.I.fortschritt_erfuellbar
  exact ⟨E, H, ρ, η, run, ideal, sim⟩

end Gabbro.Core.Ziel.Korrektheit
