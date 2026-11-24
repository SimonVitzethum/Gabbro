module

public import Core.Beobachtung.SchrankenB9B21
public import Core.Annahme.HostedLauf

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Annahme.Hosted

private def mitGrenzen (boot : AussenStart → Zustand) (speicher : Option Nat := some 1) : Modell :=
  { einheit with
    laden := fun s _ => some (boot s)
    schranken := { Schrankendaten.leer with
      stapel := some 1, speicher, stapelTiefe := fun h => if h.isSome then 1 else 0 } }

private theorem stapel_beschraenkt (boot : AussenStart → Zustand) (s : Zustand) :
    StapelZustand (mitGrenzen boot) s := by
  intro c n eq
  cases Option.some.inj eq
  cases s.lokal c with
  | none => exact Nat.zero_le _
  | some _ => exact Nat.le_refl _

private theorem zellen_leer {s : Zustand} (h : ∀ i, s.buchung.umfang i = []) :
    LebendeZellen s = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z mem
  change s.rechte.lebt z.1 = true ∧ z.2 < (s.buchung.umfang z.1).length at mem
  rw [h z.1] at mem
  exact Nat.not_lt_zero _ mem.2

private theorem speicher_beschraenkt (boot : AussenStart → Zustand) {s : Zustand}
    (h : (LebendeZellen s).encard ≤ 1) : SpeicherZustand (mitGrenzen boot) s := by
  intro n eq
  cases Option.some.inj eq
  exact h

private theorem hosted_pflichten (boot : AussenStart → Zustand)
    (initial : ∀ s, (LebendeZellen (boot s)).encard ≤ 1) : RessourcenPflichten (mitGrenzen boot) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h ρ lauf s cut
    have eq : boot ρ.start = s := Option.some.inj (lauf.2.2.2.symm.trans cut)
    exact ⟨stapel_beschraenkt boot s, speicher_beschraenkt boot (eq ▸ initial ρ.start)⟩
  · intro f h ρ lauf t c w spur vor nach vorEq kopf label nachEq step stapel speicher
    refine ⟨stapel_beschraenkt boot nach, ?_⟩
    cases step with
    | kontext _ _ form aus =>
      obtain ⟨i, _, form⟩ := form
      obtain ⟨_, _, _, _, aktion, _, ziel⟩ := aus
      change Annahme.Hosted.regel c vor w [_] _ at form
      change FuehrtAus einrichtung t c vor _ _ _ _ _ at aktion
      rcases form.2 with ⟨eq, _, rfl⟩ | ⟨eq, _, rfl⟩ <;>
        cases (List.cons.inj eq).1 <;> cases aktion <;> rw [ziel] <;> exact speicher
  · intro h ρ lauf t w spur vor nach vorEq label wahl nachEq step stapel speicher
    refine ⟨stapel_beschraenkt boot nach, ?_⟩
    cases step with
    | kontext => exact False.elim wahl
    | antwort _ step =>
      rw [step.2.2.2]
      exact speicher
    | interrupt _ step =>
      obtain ⟨_, _, _, _, _, _, _, _, _, eq⟩ := step
      rw [eq]
      exact speicher
    | absturz step =>
      rw [step.genau.2]
      apply speicher_beschraenkt boot
      rw [zellen_leer (fun _ => rfl), Set.encard_empty]
      exact zero_le _

private def eineZelle (s : AussenStart) : Zustand :=
  let z := startZustand s
  { z with buchung := { z.buchung with umfang := fun i => if i = 0 then [()] else [] } }

private theorem eineZelle_encard (s : AussenStart) : (LebendeZellen (eineZelle s)).encard = 1 := by
  have singleton : LebendeZellen (eineZelle s) = {(0, 0)} := by
    ext ⟨i, j⟩
    change (true = true ∧ j < (if i = 0 then [()] else []).length) ↔ (i, j) ∈ ({(0, 0)} : Set (Nat × Nat))
    by_cases hi : i = 0
    · subst i
      simp only [↓reduceIte, List.length_cons, List.length_nil, true_and,
        Nat.lt_one_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    · simp only [hi, if_false, List.length_nil, Nat.not_lt_zero, Set.mem_singleton_iff, Prod.mk.injEq, false_and, and_false]
  rw [singleton, Set.encard_singleton]

/-- The generic composition premises are jointly satisfiable on an admitted successful load.
    Both declared ceilings are reached at the initial cut, with one live cell and depth one. -/
theorem b9_b21_start_erfuellbar :
    ∃ (E : Modell) (h : Umgebung) (ρ : Lauf E) (s : Zustand),
      RessourcenPflichten E ∧ Laeufe E h ρ ∧ ρ.zeit.zustand 0 = some s ∧
      RessourcenPrefix E ρ 0 ∧ E.schranken.stapel = some 1 ∧ E.schranken.speicher = some 1 ∧
      E.schranken.stapelTiefe (s.lokal kontext) = 1 ∧ (LebendeZellen s).encard = 1 := by
  obtain ⟨start, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, lauf, startEq⟩ := lauf_ab_start (mitGrenzen eineZelle) (erlaubt []) zul
  have pflichten := hosted_pflichten eineZelle (fun s => (eineZelle_encard s).le)
  have cut : ρ.zeit.zustand 0 = some (eineZelle start) := lauf.2.2.2.trans (congrArg _ startEq)
  refine ⟨_, _, ρ, _, pflichten, lauf, cut, pflichten.start lauf, rfl, rfl, ?_, eineZelle_encard start⟩
  change (if (start.outside.channels .hosted 0).isSome then 1 else 0) = 1
  rw [zul.2.2.2.2.2.2.2]
  rfl

private def lauf_mit_grenzen (ρ : Lauf einheit) : Lauf (mitGrenzen startZustand) where
  start := ρ.start
  hw := ρ.hw
  zeit := ⟨ρ.zeit.zustand, ρ.zeit.spur, fun t => by
    cases ρ.zeit.takt t with
    | wartet label gleich ruhe =>
      refine .wartet label gleich (fun label neu step => ruhe label neu ?_)
      cases step with
      | schritt step => exact .schritt step
    | schritt label step =>
      cases step with
      | schritt step => exact .schritt label (.schritt step)⟩

/-- The form and protocol premises hold at occupied cuts on the same finitely bounded run. -/
theorem b9_b21_schritte_erfuellbar :
    ∃ (E : Modell) (h : Umgebung) (ρ : Lauf E) (s₀ s₁ s₂ s₃ : Zustand)
      (formSpur protokollSpur : Spur) (w : SchrittWahl Unit),
      RessourcenPflichten E ∧ Laeufe E h ρ ∧ E.schranken.stapel = some 1 ∧ E.schranken.speicher = some 1 ∧
      (ρ.zeit.zustand 0 = some s₀ ∧ E.system.kopf s₀ kontext = some () ∧
        ρ.zeit.spur 0 = some (.kontext kontext (), formSpur) ∧ ρ.zeit.zustand 1 = some s₁ ∧
        ImplSchritt E.einrichtung E.system E.katalog ρ.hw 0 s₀ (.kontext kontext (), formSpur) s₁ ∧
        StapelZustand E s₀ ∧ SpeicherZustand E s₀) ∧
      (ρ.zeit.zustand 2 = some s₂ ∧ ρ.zeit.spur 2 = some (w, protokollSpur) ∧
        ProtokollB8Wahl w ∧ ρ.zeit.zustand 3 = some s₃ ∧
        ImplSchritt E.einrichtung E.system E.katalog ρ.hw 2 s₂ (w, protokollSpur) s₃ ∧
        StapelZustand E s₂ ∧ SpeicherZustand E s₂) := by
  obtain ⟨start, zul⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  obtain ⟨ρ, g, g', lauf, _, hw, cut0, cut1, cut2, cut3, label0, _, label2, _⟩ := konkreter_lauf zul []
  let ρ' := lauf_mit_grenzen ρ
  have lauf' : Laeufe (mitGrenzen startZustand) (umgebung []) ρ' :=
    ⟨lauf.1, lauf.2.1, lauf.2.2.1, lauf.2.2.2⟩
  have pflichten := hosted_pflichten startZustand (fun s => by
    rw [zellen_leer (s := startZustand s) (fun _ => rfl), Set.encard_empty]
    exact zero_le _)
  have step {t vor w spur nach} (vorEq : ρ.zeit.zustand t = some vor)
      (label : ρ.zeit.spur t = some (w, spur)) (nachEq : ρ.zeit.zustand (t + 1) = some nach) :
      ImplSchritt (mitGrenzen startZustand).einrichtung (mitGrenzen startZustand).system
        (mitGrenzen startZustand).katalog ρ'.hw t vor (w, spur) nach := by
    have takt := ρ.zeit.takt t
    rw [vorEq, label, nachEq] at takt
    cases takt with
    | schritt label folge =>
      cases Option.some.inj label
      cases folge with
      | schritt step => exact step
    | wartet no _ _ => cases no
  have at0 := pflichten.start lauf' _ cut0
  have at2 := b9_b21_aus_pflichten pflichten lauf' 2 _ cut2
  exact ⟨_, _, ρ', _, _, _, _, _, _, _, pflichten, lauf', rfl, rfl,
    ⟨cut0, rfl, label0, cut1, step cut0 label0 cut1, at0.1, at0.2⟩,
    ⟨cut2, label2, trivial, cut3, step cut2 label2 cut3, at2.1, at2.2⟩⟩

/-- An absent memory ceiling permits an actual live cell even when an explicit zero would fail. -/
theorem b21_offen_erfuellbar :
    ∃ (E : Modell) (s : Zustand), E.schranken.speicher = none ∧ SpeicherZustand E s ∧
      (LebendeZellen s).encard = 1 ∧ ¬ SpeicherZustand (mitGrenzen eineZelle (some 0)) s := by
  obtain ⟨start, _⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  have live := eineZelle_encard start
  refine ⟨mitGrenzen eineZelle none, eineZelle start, rfl, (fun _ eq => nomatch eq), live, ?_⟩
  intro closed
  have bound := closed 0 rfl
  rw [live] at bound
  exact (not_le_of_gt zero_lt_one) bound

end Gabbro.Core.Beobachtung
