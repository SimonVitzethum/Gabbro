/-
  File:      core/Core/Ast/Semantik/Runtime/Unterbrechung/BeweiseFair.lean
  Subject:   Proofs for the two fairness duties: `sendeLiefert` closes `SendeLiefertAussage`
              over the named selection-fairness row `AuswahlFair`, `zaehlerUmlauf` closes
              `ZaehlerUmlaufAussage` over the counter row `ZaehlerZeile` with
              `ZaehlerLebendigAussage`. The positive witnesses are fair runs built below;
              the negative legs (`_nichtTrivial`) stay in `Beweise`.
-/
module

public import Core.Ast.Semantik.Runtime.Unterbrechung.Aussagen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Beobachtung

/-- A fair witness offer: every cut raises line 0 at priority 0 and selects it with its
    own origin. The raise sits at index 0, the selection names the cut as its origin. -/
private def fairAngebot : Nat → Gelegenheit
  | t => ⟨none, fun _ => true, [.erhoben 0 (.maskierbar 0 0), .zustellen 0 (t, 0) (.maskierbar 0 0)],
      fun _ => false, false, false, t⟩

/-- A fair witness run over the reference policy. -/
private def fairLauf : HwLauf :=
  ⟨fairAngebot,
    (Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer)).politik⟩

/-- A raise in the fair witness sits at index 0 and names line 0 at priority 0. -/
private theorem fairAngebot_erhoben {t i kern : Nat} {irq : Unterbrechung}
    (raise : (fairAngebot t).interrupts[i]? = some (.erhoben kern irq)) :
    i = Nat.zero ∧ kern = Nat.zero ∧ irq = .maskierbar 0 0 := by
  cases i with
  | zero =>
    have h0 : (fairAngebot t).interrupts[Nat.zero]? =
        some (.erhoben 0 (.maskierbar 0 0)) := rfl
    rw [h0] at raise
    cases raise
    exact ⟨rfl, rfl, rfl⟩
  | succ n =>
    cases n with
    | zero =>
      have h1 : (fairAngebot t).interrupts[Nat.succ Nat.zero]? =
          some (.zustellen 0 (t, 0) (.maskierbar 0 0)) := rfl
      rw [h1] at raise
      cases raise
    | succ m =>
      have hn : (fairAngebot t).interrupts[Nat.succ (Nat.succ m)]? = none := rfl
      rw [hn] at raise
      cases raise

/-- The fair witness is selection-fair: every raise is selected at its own cut. -/
private theorem fairLauf_fair :
    AuswahlFair (Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer))
      fairLauf := by
  intro t i kern irq raise _hk _sup
  obtain ⟨hi, hk0, hirq⟩ := fairAngebot_erhoben raise
  subst hi
  subst hk0
  subst hirq
  refine ⟨t, (t, 0), Nat.le_refl t, ?_, ?_⟩
  · rfl
  · cases t with
    | zero => exact ⟨rfl, rfl⟩
    | succ n => exact ⟨Nat.le_refl _, rfl⟩

/-- A counter witness offer: every cut raises the row's trap line; the counter is the cut. -/
private def zaehlerAngebot : Nat → Gelegenheit
  | t => ⟨none, fun _ => true, [.erhoben 0 (.maskierbar 32 0)], fun _ => false, false, false, t⟩

/-- A counter witness run over the reference policy. -/
private def zaehlerLauf : HwLauf :=
  ⟨zaehlerAngebot,
    (Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer)).politik⟩

/-- The counter witness raises the trap line of the x86-64 row at every cut. -/
private theorem zaehlerLauf_lebendig :
    ZaehlerLebendigAussage .x86_64
      (Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer))
      zaehlerLauf := by
  intro _hziel t kern hk _cyc
  have hk1 : kern < 1 := hk
  have hk0 : kern = 0 := Nat.lt_one_iff.mp hk1
  subst hk0
  refine ⟨t, 0, Nat.le_refl t, ?_⟩
  rfl

/-- **A sent interrupt is selected** (proof of `SendeLiefertAussage`): the row at the raise cut. -/
theorem sendeLiefert : SendeLiefertAussage := by
  intro h run t vektor kern i fair raise hk sup
  exact fair t i kern _ raise hk sup

/-- **The bound raises the trap line** (proof of `ZaehlerUmlaufAussage`): the row at the bound cut. -/
theorem zaehlerUmlauf : ZaehlerUmlaufAussage := by
  intro p h run t kern leb hziel hk cyc
  obtain ⟨t', i, le, raise⟩ := leb hziel t kern hk cyc
  refine ⟨t', p.zaehlerZeile.trap, le, ?_, i, raise⟩
  rw [hziel]
  exact p.zaehlerZeile_unterstuetzt

/-- The premises of `SendeLiefertAussage` hold jointly: a fair raise exists. -/
theorem sendeLiefert_erfuellbar :
    ∃ (h : Katalog.Umgebung) (run : HwLauf) (t vektor kern i : Nat),
      AuswahlFair h run ∧
      (run.angebot t).interrupts[i]? = some (.erhoben kern (.maskierbar vektor 0)) ∧
      kern < h.kernzahl ∧ h.ziel.unterstuetzt (.maskierbar vektor 0) := by
  refine ⟨Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer),
    fairLauf, 0, 0, 0, 0, fairLauf_fair, rfl, by decide, ?_⟩
  show (Plattform.x86_64.ziel.unterstuetzt (.maskierbar 0 0))
  simp only [ZielDaten.unterstuetzt, Plattform.ziel]
  decide

/-- The premises of `ZaehlerUmlaufAussage` hold jointly: the row's bound is reached and raised. -/
theorem zaehlerUmlauf_erfuellbar :
    ∃ (p : Plattform) (h : Katalog.Umgebung) (run : HwLauf) (t kern : Nat),
      ZaehlerLebendigAussage p h run ∧ h.ziel = p.ziel ∧ kern < h.kernzahl ∧
      (run.angebot t).cycles = p.zaehlerZeile.schranke := by
  refine ⟨.x86_64,
    Katalog.Umgebung.referenz Plattform.x86_64.katalog 1 (fun _ _ => AussenSicht.leer),
    zaehlerLauf, Plattform.x86_64.zaehlerZeile.schranke, 0,
    zaehlerLauf_lebendig, rfl, by decide, rfl⟩

end Gabbro.Core.Ast.Semantik
