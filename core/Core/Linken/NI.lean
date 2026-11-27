/-
  File:      core/Core/Linken/NI.lean
  Subject:   THE TWO-RUN NONINTERFERENCE OF SUCCESSFULLY LINKED UNITS (PERFECT-MODEL M9/M12).

  The pinned `VergleichSpurenAussage` compares the low traces of two low-equal runs. Its source-side
  instance is `niAkzeptiert`, which is quellsyntax-indexed (`einheitVon P t`). A linked program is not the
  denotation of one source tree, so that route does not apply. The proof below applies the generic
  fragment theorems at the linked unit's ACTUAL fragment `frag.einheit plan.plattform`.

  The exact invariant the concrete linked transition needs is source provenance of every module:
  `linke plan = some frag` gives `bauplanOk plan = true`, whose first conjunct is
  `plan.module.all Modul.hatQuelle`; the concatenation of source modules is `KlassenRein` by
  `verknuepfte_klassenrein` and `linke_klassenrein`. Hence a frame-only linked whole goes through
  `fragment_nichtinterferent` and one with an access through `zugriffNIFragment`. No language form,
  goal statement, hardware row or linker check is changed.
-/
module

public import Core.Linken.Aussage
public import Core.Beobachtung.Satz
public import Core.Annahme.Quellbindung
public import Core.Beobachtung.Fluss.Beweise.Gesamt
public import Core.Ziel.Korrektheit.Beweise.NIAkzeptiert
public import Core.Ziel.Korrektheit.Beweise2.ZugriffNIFragmentBeweis

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Beobachtung
open Gabbro.Core.Ziel.Korrektheit

/-- From full noninterference to the pinned comparison-trace conclusion: take the compared right run's
    start as the second start; the comparison supplies its admission, hardware, low start and policy. -/
theorem nichtinterferent_zu_vergleich {E : Ast.Semantik.Einheit}
    (ni : Beobachtung.Nichtinterferent E) :
    ∀ {H₁ H₂ : Katalog.Umgebung} {ρ₁ ρ₂ : Maschine.Lauf E},
      Beobachtung.Vergleich E H₁ H₂ ρ₁ ρ₂ →
      Beobachtung.NiedrigAequiv E (Beobachtung.NiedrigeBeob E ρ₁) (Beobachtung.NiedrigeBeob E ρ₂) := by
  intro H₁ H₂ ρ₁ ρ₂ v
  exact (ni H₁ H₂ ρ₁ ρ₂.start v.links.1 v.rechts.1 v.links v.umgebung v.rechts.2.2.1 v.start).2
    ρ₂ v.rechts rfl v.politik

/-- **A successfully linked unit is noninterferent at its actual fragment.** Checked link provenance gives
    `frag.KlassenRein`; the two classes are then discharged by the generic fragment theorems, without asking
    for a source tree that denotes the linked result. -/
theorem ni_linkAkzeptiert (plan : Bauplan) (frag : Fragment)
    (hlink : linke plan = some frag)
    (hacc : Annahme.Akzeptiert (frag.einheit plan.plattform)) :
    Beobachtung.Nichtinterferent (frag.einheit plan.plattform) := by
  by_cases rein : frag.Rein
  · exact fragment_nichtinterferent frag plan.plattform rein hacc
  · exact zugriffNIFragment frag plan.plattform ⟨linke_klassenrein hlink, rein⟩ hacc

/-- **The linked half of `VergleichSpurenAussage`.** Source acceptance of a linked unit reduces to plain
    acceptance by its provenance, so the comparison-trace conclusion follows at `frag.einheit`. -/
theorem vergleichSpuren_verlinkt (plan : Bauplan) (frag : Fragment)
    (hlink : linke plan = some frag)
    (hacc : Annahme.Quelle.Akzeptiert (frag.einheit plan.plattform)) :
    ∀ {H₁ H₂ : Katalog.Umgebung} {ρ₁ ρ₂ : Maschine.Lauf (frag.einheit plan.plattform)},
      Beobachtung.Vergleich (frag.einheit plan.plattform) H₁ H₂ ρ₁ ρ₂ →
      Beobachtung.NiedrigAequiv (frag.einheit plan.plattform)
        (Beobachtung.NiedrigeBeob (frag.einheit plan.plattform) ρ₁)
        (Beobachtung.NiedrigeBeob (frag.einheit plan.plattform) ρ₂) := by
  exact nichtinterferent_zu_vergleich (ni_linkAkzeptiert plan frag hlink hacc.regeln)

/-- The source-denoted half, for contrast: `niAkzeptiert` delivers the same conclusion at `einheitVon P t`. -/
theorem vergleichSpuren_quelle (P : Katalog.Plattform) (t : Ast.Unit)
    (hacc : Annahme.Quelle.Akzeptiert (einheitVon P t)) :
    ∀ {H₁ H₂ : Katalog.Umgebung} {ρ₁ ρ₂ : Maschine.Lauf (einheitVon P t)},
      Beobachtung.Vergleich (einheitVon P t) H₁ H₂ ρ₁ ρ₂ →
      Beobachtung.NiedrigAequiv (einheitVon P t)
        (Beobachtung.NiedrigeBeob (einheitVon P t) ρ₁)
        (Beobachtung.NiedrigeBeob (einheitVon P t) ρ₂) := by
  exact nichtinterferent_zu_vergleich (niAkzeptiert P t hacc.regeln)

/-- The two halves are jointly satisfiable: the accepted two-module example links and is noninterferent. -/
theorem ni_link_erfuellbar :
    ∃ (plan : Bauplan) (frag : Fragment), linke plan = some frag ∧
      Annahme.Akzeptiert (frag.einheit plan.plattform) ∧
      Beobachtung.Nichtinterferent (frag.einheit plan.plattform) :=
  ⟨beispielPlan, beispielFragment, beispielLinke, beispielAkzeptiert,
    ni_linkAkzeptiert beispielPlan beispielFragment beispielLinke beispielAkzeptiert⟩

end Gabbro.Core.Linken
