module

public import Core.Beobachtung.Fluss.Lader
public import Core.Verfeinerung.Formen.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Befehl Fragment eintritt)

/-- The premise of each instruction obligation occurs at the first cut of an admitted
    concrete run. The same run supplies a comparison for every predictor. -/
theorem fragment_ni_form_erfuellbar (f : Befehl) (priv : f.Privat) :
    let p := Fragment.einzel f
    let E := p.einheit .x86_64
    ∃ (h : Umgebung) (ρ : Lauf E) (vor : Ast.Semantik.Zustand),
      RegelFluss E f ∧ Vergleich E h h ρ ρ ∧ ρ.zeit.zustand 0 = some vor ∧
      E.system.kopf vor eintritt = some f ∧
      ρ.zeit.spur 0 = some (.kontext eintritt (), ⟨[], []⟩) ∧
      ∀ predictor, PraefixAbgedeckt E ρ ρ predictor 0 := by
  let p := Fragment.einzel f
  let E := p.einheit .x86_64
  obtain ⟨h, s, hw, hardware, zul, konform, _, normal, bereit, kopf, transfer, vollzug⟩ :=
    Ast.Semantik.sim_formvoraussetzungen_erfuellbar f priv
  let vor := (I.start E s).2
  let nach := f.nach eintritt vor
  let event : SchrittWahl PUnit × SchrittSpur Ast.Semantik.Zelle Int := (.kontext eintritt (), ⟨[], []⟩)
  have schritt : Lauffolge E hw 0 (some vor) event (some nach) :=
    .schritt (.kontext normal bereit ⟨f, kopf, transfer⟩ vollzug)
  obtain ⟨rest, anfang⟩ := Zeitlauf.existiert (fun t => Lauffolge E hw (t + 1)) (some nach)
  let ρ : Lauf E :=
    ⟨s, hw, {
      zustand := fun | 0 => some vor | t + 1 => rest.zustand t
      spur := fun | 0 => some event | t + 1 => rest.spur t
      takt := by
        intro t
        cases t with
        | zero =>
          refine .schritt rfl ?_
          change Lauffolge E hw 0 (some vor) event (rest.zustand 0)
          rw [anfang]
          exact schritt
        | succ t =>
          cases rest.takt t with
          | schritt label schritt => exact .schritt label schritt
          | wartet label gleich pause => exact .wartet label gleich pause }⟩
  have lauf : Laeufe E h ρ := ⟨hardware, konform, zul, (fragment_geladen p .x86_64 hardware zul).symm⟩
  have vergleich : Vergleich E h h ρ ρ := ⟨lauf, lauf, rfl, rfl, rfl⟩
  have quelle := fragment_fluss_lokal p .x86_64
  exact ⟨h, ρ, vor, quelle.2 f, vergleich, rfl, kopf, rfl,
    anfang_aus_lader E (fragment_lader_ni p .x86_64 quelle.1) vergleich⟩

end Gabbro.Core.Beobachtung
