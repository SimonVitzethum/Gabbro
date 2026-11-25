/-
  File:      core/Core/Beobachtung/SchrankenBeweise/BindungOffen.lean
  Subject:   The remaining obligation families of `SchrankenbindungOffenAussage` on the
             open part of a declaration. A declaration with no cost ceiling and no hold
             entries leaves the cost/hold legs vacuous; no stack or memory ceiling leaves
             both resource legs vacuous. The per-form and protocol duties of those
             families therefore close for every form. For a finite declaration the same
             duties need a static bound premise: the footprint of `klassenSchranken` on
             the checker side and its analogue on the cost/hold side. This file records
             the unconditional half; the finite half is the exact open obligation.
-/
module

public import Core.Beobachtung.SchrankenBeweise.BindungRessourcen
public import Core.Annahme.Schranken

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The cost and hold lookups of a declaration with an empty hold list are open. -/
private theorem haltenVon_leer (d : Schrankendeklaration) (h : d.halten = []) (l : Nat) :
    d.haltenVon l = none := by
  simp only [Schrankendeklaration.haltenVon, h, List.find?_nil, Option.map_none]

/-- With no cost ceiling and no hold entries the per-form cost/hold duty is vacuous. -/
theorem bindungKHOffen (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl)
    (hkosten : u.deklaration.kosten = none) (hhalten : u.deklaration.halten = []) :
    KHRegelPflicht (einheitMitSchranken P u) f := by
  intro h ρ lauf t c w spur vor nach kostenP halteP vorEq kopf spurEq nachEq
  constructor
  · intro n eq
    rw [einheitMitSchranken_kosten, hkosten] at eq
    cases eq
  · intro l c' a n bound own
    have hl : (einheitMitSchranken P u).schranken.halten l = none := by
      rw [einheitMitSchranken_halten]
      exact haltenVon_leer u.deklaration hhalten l
    rw [hl]
    intro m eq
    cases eq

/-- The protocol cost/hold duty is vacuous under the same open declaration. -/
theorem bindungKHProtokollOffen (P : Katalog.Plattform) (u : UnitMitSchranken)
    (hkosten : u.deklaration.kosten = none) (hhalten : u.deklaration.halten = []) :
    KHProtokollPflicht (einheitMitSchranken P u) := by
  intro h ρ lauf t w spur vor nach kostenP halteP vorEq spurEq wahl nachEq
  constructor
  · intro n eq
    rw [einheitMitSchranken_kosten, hkosten] at eq
    cases eq
  · intro l c' a n bound own
    have hl : (einheitMitSchranken P u).schranken.halten l = none := by
      rw [einheitMitSchranken_halten]
      exact haltenVon_leer u.deklaration hhalten l
    rw [hl]
    intro m eq
    cases eq

/-- With no stack or memory ceiling every state meets both bounds, so the checker row's
    per-form duty is vacuous. -/
theorem bindungRegelSchrankenOffen (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl)
    (hstapel : u.deklaration.stapel = none) (hspeicher : u.deklaration.speicher = none) :
    Annahme.RegelSchranken (einheitMitSchranken P u) f := by
  intro η lauf t c w spur vor nach vorEq kopf spurEq nachEq step stapelVor speicherVor
  have hs : (einheitMitSchranken P u).schranken.stapel = none := by
    rw [einheitMitSchranken_stapel]
    exact hstapel
  have hm : (einheitMitSchranken P u).schranken.speicher = none := by
    rw [einheitMitSchranken_speicher]
    exact hspeicher
  exact ⟨stapelZustand_leer hs _, speicherZustand_leer hm _⟩

/-- The implementation per-form resource duty is vacuous under the same open ceilings. -/
theorem bindungRessourcenRegelOffen (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl)
    (hstapel : u.deklaration.stapel = none) (hspeicher : u.deklaration.speicher = none) :
    ressourcenRegelAussage (einheitMitSchranken P u) f := by
  intro h ρ lauf t c w spur vor nach vorEq kopf spurEq nachEq step stapelVor speicherVor
  have hs : (einheitMitSchranken P u).schranken.stapel = none := by
    rw [einheitMitSchranken_stapel]
    exact hstapel
  have hm : (einheitMitSchranken P u).schranken.speicher = none := by
    rw [einheitMitSchranken_speicher]
    exact hspeicher
  exact ⟨stapelZustand_leer hs _, speicherZustand_leer hm _⟩

/-- The implementation protocol resource duty is vacuous under the same open ceilings. -/
theorem bindungRessourcenProtokollOffen (P : Katalog.Plattform) (u : UnitMitSchranken)
    (hstapel : u.deklaration.stapel = none) (hspeicher : u.deklaration.speicher = none) :
    ressourcenProtokollAussage (einheitMitSchranken P u) := by
  intro h ρ lauf t w spur vor nach vorEq spurEq wahl nachEq step stapelVor speicherVor
  have hs : (einheitMitSchranken P u).schranken.stapel = none := by
    rw [einheitMitSchranken_stapel]
    exact hstapel
  have hm : (einheitMitSchranken P u).schranken.speicher = none := by
    rw [einheitMitSchranken_speicher]
    exact hspeicher
  exact ⟨stapelZustand_leer hs _, speicherZustand_leer hm _⟩

end Gabbro.Core.Beobachtung
