/-
  File:      core/Core/Ziel/Korrektheit/SchrankenAkzeptiert.lean
  Subject:   THE PROOF of `SchrankenAkzeptiertAussage`, the pinned bounds leg of the goal theorem
             (`Core/Ziel/Korrektheit/Zusammensetzung.lean`).

  The leg asks every run of an accepted elaborated unit to meet `ImSchranken`, now including the
  `DurchlaufPrefix` leg. Elaboration binds `Schrankendaten.leer`: no cost, hold, time, stack,
  memory or per-pass ceiling is declared, and no mark or stand is ever visible. Each conjunct is
  therefore discharged by an absent bound or an empty stand; the assembly goes through
  `b8_abschluss_imSchranken` (the B8 bundle plus the two resource legs), and the per-pass bundle is
  supplied by `durchlauf_aus_pflichten` over vacuous `DurchlaufPflichten`. Acceptance is stronger
  than needed and is not used.

  The non-vacuous case is the open M9 work: bind declared bounds into `Fragment.einheit` and
  discharge the per-form duties. The per-pass rule obligation per form and `ProtokollMarkenErhaltend`
  are named in `SchrankenBeweise/DurchlaufEinheit.lean`; the unrestricted protocol duty is refuted
  there, so the premise cannot be dropped. The B8 rule and time duties and the B9/B21 bridge remain
  open. No statement is pinned here and no witness or per-program fact is used.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Beobachtung.SchrankenB8
public import Core.Beobachtung.SchrankenB9B21
public import Core.Beobachtung.SchrankenBeweise.Durchlauf

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Beobachtung

/-- The per-pass obligations of an elaborated unit are vacuous: no context's local state carries a
    mark stand, so the start duty, every form duty and the shared protocol duty hold at every
    prefix. This supplies the premise of `durchlauf_aus_pflichten` without any per-pass rule work. -/
private theorem durchlaufPflichtenLeer (P : Katalog.Plattform) (t : Ast.Unit) :
    DurchlaufPflichten (einheitVon P t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h ρ lauf t' s hle sEq c m hmem
    change m ∈ ([] : List (Nat × Nat)) at hmem
    cases hmem
  · intro f h ρ lauf t' c w spur vor nach hyp vorEq kopf spurEq nachEq t'' s hle sEq c' m hmem
    change m ∈ ([] : List (Nat × Nat)) at hmem
    cases hmem
  · intro h ρ lauf t' w spur vor nach hyp vorEq spurEq wahl nachEq t'' s hle sEq c m hmem
    change m ∈ ([] : List (Nat × Nat)) at hmem
    cases hmem

/-- EVERY RUN OF AN ACCEPTED ELABORATED UNIT STAYS IN ITS DECLARED BOUNDS (the pinned
    `SchrankenAkzeptiertAussage`). The elaborated unit declares none, so the B8 bundle and the two
    resource legs are vacuous and `b8_abschluss_imSchranken` closes; acceptance is not used. -/
theorem schrankenAkzeptiert (P : Katalog.Plattform) : SchrankenAkzeptiertAussage P := by
  intro t _ H ρ lauf
  let E := einheitVon P t
  have durchlauf : ∀ t', DurchlaufPrefix E ρ t' :=
    durchlauf_aus_pflichten (durchlaufPflichtenLeer P t) lauf
  have b8 : B8Abschluss E ρ := by
    refine ⟨?_, ?_, durchlauf, ?_⟩
    · intro l c a n own m hm
      change (none : Option Nat) = some m at hm
      cases hm
    · intro t' m hm
      change (none : Option Nat) = some m at hm
      cases hm
    · intro t' s sEq c m hmem
      change m ∈ ([] : List Zeitmarke) at hmem
      cases hmem
  have speicher : ∀ t' s, ρ.zeit.zustand t' = some s →
      ∀ n, E.schranken.speicher = some n → (LebendeZellen s).encard ≤ n := by
    intro t' s hs n hn
    change (none : Option Nat) = some n at hn
    cases hn
  have stapel : ∀ t' s, ρ.zeit.zustand t' = some s →
      ∀ c, UnterGrenze E.schranken.stapel (E.schranken.stapelTiefe (s.lokal c)) := by
    intro t' s hs c n hn
    change (none : Option Nat) = some n at hn
    cases hn
  exact b8_abschluss_imSchranken.mp ⟨b8, speicher, stapel⟩

end Gabbro.Core.Ziel.Korrektheit
