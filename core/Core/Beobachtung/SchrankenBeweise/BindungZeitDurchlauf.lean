/-
  File:      core/Core/Beobachtung/SchrankenBeweise/BindungZeitDurchlauf.lean
  Subject:   The clock and per-pass obligation families of `SchrankenbindungOffenAussage`
             over bound units. `einheitMitSchranken` fixes both mark stands to the empty
             list, so `ZeitPrefix` and `DurchlaufPrefix` hold at every cut of every run.
             The per-form and protocol duties of both families therefore close with no
             premise, for every declaration and every form. This is an unconditional
             part of the open statement; the cost/hold and resource families are not
             vacuous and are treated separately.
-/
module

public import Core.Beobachtung.SchrankenBeweise.Bindung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- At every cut of a bound unit every per-pass mark is absent: the stand is the empty list. -/
theorem bindungDurchlaufRegel (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl) :
    DurchlaufRegelPflicht (einheitMitSchranken P u) f := by
  intro h ρ lauf t c w spur vor nach hyp vorEq kopf spurEq nachEq
  intro t' s hle sEq c' m hmem
  have leer : (einheitMitSchranken P u).schranken.durchlaufstand (s.lokal c') = [] := rfl
  rw [leer] at hmem
  exact (List.not_mem_nil hmem).elim

/-- At every cut of a bound unit every time mark is absent: the stand is the empty list. -/
theorem bindungZeitRegel (P : Katalog.Plattform) (u : UnitMitSchranken) (f : Befehl) :
    ZeitRegelPflicht (einheitMitSchranken P u) f := by
  intro h ρ lauf t c w spur vor nach hyp vorEq kopf spurEq nachEq
  intro t' s hle sEq c' m hmem
  have leer : (einheitMitSchranken P u).schranken.zeitstand (s.lokal c') = [] := rfl
  rw [leer] at hmem
  exact (List.not_mem_nil hmem).elim

/-- The per-pass protocol duty of a bound unit: the successor stand is empty. -/
theorem bindungDurchlaufProtokoll (P : Katalog.Plattform) (u : UnitMitSchranken) :
    DurchlaufProtokollPflicht (einheitMitSchranken P u) := by
  intro h ρ lauf t w spur vor nach hyp vorEq spurEq wahl nachEq
  intro t' s hle sEq c' m hmem
  have leer : (einheitMitSchranken P u).schranken.durchlaufstand (s.lokal c') = [] := rfl
  rw [leer] at hmem
  exact (List.not_mem_nil hmem).elim

/-- The time protocol duty of a bound unit: the successor stand is empty. -/
theorem bindungZeitProtokoll (P : Katalog.Plattform) (u : UnitMitSchranken) :
    ZeitProtokollPflicht (einheitMitSchranken P u) := by
  intro h ρ lauf t w spur vor nach hyp vorEq spurEq wahl nachEq
  intro t' s hle sEq c' m hmem
  have leer : (einheitMitSchranken P u).schranken.zeitstand (s.lokal c') = [] := rfl
  rw [leer] at hmem
  exact (List.not_mem_nil hmem).elim

end Gabbro.Core.Beobachtung
