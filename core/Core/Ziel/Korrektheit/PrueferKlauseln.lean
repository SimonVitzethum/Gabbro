/-
  File:      core/Core/Ziel/Korrektheit/PrueferKlauseln.lean
  Subject:   SOUNDNESS and COMPLETENESS of the clause component of the checker, for the two
             pinned statements `PrueferKlauselnKorrektAussage` and
             `PrueferKlauselnVollstaendigAussage` of `Core/Ziel/Korrektheit/Pruefer.lean`.

  The checker is asked about plain source units (`Ast.Unit`). Elaboration of such a unit
  (`fragment .unit`, `programmMitInvarianten` with the empty predicate list) gives it an empty
  clause table in every kind: requires, ensures and invariants are lists over which `KlauselnWahr`
  quantifies. Hence `KlauselnWahr (einheitVon P t)` holds for every plain unit, independently of the
  unit's code, and SOUNDNESS of the clause component holds for every checker at all (the premise is
  never needed). This is recorded as `einheitVon_klauselnWahr` and
  `prueferKlauselnKorrekt_alle`.

  COMPLETENESS is not universal: a checker whose clause verdict is constantly `false` and whose
  fragment is total violates it on every plain unit. The exact missing premise is named by
  `prueferKlauselnVollstaendig_unterPraemisse`: the clause decision must accept every unit of its
  own fragment, `∀ P t, fragmentKlauseln P t = true → pruefeKlauseln P t = true`. A decidable
  checker built from `pruefeStart`/`pruefeNeustart` on the declared predicate list satisfies it
  (`prueferKlauselnVollstaendig_fuerDecidierbar`).

  PARTIAL RESULT and MISSING STEP. `pruefeKlauselnMit_richtig` shows that the loader and
  crash-recovery decisions agree exactly with the denotations of any declared predicate list, using
  `werteAus_richtig` through `pruefeStart_richtig`/`pruefeNeustart_richtig`. What is not decided here
  is the full `KlauselnWahr` of a unit that declares invariants (`UnitMitInvarianten`): it asks the
  invariant at every ideal cut of every `I` run. The available decisions cover the start, restart
  and per-command preservation premises (`pruefeEinheit_start`, `pruefeEinheit_neustart`,
  `pruefeEinheit_befehl`, `Praedikat.haelt_stabil`); the missing step is the induction over
  `I.Laeufe` carrying the invariant across command steps together with the equality of the ideal
  start content and the memory plan. The pinned statements quantify only over plain units, so they
  are proved in full below; the invariant-carrying case is stated as the open step, not claimed.
-/
module

public import Core.Ziel.Korrektheit.Pruefer

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Ast.Semantik

/-- A plain source unit carries no written clause: its elaborated clause table is empty in all three
    kinds. -/
theorem einheitVon_klauselnLeer (P : Katalog.Plattform) (t : Ast.Unit) :
    (einheitVon P t).quelltabellen.klauseln = ⟨[], [], []⟩ := by
  rfl

/-- Every plain source unit satisfies `KlauselnWahr`: the three components quantify over empty
    clause lists. -/
theorem einheitVon_klauselnWahr (P : Katalog.Plattform) (t : Ast.Unit) :
    Annahme.KlauselnWahr (einheitVon P t) := by
  intro ρ hρ
  exact ⟨fun p hp => by cases hp, fun t hp hp2 => by cases hp2,
    fun t ht hp hp2 => by cases hp2⟩

/-- SOUNDNESS of the clause component holds for every checker, because its conclusion holds for
    every unit the checker is asked about. -/
theorem prueferKlauselnKorrekt_alle (C : Pruefer) : PrueferKlauselnKorrektAussage C := by
  intro P t _
  exact einheitVon_klauselnWahr P t

/-- COMPLETENESS of the clause component under the exact missing premise: the decision accepts
    every unit of its fragment. With `KlauselnWahr` true for every plain unit, this premise is also
    necessary. -/
theorem prueferKlauselnVollstaendig_unterPraemisse (C : Pruefer)
    (h : ∀ P t, C.fragmentKlauseln P t = true → C.pruefeKlauseln P t = true) :
    PrueferKlauselnVollstaendigAussage C := by
  intro P t hf _
  exact h P t hf

/-- The decidable clause decision over a declared predicate list: the loader premise on the
    elaborated unit's memory plan conjoined with the crash-recovery premise. -/
def pruefeKlauselnMit (P : Katalog.Plattform) (t : Ast.Unit)
    (ps : List Praedikat) : Bool :=
  pruefeStart (einheitVon P t).einrichtung.initial ps && pruefeNeustart ps

/-- The decision agrees with the denotation of every declared predicate, at the loader content and
    after crash recovery. -/
theorem pruefeKlauselnMit_richtig (P : Katalog.Plattform) (t : Ast.Unit)
    (ps : List Praedikat) :
    pruefeKlauselnMit P t ps = true ↔
      (∀ q ∈ ps, q.haelt (einheitVon P t).einrichtung.initial) ∧
      (∀ q ∈ ps, q.haelt (fun _ => 0)) := by
  simp only [pruefeKlauselnMit, Bool.and_eq_true, pruefeStart_richtig, pruefeNeustart_richtig]

/-- A checker whose clause component is the decidable decision above, on the empty predicate list
    a plain unit declares, and whose fragment is total. -/
def prueferKlauselnDecidierbar : Pruefer where
  pruefeLokal := fun _ _ => true
  pruefeKlauseln := fun P t => pruefeKlauselnMit P t []
  pruefeWaechter := fun _ _ => true
  fragmentLokal := fun _ _ => true
  fragmentKlauseln := fun _ _ => true
  fragmentWaechter := fun _ _ => true

/-- SOUNDNESS for the decidable checker. -/
theorem prueferKlauselnKorrekt_fuerDecidierbar :
    PrueferKlauselnKorrektAussage prueferKlauselnDecidierbar :=
  prueferKlauselnKorrekt_alle _

/-- COMPLETENESS for the decidable checker: its clause verdict is true on its whole fragment. -/
theorem prueferKlauselnVollstaendig_fuerDecidierbar :
    PrueferKlauselnVollstaendigAussage prueferKlauselnDecidierbar := by
  intro P t _ _
  rfl

/-- The checker that refuses every unit and whose fragment is total. -/
def prueferKlauselnVerweigert : Pruefer where
  pruefeLokal := fun _ _ => false
  pruefeKlauseln := fun _ _ => false
  pruefeWaechter := fun _ _ => false
  fragmentLokal := fun _ _ => true
  fragmentKlauseln := fun _ _ => true
  fragmentWaechter := fun _ _ => true

/-- COMPLETENESS is not a property of every checker: the refuse-everything checker violates it on
    any plain unit. The premise `prueferKlauselnVollstaendig_unterPraemisse` is therefore necessary. -/
theorem prueferKlauselnVollstaendig_nichtUniversal :
    ∃ C : Pruefer, ¬ PrueferKlauselnVollstaendigAussage C := by
  refine ⟨prueferKlauselnVerweigert, ?_⟩
  intro h
  have hf : prueferKlauselnVerweigert.pruefeKlauseln Katalog.Plattform.x86_64
      ⟨[], Ast.UnitBody.done⟩ = true :=
    h Katalog.Plattform.x86_64 ⟨[], Ast.UnitBody.done⟩ rfl
      (einheitVon_klauselnWahr _ _)
  cases hf

end Gabbro.Core.Ziel.Korrektheit
