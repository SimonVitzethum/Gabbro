/-
  File:      Core/Durchstich/Klein.lean
  Subject:   THE SLICE FRAGMENT F_klein (Durchstich step 1): integers with arithmetic,
             condition, statically bounded loops, cell read/write, lock section.

  `KleinBefehl` is the machine-level predicate: which `Befehl` constructors belong to
  the slice. Allowed are the frame instructions the elaboration of integer arithmetic
  (`literal`, `binaer`, `teilen`, `vergleichen`, `negativ`, `negieren`, `verneinen`,
  `wahrheitswert`, `lesen`), bindings and assignment (`binden`, `bindeWert`,
  `zuweisen`), the condition and bounded-loop control (`springeWenn`, `springe`,
  `blockEnde`, `setzePasszahl`, `whileTest`, `zurueckSprung`, `forAnfang`, `forTest`,
  `forNaechster`), the measured-loop guard (`pruefeMass`), the unit scaffolding
  (`definiere`, `starte`, `ende`, `rueckVoid`, `zurueck`), and exactly the two plain
  access forms of MK-04 (`zugriff (.lade …)` and `zugriff (.speichere …)` in any
  mode). Everything else is outside: calls, unbounded control (`forever` needs no
  `Befehl` of its own but its elaboration is refused here by exclusion of nothing —
  see the finding), aggregates, variants, text, carriers, options, regions, outside
  calls, and the atomic updates (`tausche`, `vergleicheTausche`, `holeUndAddiere`,
  `erwarte`, `veroeffentliche`).

  FINDING (lock section, MK-05): `Wirkungsklasse.sperre` has NO `Befehl` constructor —
  `Befehl.klasse` maps every non-`zugriff` instruction to `.lokal` or `.ruf`, so no
  elaborated unit can contain a lock instruction. The lock section of F_klein is
  therefore a requirement on the elaborated unit (`AbschnittWartefrei`), not a
  machine instruction; its surface form (`locks place block`, SYNTAX §9) has no
  `Stmt` constructor either (step 2 MELDUNG).

  `F_klein t` lifts the predicate to source units through the elaborated fragment:
  every instruction of `(fragment .unit t).code` satisfies `KleinBefehl`.
-/
module

public import Core.Ast.Semantik.Runtime.Befehl
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Durchstich

open Gabbro.Core.Ast.Semantik

/-- The machine instructions of the slice: integer arithmetic, condition and
    statically bounded-loop control, cell load/store, unit scaffolding. -/
def KleinBefehl : Befehl → Prop
  | .literal .. => True
  | .binaer .. => True
  | .teilen .. => True
  | .vergleichen .. => True
  | .negativ .. => True
  | .negieren .. => True
  | .verneinen .. => True
  | .wahrheitswert .. => True
  | .lesen .. => True
  | .binden .. => True
  | .bindeWert .. => True
  | .zuweisen .. => True
  | .springeWenn .. => True
  | .springe .. => True
  | .blockEnde .. => True
  | .setzePasszahl .. => True
  | .whileTest .. => True
  | .zurueckSprung .. => True
  | .forAnfang .. => True
  | .forTest .. => True
  | .forNaechster .. => True
  | .pruefeMass .. => True
  | .definiere .. => True
  | .starte .. => True
  | .ende => True
  | .rueckVoid => True
  | .zurueck .. => True
  | .zugriff (.lade _ _ _ _ _) => True
  | .zugriff (.speichere _ _ _ _) => True
  | _ => False

/-- The slice fragment: a source unit whose elaborated code stays inside `KleinBefehl`. -/
def F_klein (t : Ast.Unit) : Prop :=
  ∀ b ∈ (fragment Ast.Category.unit t).code, KleinBefehl b

/-- The empty unit is in the slice: its code is only the `starte`/`ende` scaffolding. -/
theorem klein_leer : F_klein ⟨[], Ast.UnitBody.done⟩ := by
  intro b hb
  have code : (fragment Ast.Category.unit (⟨[], Ast.UnitBody.done⟩ : Ast.Unit)).code =
      [Befehl.starte mainName, Befehl.ende] := rfl
  rw [code] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl <;> trivial

/-- The predicate is not trivial: a call instruction is outside the slice. -/
theorem klein_nichtTrivial : ∃ b : Befehl, ¬ KleinBefehl b := by
  exact ⟨.rufe mainName [] none, by simp only [KleinBefehl, not_false_eq_true]⟩

end Gabbro.Core.Durchstich
