/-
  File:      Core/Ziel/Review/Slice/Surface.lean
  Subject:   SURFACE COVERAGE of F_klein (Durchstich step 2): for every form of the slice,
             parsing, printing and elaboration exist — except the two findings below,
             which are MELDUNG, not built here (a parallel task owns them).

  COVERED (witnessed by the aliased entries; the build checks they exist):
  * integer literal and arithmetic: `Surface.literal_entry`, `Surface.binary_entry`,
    elaboration `Semantik.literalEntry`, `Semantik.binaryEntry`;
  * condition: `Surface.ifElse_entry`, elaboration `Semantik.ifElseEntry`;
  * statically bounded loops: `Surface.boundedWhile_entry`, `Surface.forRange_entry`,
    elaboration `Semantik.boundedWhileEntry`, `Semantik.forRangeEntry`.

  MELDUNG M1 (closed by MK-04b) — the statement `mem load` / `mem store` (`Stmt.access`) elaborates to
  `Befehl.zugriff`, so an elaborated fragment is no longer frame-only in general
  (`Fragment.KlassenRein`, `Atom/Klassenrein`); the slice grammar F_klein has no access statement, so
  its fragments stay `Rein`.

  MELDUNG M2 — no surface syntax for the lock section: SYNTAX §9 has
  `lockstmt = "locks" … block`, but `Stmt` has no lock constructor, and
  `Wirkungsklasse.sperre` has no `Befehl` constructor (`sperre_ohne_befehl`
  below). The wait-free section row `AbschnittWartefrei` therefore constrains
  elaborated units whose code cannot contain a lock instruction yet.
-/
module

public import Core.Ziel.Review.Slice.Fragment
public import Core.Ast.Surface
public import Core.Ast.Program.BatchSurface
public import Core.Ast.Program.SurfaceForms
public import Core.Ast.Semantik.Beispiele
public import Core.Ast.Semantik.BatchRegistry
public import Core.Ast.ProgramRegistry.BoundedWhile
public import Core.Ast.ProgramRegistry.ForRange
public import Core.Ast.Semantik.Runtime.Atom.Rein

@[expose] public section

namespace Gabbro.Core.Ziel.Review.Slice

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Parsing and printing of integer literals exist (inventory `surface.SExpr.lit`). -/
theorem klein_literal_vorhanden (scope : Scope) : (Surface.literal scope).Entry :=
  Surface.literal_entry scope

/-- Parsing and printing of infix arithmetic exist (inventory `surface.SExpr.bin`). -/
theorem klein_binaer_vorhanden (scope : Scope) :
    (Surface.binary scope).Entry :=
  Surface.binary_entry scope

/-- Parsing and printing of the condition exist. -/
theorem klein_entscheidung_vorhanden (scope : Scope) (result : Option (Ty .value)) :
    (Surface.ifElse scope result).Entry :=
  Surface.ifElse_entry scope result

/-- Parsing and printing of the statically bounded `while` loop exist. -/
theorem klein_while_vorhanden (scope : Scope) (result : Option (Ty .value)) :
    (Surface.boundedWhile scope result).Entry :=
  Surface.boundedWhile_entry scope result

/-- Parsing and printing of the statically bounded `for` loop exist. -/
theorem klein_for_vorhanden (scope : Scope) (result : Option (Ty .value)) :
    (Surface.forRange scope result).Entry :=
  Surface.forRange_entry scope result

/-- The elaboration registry covers the arithmetic and condition forms of the slice. -/
noncomputable def klein_elab_arithmetik := (literalEntry, binaryEntry, ifElseEntry)

/-- The elaboration registry covers the bounded-loop forms of the slice. -/
noncomputable def klein_elab_schleifen := (boundedWhileProofs, forRangeProofs)

/-- MELDUNG M2, formal side: no instruction has a lock class, so the lock section
    of F_klein has no machine instruction yet (`Wirkungsklasse.sperre` is empty
    at the `Befehl` level). -/
theorem sperre_ohne_befehl (b : Befehl) (a : Maschine.SperrAktion) :
    b.klasse ≠ .sperre a := by
  cases b <;> simp only [Befehl.klasse, ne_eq, reduceCtorEq, not_false_eq_true]
  all_goals
    rename_i form
    cases form <;> simp only [Zugriffsform.klasse, Fadenform.klasse, AussenfrageformKlasse,
      reduceCtorEq, not_false_eq_true]

end Gabbro.Core.Ziel.Review.Slice
