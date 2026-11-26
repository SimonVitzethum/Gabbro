/-
  File:      core/Core/Ziel/Korrektheit/Beweise/FormBelegBasis.lean
  Subject:   A TYPED form certificate for one cohesive family of already implemented and accepted
             scalar arithmetic expression constructors (`Expr.lit`, `Expr.binary`).

  The global registry evidence in `BegleitZusammensetzung.lean` (`beleg`, `beleg_gedeckt`) is the
  Unit placeholder: it does not distinguish forms. This module does NOT replace that placeholder
  and does not touch `R₀`, any Zielsatz or a pin. It adds a separate certificate whose `Form` is a
  real inductive indexed by two existing constructors, proves `FormenGedecktAussage` for it with
  accepted source units, and proves that each form is backed by an existing typed `RegistryEntry`
  of the root-imported `exprSchema` family. All evidence is reused: source parse via
  `Ast.parse_print`, elaboration and admission via `elab_korrekt`/`zugelassen`, acceptance via
  `Fragment.akzeptiert_ohne_bedarf`, and the occurrence via the elaborated code of the unit.
-/
module

public import Core.Ziel.Korrektheit.Zusammensetzung
public import Core.Ast.Semantik.Beispiele

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Katalog
open Gabbro.Core.Waechter

/-- The basic scalar arithmetic family: exactly the two registered expression constructors for
    which `exprSchema` supplies complete Parse/Elaboriert/Realisiert/locality/satisfiability
    evidence in the root build (`literalEntry`, `binaryEntry`). -/
inductive BasisForm where
  | lit
  | binary

/-- A reserved ordinary name for the single constant of a witness unit. -/
def basisName : Identifier :=
  keywordName 'x' [] (by decide) (fun _ member => (List.not_mem_nil member).elim)

theorem basisName_ordinary : ordinaryLocal basisName :=
  (directName_of_singleton (name := basisName) rfl).1

/-- A source unit whose only declaration computes one basic arithmetic expression. -/
def basisUnit : BasisForm → Ast.Unit
  | .lit =>
      let written : WrittenType := .integer false 8 none
      let value : Expr [] (.int 1 1) := .lit 1
      ⟨[⟨basisName, .int 0 255, false, true⟩],
        .step (.constant basisName basisName_ordinary written
          (by
            change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
            omega) value
          (by trivial)
          (by
            change (0 : Int) ≤ 1 ∧ (1 : Int) ≤ 255
            omega)) .done⟩
  | .binary =>
      let written : WrittenType := .integer false 8 none
      let value : Expr [] (.int 3 3) := .binary .add (.lit 1) (.lit 2)
      ⟨[⟨basisName, .int 0 255, false, true⟩],
        .step (.constant basisName basisName_ordinary written
          (by
            change 1 ≤ 8 ∧ 8 ≤ 64 ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 255 ∧ (255 : Int) ≤ 255
            omega) value
          (by trivial)
          (by
            change (0 : Int) ≤ 3 ∧ (3 : Int) ≤ 255
            omega)) .done⟩

/-- The elaborated code of each witness unit, used for admission and acceptance. -/
theorem basisUnit_code_lit :
    (Ast.Semantik.fragment Ast.Category.unit (basisUnit .lit)).code =
      [.literal 0 1, .bindeWert 0 (.int 0 255) true,
        .starte Ast.Semantik.mainName, .ende] := rfl

theorem basisUnit_code_binary :
    (Ast.Semantik.fragment Ast.Category.unit (basisUnit .binary)).code =
      [.literal 0 1, .literal 1 2, .binaer .add 0,
        .bindeWert 0 (.int 0 255) true, .starte Ast.Semantik.mainName, .ende] := rfl

/-- Each witness unit is admitted on every platform: its code is frame-only and its type is
    platform-independent. -/
theorem basisUnit_zugelassen (f : BasisForm) (P : Plattform) :
    Ast.Semantik.zugelassen P Ast.Category.unit (basisUnit f) := by
  cases f
  · change (Ast.Semantik.fragment Ast.Category.unit (basisUnit .lit)).environmentAllowed P.katalog ∧
      (Ast.Semantik.fragment Ast.Category.unit (basisUnit .lit)).code.all
        (Ast.Semantik.Befehl.platformAllowed P) = true
    refine ⟨⟨List.nodup_nil, ?_⟩, ?_⟩
    · intro e present
      cases present
    · rw [basisUnit_code_lit]
      simp only [Ast.Semantik.Befehl.platformAllowed, Ast.Semantik.platformType,
        List.all_cons, List.all_nil, Bool.true_and]
  · change (Ast.Semantik.fragment Ast.Category.unit (basisUnit .binary)).environmentAllowed P.katalog ∧
      (Ast.Semantik.fragment Ast.Category.unit (basisUnit .binary)).code.all
        (Ast.Semantik.Befehl.platformAllowed P) = true
    refine ⟨⟨List.nodup_nil, ?_⟩, ?_⟩
    · intro e present
      cases present
    · rw [basisUnit_code_binary]
      simp only [Ast.Semantik.Befehl.platformAllowed, Ast.Semantik.platformType,
        List.all_cons, List.all_nil, Bool.true_and]

/-- Each witness unit has no clauses, no guarded instruction and only frame-only code, so it is
    accepted by the existing guard-free-fragment rule. -/
theorem basisUnit_akzeptiert (f : BasisForm) (P : Plattform) :
    Annahme.Akzeptiert (einheitVon P (basisUnit f)) := by
  cases f
  · let p := Ast.Semantik.fragment Ast.Category.unit (basisUnit .lit)
    change Annahme.Akzeptiert (p.einheit P)
    refine Ast.Semantik.Fragment.akzeptiert_ohne_bedarf p P ?_ ?_ ?_
    · rfl
    · intro b present
      rw [basisUnit_code_lit] at present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with same | same | same | same
      · subst same
        exact Or.inl rfl
      · subst same
        exact Or.inl rfl
      · subst same
        exact Or.inr (Or.inl rfl)
      · subst same
        exact Or.inl rfl
    · intro b present frame
      rw [basisUnit_code_lit] at present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with same | same | same | same <;> subst same <;> rfl
  · let p := Ast.Semantik.fragment Ast.Category.unit (basisUnit .binary)
    change Annahme.Akzeptiert (p.einheit P)
    refine Ast.Semantik.Fragment.akzeptiert_ohne_bedarf p P ?_ ?_ ?_
    · rfl
    · intro b present
      rw [basisUnit_code_binary] at present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with same | same | same | same | same | same
      · subst same
        exact Or.inl rfl
      · subst same
        exact Or.inl rfl
      · subst same
        exact Or.inl rfl
      · subst same
        exact Or.inl rfl
      · subst same
        exact Or.inr (Or.inl rfl)
      · subst same
        exact Or.inl rfl
    · intro b present frame
      rw [basisUnit_code_binary] at present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with same | same | same | same | same | same <;> subst same <;> rfl

/-- The typed form certificate: a form occurs through the printed source unit of its family, and
    its realisation is that exact unit's elaboration. -/
def basisBeleg : FormBeleg where
  Form := BasisForm
  enthaelt a f := a = Ast.print (category := Ast.Category.unit) (basisUnit f)
  realisiert f a E := a = Ast.print (category := Ast.Category.unit) (basisUnit f) ∧
    E = einheitVon Plattform.x86_64 (basisUnit f)

/-- Every form of the family occurs in an accepted source unit and is realised there: the form
    coverage leg (`FormenGedecktAussage`) holds for the typed certificate. -/
theorem basisBeleg_gedeckt : FormenGedecktAussage Plattform.x86_64 basisBeleg := by
  intro f
  refine ⟨Ast.print (category := Ast.Category.unit) (basisUnit f),
    einheitVon Plattform.x86_64 (basisUnit f), ?_, ?_, ?_, ?_⟩
  · simp [basisBeleg]
  · exact ⟨basisUnit f, Ast.parse_print (category := Ast.Category.unit) (basisUnit f),
      ⟨rfl, basisUnit_zugelassen f Plattform.x86_64⟩⟩
  · exact basisUnit_akzeptiert f Plattform.x86_64
  · simp [basisBeleg]

/-- The family is genuinely backed by the existing registry: each form maps to a constructor of
    the root-imported `Expr` family whose complete typed `RegistryEntry` is already registered. -/
def basisFormConstructor : BasisForm → Lean.Name
  | .lit => ``Expr.lit
  | .binary => ``Expr.binary

theorem basisForm_registry_covered (f : BasisForm) :
    Nonempty (RegistryEntry (basisFormConstructor f) (exprSchema (basisFormConstructor f))) := by
  cases f
  · exact ⟨literalEntry⟩
  · exact ⟨binaryEntry⟩

end Gabbro.Core.Ziel.Korrektheit
