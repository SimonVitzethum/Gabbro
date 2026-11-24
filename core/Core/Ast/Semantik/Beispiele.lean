module

public import Core.Ast.Semantik.Formbeweise
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem kleinerWert (v : Int) (h₀ : 0 ≤ v) (h₁ : v ≤ 3) :
    waechterBedarf .ganzzahlBereich (v, Plattform.x86_64.ziel.wbits) := by
  change 0 < (64 : Nat) ∧ -(9223372036854775808 : Int) ≤ v ∧ v < 9223372036854775808
  omega

theorem literal_erfuellbar : LiteralErfuellbar := by
  intro start
  let form := literalForm []
  let s := (I.start (form.einheit .x86_64 1) start).2
  refine ⟨1, form.erfuellbar_aus_erreichbar .x86_64 start 1 s .start
    (form.realisiert (literal_am_ort []) .x86_64 1 s rfl rfl) ?_⟩
  intro g guard
  have same : (⟨.ganzzahlBereich, (1, Plattform.x86_64.ziel.wbits)⟩ : Bedarf) = g :=
    Option.some.inj guard
  subst g
  exact kleinerWert 1 (by omega) (by omega)

theorem binary_erfuellbar : BinaryErfuellbar := by
  intro start op
  let form := binaryForm []
  let args : Surface.BinaryArgs [] := ⟨op, .lit 1, .lit 2⟩
  let E := form.einheit .x86_64 args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  let s₂ := (Befehl.literal 1 2).nach eintritt s₁
  have left : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.literal 0 1, rfl, rfl, rfl⟩
  have right : E.system.ISchritt eintritt s₁ () [plan] s₂ :=
    ⟨.literal 1 2, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start left) right
  refine ⟨args, rfl, form.erfuellbar_aus_erreichbar .x86_64 start args s₂ reached
    (form.realisiert (binary_am_ort []) .x86_64 args s₂ rfl rfl) ?_⟩
  intro g guard
  have same : (⟨.ganzzahlBereich, (operation op 1 2, Plattform.x86_64.ziel.wbits)⟩ : Bedarf) = g :=
    Option.some.inj guard
  subst g
  cases op with
  | add => exact kleinerWert 3 (by omega) (by omega)
  | mul => exact kleinerWert 2 (by omega) (by omega)

theorem let_erfuellbar : LetErfuellbar := by
  intro start
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  have ordinary : name.val ≠ "mut".toList := by
    change ['x'] ≠ ['m', 'u', 't']
    intro same
    cases same
  let form := letForm []
  let args : Surface.LetArgs [] := ⟨name, ordinary, .lit 1⟩
  let E := form.einheit .x86_64 args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  have initializer : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.literal 0 1, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start initializer
  refine ⟨args, form.erfuellbar_aus_erreichbar .x86_64 start args s₁ reached
    (form.realisiert (let_am_ort []) .x86_64 args s₁ rfl rfl) ?_⟩
  intro g guard
  cases guard

def literalEntry : RegistryEntry ``Expr.lit (exprSchema ``Expr.lit) := by
  rw [exprSchema, ite_eq_left rfl]
  exact Quellform.eintrag literalForm LiteralErfuellbar ``Expr.lit Surface.literal_entry literal_am_ort
    (fun _ _ => rfl) literal_erfuellbar

def binaryEntry : RegistryEntry ``Expr.binary (exprSchema ``Expr.binary) := by
  have different : (``Expr.binary : Lean.Name) ≠ ``Expr.lit := by
    intro same
    have label : "binary" = "lit" := (Lean.Name.str.inj same).2
    simp only [String.reduceEq] at label
  rw [exprSchema, ite_eq_right different, ite_eq_left rfl]
  exact Quellform.eintrag binaryForm BinaryErfuellbar ``Expr.binary Surface.binary_entry binary_am_ort
    (fun _ args => expr_keine_invarianten 0 (.binary args.op args.left args.right)) binary_erfuellbar

def letEntry : RegistryEntry ``Stmt.letValue (stmtSchema ``Stmt.letValue) := by
  rw [stmtSchema, ite_eq_left rfl]
  exact Quellform.eintrag letForm LetErfuellbar ``Stmt.letValue Surface.letValue_entry let_am_ort
    (fun _ args => stmt_keine_invarianten (.letValue args.name args.ordinary args.value)) let_erfuellbar

end Gabbro.Core.Ast.Semantik
