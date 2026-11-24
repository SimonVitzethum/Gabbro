module

public import Core.Ast.Semantik.Formbeweise
public import Core.Ast.Semantik.Auswertung
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter
open Gabbro.Core.Text (PrintedToken)
/-- Acceptance validates the exact guard operands at any recorded ideal cut. -/
theorem Fragment.guard_am_schnitt (p : Fragment) (platform : Plattform)
    {ρ : I.Lauf (p.einheit platform)} (valid : I.Laeufe (p.einheit platform) ρ)
    (accepted : Akzeptiert (p.einheit platform)) (t : I.Schnitt (p.einheit platform) ρ)
    (c : Kontext) (b : Befehl) (g : Bedarf)
    (head : kopf p.code (ρ.zeit.zustand t.val) c = some b)
    (used : b.guard ((ρ.zeit.zustand t.val).lokal c) = some g) :
    waechterBedarf g.1 g.2 := by
  rcases g with ⟨op, arguments⟩
  exact accepted.2.2.1 ρ valid t op arguments ⟨c, b, head, used⟩

/-- An out-of-range literal cannot be represented as a value of the declared
    type, and explicit narrowing of that exact value fails the pinned guard. -/
theorem literal_ausserhalb_verweigert (value : Int) (outside : value < lo ∨ hi < value) :
    (¬ ∃ n : Wert (.int lo hi), n.wert = value) ∧
      ¬ waechterBedarf .ganzzahlBereich (ganzzahlBereichOperanden value lo hi) := by
  constructor
  · rintro ⟨n, rfl⟩
    exact outside.elim (Int.not_lt_of_ge n.unten) (Int.not_lt_of_ge n.oben)
  · intro guard
    obtain ⟨lower, upper⟩ := (ganzzahlBereich_iff value lo hi).mp guard
    exact outside.elim (Int.not_lt_of_ge lower) (Int.not_lt_of_ge upper)

/-- Both refusals hold for an actual singleton-typed literal. -/
theorem literal_zwei_passt_nicht_in_null_bis_eins :
    (¬ ∃ n : Wert (.int 0 1), n.wert = (Expr.lit (scope := []) 2).wert.wert) ∧
      ¬ waechterBedarf .ganzzahlBereich (ganzzahlBereichOperanden 2 0 1) :=
  literal_ausserhalb_verweigert 2 (Or.inr (by omega))

/-- Ordinary infix syntax infers the singleton range of the sum. -/
theorem eins_plus_zwei :
    Ast.Parse (category := .expression []) ['1', ' ', '+', ' ', '2', ' ']
      (show Expr [] (.int 3 3) from .binary .add (.lit 1) (.lit 2)).typed := by
  let tokens := [printInteger 1, Arith.add.print, printInteger 2]
  obtain ⟨pieces, lexed, aligned⟩ := PrintedToken.renderLexed 0 tokens
  have spelling : PrintedToken.render tokens = ['1', ' ', '+', ' ', '2', ' '] := by
    change Nat.toDigits 10 1 ++ ' ' :: '+' :: ' ' :: (Nat.toDigits 10 2 ++ [' ']) = _
    rw [Nat.toDigits_of_lt_base (by omega : 1 < 10), Nat.toDigits_of_lt_base (by omega : 2 < 10)]
    rw [Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_two.mpr rfl]
    rfl
  rw [spelling] at lexed
  apply (Category.expression []).syntax.parse_iff.mpr
  refine ⟨pieces, lexed, ?_⟩
  rw [aligned]
  exact .atom .lit (.binary .add (Nat.zero_le _) (.atom .lit (.stop noOperatorAtEnd))
    (.stop noOperatorAtEnd))

theorem literal_erfuellbar : LiteralErfuellbar := by
  intro platform start
  let form := literalForm []
  let s := (I.start (form.einheit platform 1) start).2
  refine ⟨1, form.erfuellbar_aus_erreichbar platform start 1 s .start
    (form.realisiert (literal_am_ort []) platform 1 s rfl rfl) ?_⟩
  intro g guard
  cases guard

theorem binary_erfuellbar : BinaryErfuellbar := by
  intro platform start op
  let form := binaryForm []
  let args : Surface.BinaryArgs [] := ⟨op, .lit 1, .lit 2⟩
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  let s₂ := (Befehl.literal 1 2).nach eintritt s₁
  have left : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.literal 0 1, rfl, rfl, rfl⟩
  have right : E.system.ISchritt eintritt s₁ () [plan] s₂ :=
    ⟨.literal 1 2, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start left) right
  refine ⟨args, rfl, form.erfuellbar_aus_erreichbar platform start args s₂ reached
    (form.realisiert (binary_am_ort []) platform args s₂ rfl rfl) ?_⟩
  intro g guard
  cases guard

theorem let_erfuellbar : LetErfuellbar := by
  intro platform start
  let name : Identifier :=
    ⟨['x'], 'x', [], rfl, Or.inl (Or.inl ⟨by change 97 ≤ 120; omega, by change 120 ≤ 122; omega⟩),
      fun _ member => (List.not_mem_nil member).elim⟩
  have ordinary : name.val ≠ "mut".toList := by
    change ['x'] ≠ ['m', 'u', 't']
    intro same
    cases same
  let form := letForm []
  let args : Surface.LetArgs [] := ⟨name, ordinary, .lit 1⟩
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 1).nach eintritt s₀
  have initializer : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.literal 0 1, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₁ := .schritt eintritt () [plan] .start initializer
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₁ reached
    (form.realisiert (let_am_ort []) platform args s₁ rfl rfl) ?_⟩
  intro g guard
  cases guard

def literalEntry : RegistryEntry ``Expr.lit (exprSchema ``Expr.lit) := by
  rw [exprSchema, ite_eq_left rfl]
  exact Quellform.eintrag literalForm LiteralErfuellbar ``Expr.lit Surface.literal_entry literal_am_ort
    (fun _ _ => rfl) literal_erfuellbar

theorem binary_ne_lit : (``Expr.binary : Lean.Name) ≠ ``Expr.lit := by
  intro same
  have label : "binary" = "lit" := (Lean.Name.str.inj same).2
  simp only [String.reduceEq] at label

def binaryEntry : RegistryEntry ``Expr.binary (exprSchema ``Expr.binary) := by
  rw [exprSchema, ite_eq_right binary_ne_lit, ite_eq_left rfl]
  exact Quellform.eintrag binaryForm BinaryErfuellbar ``Expr.binary Surface.binary_entry binary_am_ort
    (fun _ args => expr_keine_invarianten 0 (.binary args.op args.left args.right)) binary_erfuellbar

def letEntry : RegistryEntry ``Stmt.letValue (stmtSchema ``Stmt.letValue) := by
  rw [stmtSchema, ite_eq_left rfl]
  exact Quellform.eintrag letForm LetErfuellbar ``Stmt.letValue Surface.letValue_entry let_am_ort
    (fun _ args => stmt_keine_invarianten (.letValue args.name args.ordinary args.value)) let_erfuellbar

end Gabbro.Core.Ast.Semantik
