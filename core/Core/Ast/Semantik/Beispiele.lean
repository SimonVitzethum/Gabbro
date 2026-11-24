module

public import Core.Ast.Semantik.Formbeweise
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter
/-- Acceptance validates the exact guard operands at any recorded ideal cut. -/
theorem Fragment.guard_am_schnitt (p : Fragment) (platform : Plattform)
    {ρ : I.Lauf (p.einheit platform)} (valid : I.Laeufe (p.einheit platform) ρ)
    (accepted : Akzeptiert (p.einheit platform)) (t : I.Schnitt (p.einheit platform) ρ)
    (c : Kontext) (b : Befehl) (g : Bedarf)
    (head : kopf p.code (ρ.zeit.zustand t.val) c = some b)
    (used : b.guard platform.ziel.wbits ((ρ.zeit.zustand t.val).lokal c) = some g) :
    waechterBedarf g.1 g.2 := by
  rcases g with ⟨op, arguments⟩
  exact accepted.2.2.1 ρ valid t op arguments ⟨c, b, head, used⟩

/-- A literal whose exact value exceeds the target range is refused at cut zero.
    The proof needs an admitted ideal run and no scheduled source transition. -/
theorem literal_ueberlauf_verweigert (platform : Plattform) (value : Nat)
    {ρ : I.Lauf ((literalForm []).einheit platform value)}
    (valid : I.Laeufe ((literalForm []).einheit platform value) ρ)
    (overflow : ¬ waechterBedarf .ganzzahlBereich (Int.ofNat value, platform.ziel.wbits)) :
    ¬ Akzeptiert ((literalForm []).einheit platform value) := by
  intro accepted
  let p := (literalForm []).fragment value
  let t : I.Schnitt (p.einheit platform) ρ := ⟨0, Or.inl rfl⟩
  have head : kopf p.code (ρ.zeit.zustand t.val) eintritt = some (.literal 0 value) := by
    change kopf p.code (ρ.zeit.zustand 0) eintritt = some (.literal 0 value)
    rw [valid.2.2.2.1]
    rfl
  exact overflow (p.guard_am_schnitt platform valid accepted t eintritt (.literal 0 value)
    ⟨.ganzzahlBereich, (Int.ofNat value, platform.ziel.wbits)⟩ head rfl)


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
