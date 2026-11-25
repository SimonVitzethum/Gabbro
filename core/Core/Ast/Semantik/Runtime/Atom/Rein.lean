/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Rein.lean
  Subject:   A SOURCE FRAGMENT CONTAINS NO ACCESS INSTRUCTION (MK-04). The access instructions
             (`Befehl.zugriff`) are written by the access forms of the memory model; no source form of the
             present grammar elaborates to one. Every instruction an elaborated fragment contains is therefore
             frame-only (`Befehl.Privat`), and the statements about EVERY elaborated unit that rest on the template
             step of the frame-only classes (`I.Bestimmt`, `I.Fortschritt`, the flow rule) keep holding for the
             elaborated units, while a unit that does contain an access instruction owes the duties of its class
             (`KlassenAussagen`, `ZugriffBefehlAussage`). The statement is proved once by the recursion over the
             source tree, exactly as the elaboration of the clauses (`programm_keine_invarianten`).
-/
module

public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Semantik.Runtime.Regeln

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- **A fragment is frame-only**: every instruction of its code is frame-only. -/
def Fragment.Rein (p : Fragment) : Prop := ∀ b ∈ p.code, b.Privat

theorem Fragment.rein_leer : Fragment.leer.Rein := fun _ hb => absurd hb List.not_mem_nil

theorem Fragment.rein_einzel_iff (b : Befehl) : (Fragment.einzel b).Rein ↔ b.Privat := by
  constructor
  · intro h
    exact h b (List.mem_singleton_self b)
  · intro h x hx
    rw [List.mem_singleton.mp hx]
    exact h

theorem Fragment.rein_anhaengen_iff (a b : Fragment) : (a.anhaengen b).Rein ↔ a.Rein ∧ b.Rein := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (List.mem_append.mpr (Or.inl hx)), fun x hx => h x (List.mem_append.mpr (Or.inr hx))⟩
  · intro h x hx
    exact (List.mem_append.mp hx).elim (h.1 x) (h.2 x)

theorem expr_rein (slot : Nat) (tree : Expr scope type) : (expr slot tree).Rein := by
  refine @Expr.rec scope
    (fun _ t => ∀ i, (expr i t).Rein)
    (fun _ t => ∀ i, (itemCode i t).Rein)
    (fun _ _ t => ∀ i, (labeledCode i t).Rein)
    (fun _ t => ∀ i, (caseCode i t).Rein)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ type tree slot
  all_goals
    intros
    simp_all only [expr, itemCode, labeledCode, caseCode, Fragment.rein_leer, Fragment.rein_einzel_iff,
      Fragment.rein_anhaengen_iff, true_and, and_true]
  all_goals
    repeat' first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | refine ⟨?_, ?_⟩

private theorem argsCode_rein (slot : Nat) (args : List (TypedExpr scope)) : (argsCode slot args).Rein := by
  induction args generalizing slot with
  | nil => exact Fragment.rein_leer
  | cons value rest ih =>
    simp only [argsCode, Fragment.rein_anhaengen_iff]
    exact ⟨expr_rein _ _, ih _⟩

private theorem optionCode_rein (slot : Nat) (value : OptionInitializer scope count) :
    (optionCode slot value).Rein := by
  simp only [optionCode, Fragment.rein_anhaengen_iff, Fragment.rein_einzel_iff]
  refine ⟨?_, ?_⟩
  · cases value with
    | absent => exact Fragment.rein_leer
    | present value _ => exact expr_rein _ _
  · first
      | exact Or.inl rfl
      | exact Or.inr rfl

theorem stmt_rein (tree : Stmt result before after) : (stmt tree).Rein := by
  refine @Stmt.rec result
    (fun _ _ t => (stmt t).Rein)
    (fun _ _ t => (block t).Rein)
    (fun _ t => (bracedBlock t).Rein)
    (fun _ _ _ _ t => (variantArms t).body.Rein)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ before after tree
  all_goals
    intros
    simp_all only [stmt, block, bracedBlock, variantArms, callCode, MatchCode.prepend, Bool.false_eq_true,
      ↓reduceIte, Fragment.rein_leer, Fragment.rein_einzel_iff, Fragment.rein_anhaengen_iff, expr_rein,
      argsCode_rein, optionCode_rein, true_and, and_true]
  all_goals
    repeat' first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | refine ⟨?_, ?_⟩

theorem bracedBlock_rein (tree : BracedBlock result scope) : (bracedBlock tree).Rein := by
  have both := stmt_rein (Stmt.ite .trueLit tree tree)
  simp only [stmt, expr, Fragment.rein_anhaengen_iff, Fragment.rein_einzel_iff] at both
  exact both.1.1.2

private theorem functionCode_rein {result : Option WrittenType} {scope : Scope}
    (measure : Option (Measure scope)) (body : BracedBlock (writtenResult result) scope) :
    (functionCode result measure body).Rein := by
  cases measure with
  | none =>
    simp only [functionCode, Fragment.rein_anhaengen_iff, Fragment.rein_einzel_iff, Fragment.rein_leer,
      bracedBlock_rein, true_and]
    exact Or.inl rfl
  | some m =>
    simp only [functionCode, Fragment.rein_anhaengen_iff, Fragment.rein_einzel_iff, expr_rein,
      bracedBlock_rein, true_and]
    repeat' first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | exact trivial
      | refine ⟨?_, ?_⟩

private theorem decl_rein {before after : Scope} (d : Decl before after) : (decl d).Rein := by
  cases d with
  | constant name ordinary written valid value staticValue fits =>
    simp only [decl, Fragment.rein_anhaengen_iff, Fragment.rein_einzel_iff, expr_rein, true_and]
    exact Or.inl rfl
  | function name ordinary parameters result valid decreases body distinct returns effects =>
    simp only [decl, Fragment.rein_anhaengen_iff, Fragment.rein_einzel_iff, functionCode_rein, and_true]
    exact Or.inl rfl
  | record exported name fields valid distinct =>
    simp only [decl, Fragment.rein_einzel_iff]
    exact Or.inl rfl
  | tagged exported name first tail valid distinct =>
    simp only [decl, Fragment.rein_einzel_iff]
    exact Or.inl rfl
  | table item =>
    simp only [decl, Fragment.rein_einzel_iff]
    exact Or.inl rfl
  | effectGroup item =>
    simp only [decl, Fragment.rein_einzel_iff]
    exact Or.inl rfl
  | environment name abi row =>
    simp only [decl, Fragment.rein_einzel_iff]
    exact Or.inl rfl

private theorem unitBody_rein {before after : Scope} (body : UnitBody before after) : (unitBody body).Rein := by
  induction body with
  | done => exact Fragment.rein_leer
  | step first rest ih =>
    simp only [unitBody, Fragment.rein_anhaengen_iff]
    exact ⟨decl_rein first, ih⟩

theorem programm_rein (tree : Ast.Unit) : (programm tree).Rein := by
  simp only [programm, Fragment.rein_anhaengen_iff, Fragment.rein_einzel_iff, unitBody_rein, true_and]
  exact ⟨Or.inr rfl, Or.inl rfl⟩

/-- **Every elaborated fragment of every category is frame-only.** -/
theorem fragment_rein (category : Category) (tree : category.Tree) : (fragment category tree).Rein := by
  cases category with
  | expression scope => exact expr_rein _ _
  | statement scope result => exact stmt_rein _
  | block scope result => exact bracedBlock_rein _
  | unit => exact programm_rein tree
  | declaration scope => exact decl_rein _

end Gabbro.Core.Ast.Semantik
