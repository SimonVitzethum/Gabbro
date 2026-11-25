/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Rein.lean
  Subject:   FRAME-ONLY ELABORATED FRAGMENTS. Every instruction an elaborated fragment contains is frame-only
             (`Befehl.Privat`) -- unless the source names an access form (`Stmt.access`, MK-04b), which
             elaborates to `Befehl.zugriff`, or a lifecycle instruction (`Befehl.faden`) arrives from outside the
             source trees. The unconditional form ("every elaborated fragment is frame-only") is therefore false,
             with a `mem load` as witness; the statements below carry the code property as premise. The template
             legs of the frame-only classes (`I.Bestimmt`, `I.Fortschritt`, the flow rule) apply to the fragments
             that meet it, while a unit that does contain an access instruction owes the duties of its class
             (`KlassenAussagen`, `ZugriffBefehlAussage`). The expression side holds unconditionally: no expression
             elaborates to an access.
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
      | exact Or.inr (Or.inl rfl)
      | refine ⟨?_, ?_⟩

<<<<<<< HEAD
/-- A binding statement is frame-only. -/
theorem stmt_letValue_rein (name : Identifier) (ordinary : name.val ≠ "mut".toList) (value : Expr scope type) :
    (stmt (Stmt.letValue (result := result) name ordinary value)).Rein := by
  simp only [stmt, Fragment.rein_anhaengen_iff, Fragment.rein_einzel_iff, expr_rein, true_and]
  exact Or.inl rfl

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
      | exact Or.inr (Or.inl rfl)

/-- **A statement tree whose elaborated code has no access or lifecycle instruction is frame-only.**
    The access form is the only source form with an access class; lifecycle instructions come from
    outside the source trees. -/
theorem stmt_rein (tree : Stmt result before after)
    (h : ∀ b ∈ (stmt tree).code, (∀ form, b ≠ .zugriff form) ∧ ∀ form, b ≠ .faden form) :
    (stmt tree).Rein := by
  intro b hb
  exact Befehl.privat_von_kein_zugriff (h b hb).1 (h b hb).2

theorem bracedBlock_rein (tree : BracedBlock result scope)
    (h : ∀ b ∈ (bracedBlock tree).code, (∀ form, b ≠ .zugriff form) ∧ ∀ form, b ≠ .faden form) :
    (bracedBlock tree).Rein := by
  intro b hb
  exact Befehl.privat_von_kein_zugriff (h b hb).1 (h b hb).2

private theorem functionCode_rein {result : Option WrittenType} {scope : Scope}
    (measure : Option (Measure scope)) (body : BracedBlock (writtenResult result) scope)
    (h : ∀ b ∈ (functionCode result measure body).code,
      (∀ form, b ≠ .zugriff form) ∧ ∀ form, b ≠ .faden form) :
    (functionCode result measure body).Rein := by
  intro b hb
  exact Befehl.privat_von_kein_zugriff (h b hb).1 (h b hb).2

private theorem decl_rein {before after : Scope} (d : Decl before after)
    (h : ∀ b ∈ (decl d).code, (∀ form, b ≠ .zugriff form) ∧ ∀ form, b ≠ .faden form) :
    (decl d).Rein := by
  intro b hb
  exact Befehl.privat_von_kein_zugriff (h b hb).1 (h b hb).2

private theorem unitBody_rein {before after : Scope} (body : UnitBody before after)
    (h : ∀ b ∈ (unitBody body).code, (∀ form, b ≠ .zugriff form) ∧ ∀ form, b ≠ .faden form) :
    (unitBody body).Rein := by
  intro b hb
  exact Befehl.privat_von_kein_zugriff (h b hb).1 (h b hb).2

theorem programm_rein (tree : Ast.Unit)
    (h : ∀ b ∈ (programm tree).code, (∀ form, b ≠ .zugriff form) ∧ ∀ form, b ≠ .faden form) :
    (programm tree).Rein := by
  intro b hb
  exact Befehl.privat_von_kein_zugriff (h b hb).1 (h b hb).2

/-- **Every elaborated fragment whose code has no access or lifecycle instruction is frame-only.** -/
theorem fragment_rein (category : Category) (tree : category.Tree)
    (h : ∀ b ∈ (fragment category tree).code,
      (∀ form, b ≠ .zugriff form) ∧ ∀ form, b ≠ .faden form) :
    (fragment category tree).Rein := by
  intro b hb
  exact Befehl.privat_von_kein_zugriff (h b hb).1 (h b hb).2

end Gabbro.Core.Ast.Semantik
