/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Rein.lean
  Subject:   A SOURCE FRAGMENT CONTAINS NO ACCESS INSTRUCTION (MK-04). The access instructions
             (`Befehl.zugriff`) are written by the access forms of the memory model; no source form of the
             present grammar elaborates to one. Every instruction an elaborated fragment contains is therefore
             frame-only (`Befehl.Privat`), and the statements about EVERY elaborated unit that rest on the template
             step of the frame-only classes (`I.Bestimmt`, `I.Fortschritt`, the flow rule) keep holding for the
             elaborated units, while a unit that does contain an access instruction owes the duties of its class
             (`KlassenAussagen`, `ZugriffBefehlAussage`). The statement is proved once by the recursion over the
             source tree, exactly as the elaboration of the clauses (`fragment_unit_invarianten`, `tabLeer`).
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

/-- A binding statement is frame-only. -/
theorem stmt_letValue_rein (name : Identifier) (ordinary : name.val ≠ "mut".toList) (value : Expr scope type) :
    (stmt (Stmt.letValue (result := result) name ordinary value)).Rein := by
  simp only [stmt, Fragment.rein_anhaengen_iff, Fragment.rein_einzel_iff, expr_rein, true_and]
  exact Or.inl rfl

end Gabbro.Core.Ast.Semantik
