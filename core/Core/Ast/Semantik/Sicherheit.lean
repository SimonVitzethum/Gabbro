module

public import Core.Ast.Semantik.Pflichten
public import Core.Sicherheit.Regel

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Sicherheit Katalog

def Fragment.sicherheitsEinheit (p : Fragment) (platform : Plattform) :
    Sicherheit.Einheit PUnit PUnit Int PUnit Rahmen PUnit PUnit PUnit Befehl :=
  ⟨p.einheit platform, p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩)⟩

theorem Befehl.sicher (p : Fragment) (platform : Plattform)
    (keine : p.klauseln.invariant = []) (b : Befehl) :
    RegelSicher (p.sicherheitsEinheit platform) b := by
  intro H ρ t c w vor zwischen nach stepPlan spur head impl execute
  obtain ⟨rfl, rfl⟩ := b.vollzug_genau (w := w) impl execute
  have ohneAbsturz : ¬ Absturz (⟨[], []⟩ : SchrittSpur PUnit Int) := List.not_mem_nil
  have wirkungen :
      NeueWirkungen vor (b.nach c vor) (⟨[], []⟩ : SchrittSpur PUnit Int) [] :=
    Or.inr ⟨ohneAbsturz, (List.append_nil _).symm⟩
  refine ⟨⟨?_, [], wirkungen, ?_⟩, ?_, ?_, fun ordered => ordered, ?_, ?_⟩
  · intro i actor access recorded _
    cases recorded
  · refine ⟨List.nodup_nil, fun _ _ mem => (List.not_mem_nil mem).elim, ?_⟩
    intro _ obj alive lost
    exact nomatch alive.symm.trans lost
  · intro _
    refine ⟨fun _ _ => trivial, ?_⟩
    intro i d declared _
    change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at declared
    rw [keine] at declared
    cases declared
  · intro _ l changeOwner
    exact (changeOwner rfl).elim
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩

-- Extend the original expr_keine_invarianten with Fragment.anhaengen for each operator.
theorem expr_keine_invarianten (slot : Nat) (tree : Expr scope type) :
    (expr slot tree).klauseln.invariant = [] := by
  induction tree generalizing slot with
  | lit => rfl
  | binary op left right leftIH rightIH =>
      simp only [expr, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
        Quellklauseln.leer, List.nil_append, leftIH, rightIH]
  | trueLit => rfl
  | falseLit => rfl
  | variable => rfl
  | negativeLit => rfl
  | neg operand operandIH =>
      simp only [expr, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
        Quellklauseln.leer, List.nil_append, operandIH]
  | not operand operandIH =>
      simp only [expr, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
        Quellklauseln.leer, List.nil_append, operandIH]
  | div left right nonzero leftIH rightIH =>
      simp only [expr, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
        Quellklauseln.leer, List.nil_append, leftIH, rightIH]
  | compare op left right leftIH rightIH =>
      simp only [expr, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
        Quellklauseln.leer, List.nil_append, leftIH, rightIH]
  | logic op left right leftIH rightIH =>
      simp only [expr, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
        Quellklauseln.leer, List.nil_append, leftIH, rightIH]

-- Extend the original stmt_keine_invarianten by mutual recursion over Stmt and Block.
theorem stmt_keine_invarianten (tree : Stmt result before after) :
    (stmt tree).klauseln.invariant = [] := by
  induction tree with
  | letValue name ordinary value =>
      simp only [stmt, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
        Quellklauseln.leer, List.nil_append, expr_keine_invarianten]
  | assignVar ref visible writable value fits =>
      simp only [stmt, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
        Quellklauseln.leer, List.nil_append, expr_keine_invarianten]
  | ret declared value fits =>
      simp only [stmt, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
        Quellklauseln.leer, List.nil_append, expr_keine_invarianten]
  | ite condition yes no =>
      have blockEmpty : ∀ {r b a} (body : Block r b a), (block body).klauseln.invariant = [] := by
        intro r b a body
        induction body with
        | done => rfl
        | step first rest restIH =>
            simp only [block, Fragment.anhaengen, Quellklauseln.anhaengen,
              stmt_keine_invarianten first, restIH, List.nil_append]
      cases yes with
      | braces yesBody =>
      cases no with
      | braces noBody =>
      simp only [stmt, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
        Quellklauseln.leer, List.nil_append, expr_keine_invarianten, bracedBlock,
        blockEmpty]

end Gabbro.Core.Ast.Semantik
