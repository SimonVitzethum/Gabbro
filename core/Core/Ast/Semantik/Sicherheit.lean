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
  | binary op left right leftIH rightIH =>
      simp only [expr, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
        Quellklauseln.leer, List.nil_append, leftIH, rightIH]
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
  | _ => rfl

-- Extend the original stmt_keine_invarianten by mutual recursion over Stmt and Block.
theorem stmt_keine_invarianten (tree : Stmt result before after) :
    (stmt tree).klauseln.invariant = [] := by
  refine @Stmt.rec result
    (fun b a t => (stmt t).klauseln.invariant = [])
    (fun b a t => (block t).klauseln.invariant = [])
    (fun b t => (bracedBlock t).klauseln.invariant = [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ before after tree
  · simp [stmt, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
      Quellklauseln.leer, expr_keine_invarianten]
  · simp [stmt, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
      Quellklauseln.leer, expr_keine_invarianten]
  · simp [stmt, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
      Quellklauseln.leer, expr_keine_invarianten]
  · intro scope condition yes no yesIH noIH
    simp [stmt, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
      Quellklauseln.leer, expr_keine_invarianten, yesIH, noIH]
  · simp [block]
  · intro before middle after first rest firstIH restIH
    simp [block, Fragment.anhaengen, Quellklauseln.anhaengen, firstIH, restIH]
  · intro before after body bodyIH
    simp [bracedBlock, Fragment.anhaengen, Fragment.einzel, Quellklauseln.anhaengen,
      Quellklauseln.leer, bodyIH]

end Gabbro.Core.Ast.Semantik
