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

theorem expr_keine_invarianten (slot : Nat) (tree : Expr scope type) :
    (expr slot tree).klauseln.invariant = [] := by
  induction tree generalizing slot with
  | lit => rfl
  | binary op left right leftIH rightIH =>
    simp only [expr, Fragment.anhaengen, Quellklauseln.anhaengen, leftIH, rightIH,
      Fragment.einzel, Quellklauseln.leer, List.nil_append]

theorem stmt_keine_invarianten (tree : Stmt before after) :
    (stmt tree).klauseln.invariant = [] := by
  cases tree with
  | letValue _ _ init =>
    simp only [stmt, Fragment.anhaengen, Quellklauseln.anhaengen, expr_keine_invarianten,
      Fragment.einzel, Quellklauseln.leer, List.nil_append]

end Gabbro.Core.Ast.Semantik
