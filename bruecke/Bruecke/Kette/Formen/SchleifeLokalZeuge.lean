module
public import Bruecke.Anweisung.Schleife.Simulation
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- A literal condition has no name lookup or captured context to evaluate. -/
theorem condZ_true (u : UProg) (fn : UFn) (ns : BodyNames) :
    condZ u fn ns .tru = some (.lit (.bool true)) := by
  simp [condZ, rawCond, ensExpr, renameScalar]

/-- Small source-reader witness for an actual scalar update in a traversal. Table and
    positional lookup are explicit small premises; the proof evaluates no whole unit. -/
theorem loop_local_reader_zeuge (u : UProg) (fn : UFn) (ns : BodyNames)
    (binder tab x id : String) (t : Fin u.tabs.length)
    (ht : tabIdx u.tabs tab = .ok t)
    (hx : (ns.push binder).lookup
      (fn.mitIndex binder t.val ((declOf u).count t)) x = some id) :
    stmtsBodyZ u 5 fn ns
      [.loopBeg binder tab .tru, .setVarB x .tru, .blkEnd] .empty =
        some [.forEach (ns.fresh binder) (loopIndices u t)
          [.bindName id (.lit (.bool true))]] := by
  simp only [stmtsBodyZ, loopWritesB, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ht, Except.toOption,
    seqZ, schrittB, hx, condZ_true, namedEnd, bind, pure, Option.bind, Option.map]

/-- The updated local is the output of the pass, rather than the old entry environment. -/
theorem forEach_local_true (ρB : Gabbro.Body.Env) (s : Gabbro.Body.State)
    (binder x : String) (i : Int) (indices : List Int) :
    ∃ t, Gabbro.Body.step ρB
      (.forEach binder (i :: indices) [.bindName x (.lit (.bool true))]) s = .running t ∧
      t.local' x = .bool true := by
  induction indices generalizing s i with
  | nil =>
      let t : Gabbro.Body.State :=
        ⟨s.world, Gabbro.Body.bindLocal
          (Gabbro.Body.bindLocal s.local' binder (.int i)) x (.bool true)⟩
      refine ⟨t, ?_, Gabbro.Body.bindLocal_here _ _ _⟩
      exact (Gabbro.Body.forEach_cons_running ρB binder i [] _ s t (by
        simp only [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, t])).trans
          (Gabbro.Body.forEach_nil ρB binder _ t)
  | cons j indices ih =>
      let t : Gabbro.Body.State :=
        ⟨s.world, Gabbro.Body.bindLocal
          (Gabbro.Body.bindLocal s.local' binder (.int i)) x (.bool true)⟩
      obtain ⟨last, hr, hv⟩ := ih t j
      refine ⟨last, ?_, hv⟩
      exact (Gabbro.Body.forEach_cons_running ρB binder i (j :: indices) _ s t (by
        simp only [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, t])).trans hr

/-- Source reading and nonempty operational local mutation hold together. The lookup
    premise admits arbitrary generated identifiers, including source-name shadowing. -/
theorem local_mutation_zeuge (u : UProg) (fn : UFn) (ns : BodyNames)
    (binder tab x id : String) (t : Fin u.tabs.length)
    (ht : tabIdx u.tabs tab = .ok t)
    (hx : (ns.push binder).lookup
      (fn.mitIndex binder t.val ((declOf u).count t)) x = some id)
    (i : Int) (indices : List Int) (hi : loopIndices u t = i :: indices)
    (ρB : Gabbro.Body.Env) (s : Gabbro.Body.State) :
    ∃ bs, stmtsBodyZ u 5 fn ns
      [.loopBeg binder tab .tru, .setVarB x .tru, .blkEnd] .empty = some bs ∧
      ∃ last, Gabbro.Body.exec ρB bs s = .running last ∧ last.local' id = .bool true := by
  refine ⟨_, loop_local_reader_zeuge u fn ns binder tab x id t ht hx, ?_⟩
  obtain ⟨last, hr, hv⟩ := forEach_local_true ρB s (ns.fresh binder) id i indices
  rw [← hi] at hr
  exact ⟨last, by simp only [Gabbro.Body.exec, hr], hv⟩

end Gabbro.Bruecke
