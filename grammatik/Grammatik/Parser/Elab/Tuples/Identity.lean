module
public import Grammatik.Parser.Elab.Tuples.Frontend
@[expose] public section

namespace Gabbro.Grammatik.Parser.Tuples

/-- Empty signatures and bodies do not need type discovery. All other signature metadata is
    retained, including the error channel and generic parameters. -/
theorem expandItem_empty_function (k : Context) (sig : FnSig)
    (params : sig.params = []) (result : sig.res = none) (clauses : sig.klauseln = []) :
    expandItem k 100000 (.fnT sig (.block [] none)) = pure (.fnT sig (.block [] none)) := by
  cases sig with
  | mk art name ps res error ks generics =>
    dsimp only at params result clauses
    subst ps
    subst res
    subst ks
    rfl

/-- Check declarations belong to the check elaborator; tuple expansion retains them verbatim. -/
theorem expandItem_check (k : Context) (check : SCheck) :
    expandItem k 100000 (.checkT check) = pure (.checkT check) := by
  rfl

/-- A context-independent identity certificate avoids evaluating unused constants, aliases or
    source types. The actual pass still runs with its canonical context and initial state. -/
theorem expand_of_mapM_eq_pure (items : List SItemTief)
    (unchanged : ∀ k : Context,
      items.mapM (expandItem k 100000) = (pure items : ExpandM (List SItemTief))) :
    expand items = .ok (items, []) := by
  unfold expand
  dsimp only
  rw [unchanged]
  rfl

end Gabbro.Grammatik.Parser.Tuples
