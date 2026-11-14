module
public import Grammatik.Parser.Elab.Tuples.Frontend
@[expose] public section

namespace Gabbro.Grammatik.Parser.Tuples

/-- Select only the actual mutual equation, before instantiating the large frontend budget. -/
private theorem statements_nil (k : Context) (locals : Spec.Locals) (result : Option STyp)
    (fuel : Nat) :
    expandStatements k locals result fuel [] = match fuel with
      | 0 => lift (.error "tuple expansion: block fuel exhausted")
      | _ + 1 => pure ([], locals) := by
  cases fuel <;> simp only [expandStatements]

private theorem empty_block (k : Context) (locals : Spec.Locals) (result : Option STyp)
    (fuel : Nat) :
    expandStatement k locals result fuel (.block [] none) = match fuel with
      | 0 => lift (.error "tuple expansion: statement fuel exhausted")
      | fuel + 1 => do
        let (statements, _) ← expandStatements k locals result fuel []
        pure [.block statements none] := by
  cases fuel <;> simp only [expandStatement, Option.mapM_none, pure_bind]

/-- Empty signatures and bodies do not need type discovery. All other signature metadata is
    retained, including the error channel and generic parameters. -/
theorem expandItem_empty_function (k : Context) (sig : FnSig) (fuel : Nat)
    (params : sig.params = []) (result : sig.res = none) (clauses : sig.klauseln = []) :
    expandItem k fuel (.fnT sig (.block [] none)) = match fuel with
      | 0 => lift (.error "tuple expansion: item fuel exhausted")
      | _ + 1 => pure (.fnT sig (.block [] none)) := by
  cases sig with
  | mk art name ps res error ks generics =>
    dsimp only at params result clauses
    subst ps
    subst res
    subst ks
    cases fuel <;>
      simp only [expandItem, expandSignature, List.mapM_nil, Option.mapM_none,
        List.nil_append, empty_block, statements_nil, pure_bind]

/-- Check declarations belong to the check elaborator; tuple expansion retains them verbatim. -/
theorem expandItem_check (k : Context) (check : SCheck) (fuel : Nat) :
    expandItem k fuel (.checkT check) = match fuel with
      | 0 => lift (.error "tuple expansion: item fuel exhausted")
      | _ + 1 => pure (.checkT check) := by
  cases fuel <;> simp only [expandItem]

/-- A context-independent identity certificate avoids evaluating unused constants, aliases or
    source types. The actual pass still runs with its canonical context and initial state. -/
theorem expand_of_mapM_eq_pure (items : List SItemTief)
    (unchanged : ∀ k : Context,
      items.mapM (expandItem k 100000) = (pure items : ExpandM (List SItemTief))) :
    expand items = .ok (items, []) := by
  unfold expand
  rw [unchanged]
  rfl

end Gabbro.Grammatik.Parser.Tuples
