module
public import Grammatik.Parser.Elab.Konst.Scopes.AliasOrder
public import Grammatik.Parser.Lex.TafelIndex
@[expose] public section

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser

/-- The alias graph is indexed once per ordering pass, rather than rebuilt and
    scanned over the entire source at every depth of every dependency search. -/
def aliasDepthIndexed (edges : Tafel.Index String (String × String) Prod.fst) :
    Nat → List String → String → Except String Nat
  | 0, _, _ => .error "compile-time alias dependency depth exhausted"
  | fuel + 1, active, name =>
    if name ∈ active then .error ("compile-time alias dependency cycle at " ++ name)
    else match edges.finde name with
    | none => .ok 0
    | some edge => (aliasDepthIndexed edges fuel (name :: active) edge.2).map (· + 1)

theorem aliasDepthIndexed_eq (items : List SItemTief)
    (edges : Tafel.Index String (String × String) Prod.fst)
    (faithful : edges.liste = aliasEdges items) (fuel : Nat) (active : List String) (name : String) :
    aliasDepthIndexed edges fuel active name = aliasDepth items fuel active name := by
  induction fuel generalizing active name with
  | zero => rfl
  | succ fuel ih =>
    have index_lookup_eq : edges.finde name =
        (aliasEdges items).find? (fun edge => edge.1 == name) := by
      rw [Tafel.Index.finde, faithful]
    rw [aliasDepthIndexed, aliasDepth]
    by_cases hmem : name ∈ active
    · rw [if_pos hmem, if_pos hmem]
    · rw [if_neg hmem, if_neg hmem, index_lookup_eq]
      cases hfind : (aliasEdges items).find? (fun edge => edge.1 == name) with
      | none => rfl
      | some edge =>
        exact congrArg (Except.map (· + 1)) (ih (name :: active) edge.2)

theorem aliasDepthIndexed_von_eq (items : List SItemTief) (fuel : Nat)
    (active : List String) (name : String) :
    aliasDepthIndexed (Tafel.Index.von Prod.fst (aliasEdges items)) fuel active name =
      aliasDepth items fuel active name :=
  aliasDepthIndexed_eq items _ rfl fuel active name

def orderAliasesFast (items : List SItemTief) : Except String (AliasOrder items) :=
  if hn : (aliasNames items).Nodup then do
    let edges := Tafel.Index.von (κ := String) (α := String × String) Prod.fst (aliasEdges items)
    let depths ← (aliasNames items).mapM fun name => do
      let depth ← aliasDepthIndexed edges (items.length + 2) [] name
      pure (name, depth)
    let ranks := Tafel.Index.von (fun entry : String × Nat => entry.1) depths
    let rank := fun (name : String) => ((ranks.finde name).map (·.2)).getD 0
    if h : (aliasEdges items).all (fun edge => rank edge.2 < rank edge.1) then
      let priority := fun (item : SItemTief) => match item with
        | .typeT _ name _ _ _ => rank name
        | _ => 0
      let ordered := aliasRankOrder priority items
      pure ⟨ordered.val, ordered.property, ⟨rank, by
          intro edge hm
          exact of_decide_eq_true (List.all_eq_true.mp h edge hm)⟩, hn⟩
    else throw "compile-time alias dependency ranks are inconsistent"
  else .error "compile-time alias dependency ordering requires unique type names"

/-- Ordering, proofs, cycle errors and all remaining diagnostics are identical. -/
@[csimp] theorem orderAliases_eq_fast : @orderAliases = @orderAliasesFast := by
  funext items
  unfold orderAliasesFast orderAliases
  simp only [aliasDepthIndexed_von_eq, Tafel.Index.finde] <;> rfl

end Gabbro.Stage0.Frontend
