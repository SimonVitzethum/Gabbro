module
public import Grammatik.Parser.Elab.Konst.Scopes.ConstantOrder
public import Grammatik.Parser.Lex.TafelIndex
@[expose] public section

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser

/-- Structural namespace keys cannot collide through separator spellings. -/
def DependencyName.key : DependencyName → Nat × String
  | .value name => (0, name)
  | .type name => (1, name)
  | .function name => (2, name)

theorem sameDependency_key (a b : DependencyName) :
    sameDependency a b = (a.key == b.key) := by
  cases a <;> cases b <;>
    simp only [sameDependency, DependencyName.key, strEq_eq_schnell, strEqSchnell,
      Bool.beq_eq_decide_eq, Prod.mk.injEq] <;> rfl

abbrev DependencyIndex := Tafel.Index (Nat × String)
  (DependencyName × List DependencyName) (fun entry => entry.1.key)

/-- The immutable graph is computed and indexed once. Active-path and completed
    lists keep their exact order, fuel behaviour and cycle diagnostics. -/
def constantDepthIndexed (declarations : DependencyIndex) : Nat → List DependencyName →
    List (DependencyName × Nat) → DependencyName →
    Except String (Nat × List (DependencyName × Nat))
  | 0, _, _, _ => .error "compile-time constant dependency depth exhausted"
  | fuel + 1, active, resolved, name =>
    if active.any (sameDependency name) then .error ("compile-time dependency cycle at " ++ name.label)
    else match resolved.find? (fun entry => sameDependency entry.1 name) with
    | some entry => .ok (entry.2, resolved)
    | none => match declarations.finde name.key with
      | none => match name with
        | .type _ => .ok (0, resolved)
        | _ => .error ("unresolved compile-time dependency: " ++ name.label)
      | some entry => do
        let (depth, next) ← entry.2.foldlM (fun (depth, known) dependency => do
          let (value, known) ← constantDepthIndexed declarations fuel (name :: active) known dependency
          pure (max depth value, known)) (0, resolved)
        let value := depth + 1
        pure (value, (name, value) :: next)

theorem constantDepthIndexed_eq (items : List SItemTief) (declarations : DependencyIndex)
    (faithful : declarations.liste = dependencyDeclarations items) (fuel : Nat)
    (active : List DependencyName) (resolved : List (DependencyName × Nat)) (name : DependencyName) :
    constantDepthIndexed declarations fuel active resolved name =
      constantDepth items fuel active resolved name := by
  induction fuel generalizing active resolved name with
  | zero => rfl
  | succ fuel ih =>
    have index_lookup_eq : declarations.finde name.key =
        (dependencyDeclarations items).find? (fun entry => sameDependency entry.1 name) := by
      simp only [Tafel.Index.finde, faithful, sameDependency_key]
    unfold constantDepthIndexed constantDepth
    by_cases hmem : active.any (sameDependency name) = true
    · rw [if_pos hmem, if_pos hmem]
    · rw [if_neg hmem, if_neg hmem]
      cases hresolved : resolved.find? (fun entry => sameDependency entry.1 name) with
      | some entry => simp only [hresolved]
      | none =>
        simp only [hresolved, index_lookup_eq]
        cases hfind : (dependencyDeclarations items).find?
            (fun entry => sameDependency entry.1 name) with
        | none => simp only [hfind] <;> cases name <;> rfl
        | some entry => simp only [hfind, ih]

theorem constantDepthIndexed_von_eq (items : List SItemTief) (fuel : Nat)
    (active : List DependencyName) (resolved : List (DependencyName × Nat)) (name : DependencyName) :
    constantDepthIndexed (Tafel.Index.von (fun entry : DependencyName × List DependencyName => entry.1.key) (dependencyDeclarations items))
      fuel active resolved name = constantDepth items fuel active resolved name :=
  constantDepthIndexed_eq items _ rfl fuel active resolved name

/-- Preserve the independently checked rank certificate and exact stable order. -/
def orderConstantsFast (items : List SItemTief) : Except String (ConstantOrder items) :=
  if hn : (constantNames items).Nodup then do
    let declarations := Tafel.Index.von (fun entry : DependencyName × List DependencyName => entry.1.key) (dependencyDeclarations items)
    let nodes := (dependencyDeclarations items).map (·.1)
    let depths ← nodes.foldlM (fun known name => do
      let (_, next) ← constantDepthIndexed declarations (nodes.length + 2) [] known name
      pure next) []
    let ranks := Tafel.Index.von (fun entry : DependencyName × Nat => entry.1.key) depths
    let rank := fun (name : DependencyName) => ((ranks.finde name.key).map (·.2)).getD 0
    if h : (constantEdges items).all (fun edge => rank edge.2 < rank edge.1) then
      let priority := fun (item : SItemTief) => match item with
        | .constT name _ _ => rank (.value name)
        | _ => 0
      let ordered := aliasRankOrder priority items
      pure ⟨ordered.val, ordered.property, ⟨rank, by
        intro edge hm
        exact of_decide_eq_true (List.all_eq_true.mp h edge hm)⟩, hn⟩
    else throw "compile-time constant dependency ranks are inconsistent"
  else .error "compile-time constant dependency ordering requires unique constant names"

@[csimp] theorem orderConstants_eq_fast : @orderConstants = @orderConstantsFast := by
  funext items
  unfold orderConstantsFast orderConstants
  simp only [constantDepthIndexed_von_eq, Tafel.Index.finde, sameDependency_key] <;> rfl

end Gabbro.Stage0.Frontend
