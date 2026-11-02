module
public import Stage0.Frontend.Aliases
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Only atom aliases introduce type-name dependencies. Explicit ranges retain the canonical
    bound semantics; their scalar dependencies are checked separately, in original source order. -/
def aliasEdges (items : List SItemTief) : List (String × String) :=
  items.filterMap fun
    | .typeT _ name [] _ (some (.atom target)) => some (name, target)
    | _ => none

/-- A single source namespace for type declarations; reordering cannot change shadowing. -/
def aliasNames (items : List SItemTief) : List String :=
  items.filterMap fun | .typeT _ name _ _ _ => some name | _ => none

/-- A rank certificate rules out every nonempty alias dependency cycle, including unused ones. -/
def AliasAcyclic (items : List SItemTief) : Prop :=
  ∃ rank : String → Nat, ∀ edge ∈ aliasEdges items, rank edge.2 < rank edge.1

theorem AliasAcyclic.no_cycle {items : List SItemTief} (h : AliasAcyclic items) (name : String) :
    ¬ Relation.TransGen (fun a b => (a, b) ∈ aliasEdges items) name name := by
  obtain ⟨rank, hr⟩ := h
  intro cycle
  have decreases {a b : String}
      (path : Relation.TransGen (fun a b => (a, b) ∈ aliasEdges items) a b) : rank b < rank a := by
    induction path with
    | single edge => exact hr _ edge
    | tail _ edge ih => exact Nat.lt_trans (hr _ edge) ih
  exact Nat.lt_irrefl _ (decreases cycle)

/-- Source lookup is explicit. A repeated active name diagnoses a cycle; unknown names remain
    leaves and must still pass canonical alias elaboration before any scope can be accepted. -/
def aliasDepth (items : List SItemTief) : Nat → List String → String → Except String Nat
  | 0, _, _ => .error "compile-time alias dependency depth exhausted"
  | fuel + 1, active, name =>
    if name ∈ active then .error ("compile-time alias dependency cycle at " ++ name)
    else match (aliasEdges items).find? (fun edge => edge.1 == name) with
    | none => .ok 0
    | some edge => (aliasDepth items fuel (name :: active) edge.2).map (· + 1)

/-- Reordering changes only the alias collection schedule. Runtime declarations, scalar folds
    and function origins continue to use the untouched original list. The permutation prevents
    dropped or invented declarations; the rank check is independent of the search algorithm. -/
structure AliasOrder (items : List SItemTief) where
  ordered : List SItemTief
  permutation : ordered.Perm items
  acyclic : AliasAcyclic items
  unique : (aliasNames items).Nodup

/-- Structural insertion carries its permutation proof and remains kernel-computable for
    whole-source witnesses. This avoids a new Mathlib sorting import. -/
def insertAliasRank (priority : SItemTief → Nat) (item : SItemTief) :
    (items : List SItemTief) → { ordered : List SItemTief // ordered.Perm (item :: items) }
  | [] => ⟨[item], .refl _⟩
  | head :: tail =>
    if priority item ≤ priority head then ⟨item :: head :: tail, .refl _⟩
    else
      let rest := insertAliasRank priority item tail
      ⟨head :: rest.val, (rest.property.cons head).trans (.swap _ _ _)⟩

/-- Stable rank ordering preserves every original declaration, with no equality instance on
    source syntax and no fuel limit that could silently drop an item. -/
def aliasRankOrder (priority : SItemTief → Nat) :
    (items : List SItemTief) → { ordered : List SItemTief // ordered.Perm items }
  | [] => ⟨[], .refl _⟩
  | item :: rest =>
    let tail := aliasRankOrder priority rest
    let inserted := insertAliasRank priority item tail.val
    ⟨inserted.val, inserted.property.trans (tail.property.cons item)⟩

/-- Build candidate depths, then independently check strict descent on EVERY source edge.
    Sorting uses those checked ranks. Duplicate alias names refuse rather than change shadowing. -/
def orderAliases (items : List SItemTief) : Except String (AliasOrder items) :=
  if hn : (aliasNames items).Nodup then do
    let depths ← (aliasNames items).mapM fun name => do
      let depth ← aliasDepth items (items.length + 2) [] name
      pure (name, depth)
    let rank := fun name => ((depths.find? (fun entry => entry.1 == name)).map (·.2)).getD 0
    if h : (aliasEdges items).all (fun edge => rank edge.2 < rank edge.1) then
      let priority := fun item => match item with
        | .typeT _ name _ _ _ => rank name
        | _ => 0
      let ordered := aliasRankOrder priority items
      pure ⟨ordered.val, ordered.property, ⟨rank, by
          intro edge hm
          exact of_decide_eq_true (List.all_eq_true.mp h edge hm)⟩, hn⟩
    else throw "compile-time alias dependency ranks are inconsistent"
  else .error "compile-time alias dependency ordering requires unique type names"

/-- The independently checked ranks exclude cycles for every accepted schedule. -/
theorem orderAliases_acyclic (items : List SItemTief) (order : AliasOrder items) : AliasAcyclic items :=
  order.acyclic

/-- A nondegenerate forward chain has a complete original-declaration permutation and no cycle. -/
theorem orderAliases_zeuge :
    let items := [SItemTief.typeT [] "Result" [] [] (some (.atom "Count")),
      .typeT [] "Count" [] [] (some (.atom "Byte")),
      .typeT [] "Byte" [] [] (some (.atom "u8"))]
    ∃ order : AliasOrder items, orderAliases items = .ok order ∧
      order.ordered.filterMap (fun | .typeT _ name _ _ _ => some name | _ => none) =
        ["Byte", "Count", "Result"] ∧ AliasAcyclic items := by
  dsimp only
  refine ⟨(orderAliases _).toOption.get (by decide +kernel), ?_, ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  · decide +kernel
  · exact orderAliases_acyclic _ ((orderAliases _).toOption.get (by decide +kernel))

/-- Cycles are refused before even unused aliases can disappear from canonical collection. -/
theorem orderAliases_cycle_zeuge :
    orderAliases [SItemTief.typeT [] "A" [] [] (some (.atom "B")),
      .typeT [] "B" [] [] (some (.atom "A"))] =
      .error "compile-time alias dependency cycle at A" := by rfl

/-- The generic no-cycle theorem is inhabited by a nonempty, two-edge alias chain. -/
theorem AliasAcyclic.no_cycle_zeuge :
    ¬ Relation.TransGen (fun a b => (a, b) ∈ aliasEdges
      [SItemTief.typeT [] "A" [] [] (some (.atom "B")),
       .typeT [] "B" [] [] (some (.atom "u8"))]) "A" "A" :=
  (orderAliases_acyclic _ ((orderAliases _).toOption.get (by decide +kernel))).no_cycle "A"

end Gabbro.Stage0.Frontend
