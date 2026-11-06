module
public import Grammatik.Parser.Elab.Konst.Scopes.ConstantOrder
public import Stage0.Frontend.AliasOrder
public import Stage0.Frontend.Guard
public import Grammatik.Parser.Elab.Uebersetze.Tagged.Schema
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

/-- Both a forward scalar edge and a range-bound edge inhabit the generic cycle exclusion. -/
theorem ConstantAcyclic.no_cycle_zeuge :
    let items := [SItemTief.constT "ANSWER" (.atom "Bound") (.one (.variable "LIMIT")),
      .typeT [] "Bound" [] [] (some (.range (.atom "u8") (.lit 0) (.variable "LIMIT") false)),
      .constT "LIMIT" (.atom "u8") (.one (.lit 42))]
    ∃ order : ConstantOrder items, orderConstants items = .ok order ∧
      ¬ Relation.TransGen (fun a b => (a, b) ∈ constantEdges items) (.value "ANSWER") (.value "ANSWER") := by
  dsimp only
  refine ⟨(orderConstants _).toOption.get (by decide +kernel), ?_, ?_⟩
  · exact Gabbro.Grammatik.except_ok_get _
  · exact ((orderConstants _).toOption.get (by decide +kernel)).acyclic.no_cycle _

/-- Unused cycles cannot be hidden behind a candidate fixed point. -/
theorem orderConstants_cycle_zeuge :
    orderConstants [SItemTief.constT "A" (.atom "u8") (.one (.variable "B")),
      .constT "B" (.atom "u8") (.one (.variable "A"))] =
      .error "compile-time dependency cycle at constant A" := by rfl

/-- Removing a constructor head retains nested function and original value edges. -/
theorem option_dependencies_zeuge :
    valueReferences (.call "Some" [.call "work" [.variable "LIMIT"]]) =
      [.function "work", .value "LIMIT"] ∧
    valueReferences (.call "None" []) = [] ∧
    valueReferences (.call "Some" [.lit 1]) (fun name => strEq name "Some") =
      [.function "Some"] := ⟨rfl, rfl, rfl⟩

/-- A malformed constructor or an unknown head is never silently removed. -/
theorem option_wrong_arity_zeuge :
    valueReferences (.call "Some" []) = [.function "Some"] ∧
    valueReferences (.call "Some" [.lit 1, .lit 2]) = [.function "Some"] ∧
    valueReferences (.call "None" [.lit 1]) = [.function "None"] ∧
    valueReferences (.call "unknown" []) = [.function "unknown"] := ⟨rfl, rfl, rfl, rfl⟩

/-- Constructor operands cannot hide an unresolved call or an unused user cycle. -/
theorem option_nested_unresolved_zeuge :
    orderConstants [.constT "K" (.atom "u8") (.one (.call "Some" [.call "missing" []]))] =
      .error "unresolved compile-time dependency: const function missing" := by rfl

theorem option_nested_cycle_zeuge :
    let fn := SItemTief.fnT ⟨"const", "loop", [], some (.atom "u8"), none, [], []⟩
      (.block [] (some (.ret (some (.call "Some" [.call "loop" []])))))
    orderConstants [fn] = .error "compile-time dependency cycle at const function loop" := by rfl

theorem option_declared_cycle_zeuge :
    let fn := SItemTief.fnT ⟨"const", "Some", [("x", .atom "u8")], some (.atom "u8"), none, [], []⟩
      (.block [] (some (.ret (some (.call "Some" [.variable "x"])))))
    orderConstants [fn] = .error "compile-time dependency cycle at const function Some" := by rfl

/-- The schema controls arity; nested calls and variable operands remain intact. -/
theorem tagged_dependencies_zeuge :
    let schema : USum STyp := ⟨"Choice", [("Empty", none), ("Data", some (.atom "u8"))]⟩
    let owner := taggedConstructorOwner [schema]
    valueReferences (.call "Data" [.call "work" [.variable "LIMIT"]]) (fun _ => false) owner =
      [.type "Choice", .function "work", .value "LIMIT"] ∧
    valueReferences (.variable "Empty") (fun _ => false) owner = [.type "Choice"] ∧
    valueReferences (.call "Data" []) (fun _ => false) owner = [.function "Data"] ∧
    valueReferences (.call "Empty" [.lit 1]) (fun _ => false) owner = [.function "Empty"] ∧
    valueReferences (.call "Data" [.lit 1]) (fun name => strEq name "Data") owner =
      [.function "Data"] := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem tagged_ambiguous_owner_zeuge :
    taggedConstructorOwner
      [⟨"First", [("Data", some (.atom "u8"))]⟩,
       ⟨"Second", [("Data", some (.atom "u8"))]⟩] "Data" true = none := rfl

end Gabbro.Stage0.Frontend
