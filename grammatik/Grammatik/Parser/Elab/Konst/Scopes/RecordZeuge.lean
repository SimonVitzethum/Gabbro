module
public import Grammatik.Parser.Elab.Konst.Scopes.ConstantOrder
import Grammatik.Kern.Taktik.KernelRfl
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

def singleFieldDeclaration : List SItemTief :=
  [.typeT [] "Flag" [] [] (some (.raw "{ ok : u32 in 0 .. 1, }"))]

/-- Even the shortest ranged record reaches the canonical field/range reader. -/
theorem single_field_schema_zeuge :
    (expandRecord 2 singleFieldDeclaration [] "Flag").map
        (fun fields => fields.map (fun field => (field.fname, field.ftyp))) =
      .ok [("ok", .range (.atom "u32") (.lit 0) (.lit 1) false)] ∧
    (uRecordFields "{ ok : u32 in 0 .. 1, }").map
        (fun fields => fields.map (fun field => (field.fname, field.ftyp))) =
      .ok [("ok", .range (.atom "u32") (.lit 0) (.lit 1) false)] :=
  ⟨by kernel_rfl, by kernel_rfl⟩

/-- Successful expansion depends on the field's scalar type, never on the record itself. -/
theorem single_field_dependency_zeuge :
    (dependencyDeclarations singleFieldDeclaration).map
        (fun entry => (entry.1.label, entry.2.map DependencyName.label)) =
      [("type Flag", ["type u32"])] ∧
    (constantDepth singleFieldDeclaration 3 [] [] (.type "Flag")).map (·.1) = .ok 1 :=
  ⟨by kernel_rfl, by kernel_rfl⟩

end Gabbro.Stage0.Frontend
