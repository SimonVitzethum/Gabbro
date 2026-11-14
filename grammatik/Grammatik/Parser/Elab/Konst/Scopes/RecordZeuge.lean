module
public import Grammatik.Parser.Elab.Konst.Scopes.ConstantOrder
import Lean.Elab.Tactic.Cbv
import all Grammatik.Parser.Expr.Ausdruck.Teil1
import all Grammatik.Parser.Expr.Ausdruck.Teil2a
import all Grammatik.Parser.Expr.Ausdruck.Teil3
import all Grammatik.Parser.Expr.Typ
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

attribute [local cbv_eval] strEq_apply_eq_decide

-- Evaluate only the actual parser nodes, without unfolding the mutual fuel tuple.
attribute [local cbv_opaque] parseTyp parseTypNach parseOr parseOrL parseAnd parseAndL
  parseCmp parseBit parseBitL parseAdd parseAddL parseMul parseMulL parseUnary
  parsePrimary parseKopf parseSuffixe
attribute [local cbv_eval] parseTyp.eq_def parseTypNach.eq_def parseOr.eq_def parseOrL.eq_def
  parseAnd.eq_def parseAndL.eq_def parseCmp.eq_def parseBit.eq_def parseBitL.eq_def
  parseAdd.eq_def parseAddL.eq_def parseMul.eq_def parseMulL.eq_def parseUnary.eq_def
  parsePrimary.eq_def parseKopf.eq_def parseSuffixe.eq_def

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
  ⟨by cbv, by cbv⟩

private theorem single_field_dependencies :
    dependencyDeclarations singleFieldDeclaration = [(.type "Flag", [.type "u32"])] := by
  cbv

/-- Successful expansion depends on the field's scalar type, never on the record itself. -/
theorem single_field_dependency_zeuge :
    (dependencyDeclarations singleFieldDeclaration).map
        (fun entry => (entry.1.label, entry.2.map DependencyName.label)) =
      [("type Flag", ["type u32"])] ∧
    (constantDepth singleFieldDeclaration 3 [] [] (.type "Flag")).map (·.1) = .ok 1 := by
  constructor
  · rw [single_field_dependencies]
    cbv
  · simp only [constantDepth, single_field_dependencies]
    cbv

end Gabbro.Stage0.Frontend
