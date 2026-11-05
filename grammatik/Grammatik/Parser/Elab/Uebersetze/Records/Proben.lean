module

public import Grammatik.Parser.Elab.UebersetzeAllg.RecordLaws
public import Grammatik.GabbroV.Start.GvStartPflichta
import all Grammatik.Parser.Elab.Uebersetze.Records.Records
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5

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

namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

attribute [local cbv_eval] lowWertE.eq_def lowWertAtE.eq_def lowProductArgs.eq_def

/-
  File:       Grammatik/Parser/Elab/Uebersetze/Records/Proben.lean
  Subject:    WITNESSES of the C01 record export: schema lookup, construction in and out of
              declaration order, projection, replacement and nested replacement through the real
              `lowWertE`, plus refusal twins. These witnesses start from elaborated sides;
              source parsing and declaration population are checked by their frontend witnesses.
-/

def recordFixture : URecord :=
  { name := "Pair", identity := 7, fields := [("small", .int 0 255), ("flag", .bool)] }

def recordFunction : UFn :=
  { name := "sample", params := [], kinds := [], res := none, held := [], puts := [], gives := [],
    body := [], ret := .empty }

def recordUnit : UProg := { tabs := [], locks := [], fns := [recordFunction], records := [recordFixture] }

def recordLiteral : USide :=
  .product 7 false [(.int 0 255, .lit 42), (.bool, .truth true)]

def recordLiteralUmgestellt : USide :=
  .product 7 true [(.bool, .truth true), (.int 0 255, .lit 42)]

private def recordArgs : Args (declOf recordUnit) [] [] [.int 0 255, .bool] :=
  .cons (Expr.widen (by decide) (by decide) (Expr.lit 42)) (.cons Expr.tru .nil)

private theorem record_schema_selected :
    uRecordOf recordUnit.records recordFixture.ty = .ok ⟨recordFixture, rfl⟩ := by
  cbv <;> rfl

private theorem record_named_fields_arranged :
    uRecordValues recordFixture [("flag", .truth true), ("small", .lit 42)] =
      .ok (.product 7 true [(.int 0 255, .lit 42), (.bool, .truth true)]) := by
  cbv <;> rfl

private theorem record_fields_lowered :
    lowProductArgs recordUnit [] [] recordFunction none
      [(.int 0 255, .lit 42), (.bool, .truth true)] = .ok recordArgs := by
  cbv <;> rfl

private theorem record_product_lowered (reordered : Bool) :
    lowWertE recordUnit [] [] recordFunction none
      (.product 7 reordered [(.int 0 255, .lit 42), (.bool, .truth true)]) =
      .ok ⟨recordFixture.ty, Expr.prod 7 recordArgs⟩ := by
  exact record_lower recordUnit [] [] recordFunction none 7 reordered _ recordArgs
    (by cbv) record_fields_lowered ⟨recordFixture, rfl⟩ record_schema_selected

private theorem record_swapped_types_refused :
    lowWertE recordUnit [] [] recordFunction none
      (.product 7 true [(.bool, .truth true), (.int 0 255, .lit 42)]) =
      .error "source export: unknown nominal record schema" := by
  cbv <;> rfl

private theorem record_constant_quoted (number : Int) :
    uConstantValue (.product 7 false [(.int 0 255, .lit number), (.bool, .truth true)]) =
      .ok (.product 7 [.zahl number, .wahr true]) := by
  cbv <;> rfl

/-- Nondegenerate nominal schema, construction (in and out of declaration order), projection,
    replacement and nested replacement, all through the real lowering. -/
theorem record_lower_zeuge :
    uRecordOf recordUnit.records recordFixture.ty = .ok ⟨recordFixture, rfl⟩ ∧
    (lowWertE recordUnit [] [] recordFunction none recordLiteral).toBool = true ∧
    (lowWertE recordUnit [] [] recordFunction none recordLiteralUmgestellt).toBool = true ∧
    (lowWertE recordUnit [] [] recordFunction none (.field recordLiteral "flag")).toBool = true ∧
    (lowWertE recordUnit [] [] recordFunction none (.replace recordLiteral "small" (.lit 9))).toBool = true := by
  cbv

/-- Empty and foreign nominal types are distinct even when their field shapes agree; unknown fields,
    duplicate constructors and missing fields are refused. -/
theorem record_schema_refused_zeuge :
    (uRecordPosition recordFixture.fields "missing").toBool = false ∧
    (uRecordOf [recordFixture] (.prodOf 8 [.int 0 255, .bool])).toBool = false ∧
    (uRecordValues recordFixture [("small", .lit 1), ("small", .lit 2)]).toBool = false ∧
    (uRecordValues recordFixture [("flag", .truth true)]).toBool = false ∧
    (lowWertE recordUnit [] [] recordFunction none (.field recordLiteral "missing")).toBool = false ∧
    (lowWertE recordUnit [] [] recordFunction none
      (.product 8 false [(.int 0 255, .lit 1), (.bool, .truth true)])).toBool = false := by
  decide +kernel

/-- Constants evaluate at the nominal product type, field by field; out-of-range fields and
    bare `null` have no product value. -/
theorem record_konst_zeuge :
    (GabbroV.konstWert (F := Unit) (P := fun _ _ => false) recordFixture.ty
      (.product 7 [.zahl 42, .wahr true])).isSome = true ∧
    (GabbroV.konstWert (F := Unit) (P := fun _ _ => false) recordFixture.ty .null).isSome = false ∧
    (GabbroV.konstWert (F := Unit) (P := fun _ _ => false) recordFixture.ty
      (.product 7 [.zahl 256, .wahr true])).isSome = false ∧
    (GabbroV.konstWert (F := Unit) (P := fun _ _ => false) recordFixture.ty
      (.product 8 [.zahl 42, .wahr true])).isSome = false := by
  decide +kernel

/-- Nested replacements retain the nominal schema through the actual expression lowerer. -/
theorem record_nested_replace_zeuge :
    (lowWertE recordUnit [] [] recordFunction none
      (.replace recordLiteral "small" (.field (.replace recordLiteral "small" (.lit 17)) "small"))).toBool = true := by
  decide +kernel

/-- Initializers validate every component at its declared nominal product type. -/
theorem record_initial_zeuge :
    (uConstantValue (.product 7 false [(.int 0 255, .lit 42), (.bool, .truth true)])).toBool = true ∧
    (uConstantValue (.product 7 false [(.int 0 255, .lit 256), (.bool, .truth true)])).toBool = false := by
  cbv

end Gabbro.Grammatik.Parser.Uebersetze
