module

public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Elab.Konst.Scopes.ConstantScopes
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

namespace Gabbro.Grammatik.Parser.UebersetzeAllg.WidthSources
open Gabbro.Grammatik.Parser.Uebersetze

/-- Every string compares equal to itself. -/
theorem strEq_self (a : String) : strEq a a = true := by
  unfold strEq
  exact beq_self_eq_true a.toList

/-- The compiler's signature metadata is exactly the written declaration width at each position. -/
theorem parameter_declaration (alias : List (String × (Int × Int))) (parameters : List (String × STyp))
    (position : Nat) (name : String) (ty : STyp)
    (declared : parameters[position]? = some (name, ty))
    (widths : List (String × (Int × Int)) := []) :
    (uParameterBreiten alias parameters widths)[position]? = some (uWordBindingBreite alias ty widths) := by
  simp only [uParameterBreiten, List.getElem?_map, declared, Option.map_some]

/-- Binding metadata uses declarations only on the compiler path; canonical read-back stays unchanged. -/
theorem binding_declaration (ctx : UCtx) (ty : STyp) :
    uBindingBreite {ctx with narrow := true} ty = uWordBindingBreite ctx.alias ty ctx.widths ∧
    uBindingBreite {ctx with narrow := false} ty = uParamBreite ty := ⟨rfl, rfl⟩

/-- The width the builtin reader sees for a parameter or typed local is its stored declaration width. -/
theorem local_width (ctx : UCtx) (name : String) (position width : Nat)
    (resolved : uParamNr ctx name = .ok position) (declared : ctx.bits[position]? = some width)
    (positive : 0 < width) : uBreite ctx (.variable name) = some width := by
  simp only [uBreite, resolved, declared, positive, ↓reduceIte]

/-- A typed local puts the selected declaration width at the head of the actual binding context. -/
theorem typed_binding_width (ctx : UCtx) (name : String) (ty : STyp) (lo hi : Int)
    (range : uErgBereich ctx.alias ty = .ok (lo, hi)) :
    uBindKopf ctx name (some ty) = .ok (some (lo, hi),
      { ctx with
        names := name :: ctx.names
        kinds := .int :: ctx.kinds
        types := .int lo hi :: ctx.types
        bits := uBindingBreite ctx ty :: ctx.bits }) := by
  simp only [uBindKopf, range]

/-- Typed call results expose the same declaration metadata as ordinary typed bindings. -/
theorem call_binding_width (before after : UCtx) (ty : STyp) (enabled : before.narrow = true) :
    (uAnnotatedBinding before (some ty) after).bits = uBindingBreite before ty :: before.bits := by
  simp only [uAnnotatedBinding, enabled, ↓reduceIte]

/-- Pointer field access selects the pointed-to table's declaration, without inspecting the index. -/
theorem pointer_field_width (ctx : UCtx) (name field : String) (index : SExpr)
    (position number : Nat) (cap : DataCapTy)
    (resolved : uParamNr ctx name = .ok position)
    (kind : uArtBei ctx.kinds position = .ok (.ptr cap))
    (target : cap.target = .table number) :
    uBreite ctx (.field (.index (.field (.variable name) "slots") index) field) =
      (ctx.tabs[number]?).bind (fun table => uFeldBreite table field) := by
  cases cap with
  | mk space rights targetKind =>
    cases target
    simp only [uBreite, strEq_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, resolved, kind]

/-- Statics retain UGlob's declared width; a shadowing local is resolved before this case. -/
theorem static_width (ctx : UCtx) (name error : String) (global : UGlob)
    (absent : uParamNr ctx name = .error error)
    (declared : ctx.globs.find? (fun entry => strEq entry.name name) = some global)
    (positive : 0 < global.breite) : uBreite ctx (.variable name) = some global.breite := by
  simp only [uBreite, absent, declared, positive, ↓reduceIte]

/-- A table field keeps the width stored by uFeldBreiten, regardless of the access index. -/
theorem table_field_width (ctx : UCtx) (name field error : String) (index : SExpr) (table : UTab)
    (absent : uParamNr ctx name = .error error)
    (declared : ctx.tabs.find? (fun entry => strEq entry.name name) = some table) :
    uBreite ctx (.field (.index (.field (.variable name) "slots") index) field) = uFeldBreite table field := by
  simp only [uBreite, strEq_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, absent, declared,
    Option.bind_some]

/-- Arena element storage uses the arena's declared value-column width. -/
theorem arena_width (ctx : UCtx) (name : String) (index : SExpr) (table : UTab)
    (declared : ctx.tabs.find? (fun entry => strEq entry.name name) = some table)
    (arena : table.arena = true) :
    uBreite ctx (.index (.variable name) index) = uFeldBreite table "wert" := by
  simp only [uBreite, declared, arena, ↓reduceIte]

/-- Nominal fields retain source storage metadata in addition to their canonical value type. -/
theorem record_field_width (ctx : UCtx) (name field : String) (ty : Ty) (schema : URecord)
    (base : uStorageValueType ctx (.variable name) = some ty)
    (declared : ctx.records.find? (fun entry => decide (entry.ty = ty)) = some schema) :
    uBreite ctx (.field (.variable name) field) =
      (schema.breiten.find? (fun entry => strEq entry.1 field)).map (·.2) := by
  simp only [uBreite, uRecordBreite, base, declared, bind, Option.bind_some]

/-- Conversions and aliases read the source storage resolver, never an inferred integer interval. -/
theorem conversion_width (ctx : UCtx) (name : String) (value : SExpr) (width : Nat)
    (declared : uSpeicherBreite ctx.widths (.atom name) = width + 1) :
    uBreite ctx (.call name [value]) = some (width + 1) := by
  simp only [uBreite, declared]

/-- Alias entries transport their declared width exactly. -/
theorem alias_width (alias : List (String × (Int × Int))) (name : String) (width : Nat)
    (notBuiltin : uAtomBreite name = 0)
    (declared : uSuch "type" alias (name ++ "#bits") = .ok ((width : Int), (width : Int))) :
    uSpeicherBreite alias (.atom name) = width := by
  simp only [uSpeicherBreite, notBuiltin, Nat.lt_irrefl, ↓reduceIte, declared, Int.toNat_natCast]

/-- A complete word alias preserves its declared width at the parameter/local producer. -/
theorem word_alias_binding_width (alias widths : List (String × (Int × Int))) (name : String) (width : Nat)
    (notBuiltin : uAtomBreite name = 0)
    (declared : uSpeicherBreite widths (.atom name) = width)
    (range : uTypName alias name = .ok (0, (2 : Int) ^ width - 1)) :
    uWordBindingBreite alias (.atom name) widths = width := by
  simp only [uWordBindingBreite, declared, notBuiltin, Nat.lt_irrefl, ↓reduceIte, range] <;> rfl

/-- A non-word range alias never supplies a parameter/local builtin width. -/
theorem range_alias_binding_refused (alias widths : List (String × (Int × Int))) (name : String)
    (lo hi : Int) (width : Nat) (notBuiltin : uAtomBreite name = 0)
    (declared : uSpeicherBreite widths (.atom name) = width)
    (range : uTypName alias name = .ok (lo, hi))
    (notWord : ¬ (lo = 0 ∧ hi = (2 : Int) ^ width - 1)) :
    uWordBindingBreite alias (.atom name) widths = 0 := by
  simp only [uWordBindingBreite, declared, notBuiltin, Nat.lt_irrefl, ↓reduceIte, range, notWord]

/-- Each source alias edge preserves the storage base, even if its range was narrowed. -/
theorem alias_chain_width (items : List SItemTief) (fuel : Nat) (name target : String)
    (flags : List String) (args : List STyp) (order : List String) (body : STyp)
    (notBuiltin : uAtomBreite name = 0)
    (declared : items.find? (uTypeDeclNamed name) = some (.typeT flags name args order (some body)))
    (base : uStorageName body = some target) :
    uAliasWordWidth items (fuel + 1) name = uAliasWordWidth items fuel target := by
  rw [uAliasWordWidth, notBuiltin]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [declared]
  simp only [base]

/-- A resolved original declaration really contributes its metadata to the collector. -/
theorem alias_source_collected (items : List SItemTief) (name target : String)
    (flags : List String) (args : List STyp) (order : List String) (body : STyp) (width : Nat)
    (member : SItemTief.typeT flags name args order (some body) ∈ items)
    (base : uStorageName body = some target)
    (resolved : uAliasWordWidth items (items.length + 1) target = width)
    (positive : 0 < width) :
    (name ++ "#bits", ((width : Int), (width : Int))) ∈ uAliasBreiten items := by
  apply List.mem_filterMap.mpr
  refine ⟨_, member, ?_⟩
  simp only [base, resolved, Int.natCast_pos, positive, ↓reduceIte]

/-- Stage 0 passes original-source storage metadata along with the certified alias ranges. -/
theorem source_scope_widths {items : List SItemTief} (scope : Gabbro.Stage0.Frontend.Scopes items) :
    scope.types = scope.declared ++
      scope.values.map (fun entry => (entry.1, (entry.2, entry.2))) ∧
    scope.widths = uAliasBreiten scope.aliasOrder := ⟨rfl, rfl⟩

/-- Range classification keeps the exact original first-match scope, for every surface type. -/
theorem source_range_lookup {items : List SItemTief}
    (scope : Gabbro.Stage0.Frontend.Scopes items) (ty : STyp) :
    uFeldTyp scope.types ty = uFeldTyp
      (scope.declared ++ scope.values.map (fun entry => (entry.1, (entry.2, entry.2)))) ty := rfl

/-- Alias parameters use the same position-based signature producer as builtin types. -/
theorem alias_parameter_width (alias widths : List (String × (Int × Int)))
    (parameters : List (String × STyp)) (position width : Nat) (name aliasName : String)
    (parameter : parameters[position]? = some (name, .atom aliasName))
    (notBuiltin : uAtomBreite aliasName = 0)
    (declared : uSpeicherBreite widths (.atom aliasName) = width)
    (range : uTypName alias aliasName = .ok (0, (2 : Int) ^ width - 1)) :
    (uParameterBreiten alias parameters widths)[position]? = some width := by
  rw [parameter_declaration alias parameters position name (.atom aliasName) parameter widths,
    word_alias_binding_width alias widths aliasName width notBuiltin declared range]

/-- Alias locals, including annotated call results, retain the complete-word restriction. -/
theorem alias_binding_width (ctx : UCtx) (name : String) (width : Nat)
    (enabled : ctx.narrow = true) (notBuiltin : uAtomBreite name = 0)
    (declared : uSpeicherBreite ctx.widths (.atom name) = width)
    (range : uTypName ctx.alias name = .ok (0, (2 : Int) ^ width - 1)) :
    uBindingBreite ctx (.atom name) = width := by
  simp only [uBindingBreite, enabled, ↓reduceIte]
  exact word_alias_binding_width ctx.alias ctx.widths name width notBuiltin declared range

/-- Tables and records share the same alias-aware field metadata producer. -/
theorem alias_field_width (alias : List (String × (Int × Int))) (field : SFeld)
    (rest : List SFeld) (name : String) (width : Nat)
    (ty : field.ftyp = .atom name) (declared : uSpeicherBreite alias (.atom name) = width)
    (positive : 0 < width) :
    uFeldBreiten alias (field :: rest) = (field.fname, width) :: uFeldBreiten alias rest := by
  simp only [uFeldBreiten, List.filterMap_cons, ty, declared, positive, ↓reduceIte]

end Gabbro.Grammatik.Parser.UebersetzeAllg.WidthSources
