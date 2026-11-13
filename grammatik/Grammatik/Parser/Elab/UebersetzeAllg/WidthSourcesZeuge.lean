module

public import Grammatik.Parser.Elab.UebersetzeAllg.WidthSources
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

/- Width witnesses are outside the compiler import path. Reduce concrete lookup premises,
   then use the width laws rather than evaluating the complete context in the kernel. -/

/-- Concrete lookup proofs can use literal equality without decoding character lists. -/
theorem strEq_decide (a b : String) : strEq a b = decide (a = b) :=
  congrFun (congrFun strEq_eq_schnell a) b

attribute [local cbv_eval] strEq_decide

def aliasContext : UCtx :=
  { names := ["x"]
    kinds := [.int]
    types := [.int 0 4294967295]
    bits := [32]
    tabs := []
    locks := []
    held := []
    res := none
    fname := "sample"
    alias := [("Word", (0, 4294967295))]
    widths := [("Word#bits", (32, 32))]
    lits := []
    narrow := true }

private theorem word_storage : uSpeicherBreite aliasContext.widths (.atom "Word") = 32 := by
  apply alias_width _ _ 32 (by cbv)
  have bits : ("Word" ++ "#bits") = "Word#bits" := rfl
  simp only [aliasContext, uSuch, bits, strEq_self, ↓reduceIte]
  rfl

private theorem word_binding :
    uWordBindingBreite aliasContext.alias (.atom "Word") aliasContext.widths = 32 := by
  exact word_alias_binding_width _ _ _ 32 (by cbv) word_storage (by cbv)

theorem alias_parameter_zeuge :
    uParameterBreiten aliasContext.alias [("x", .atom "Word")] aliasContext.widths = [32] := by
  simp only [uParameterBreiten, List.map_cons, List.map_nil, word_binding]

theorem alias_local_zeuge :
    uBindingBreite aliasContext (.atom "Word") = 32 := by
  exact alias_binding_width _ _ 32 rfl (by cbv) word_storage (by cbv)

theorem range_alias_refused_zeuge :
    uBindingBreite {aliasContext with alias := [("Small", (0, 15))], widths := [("Small#bits", (32, 32))]}
      (.atom "Small") = 0 := by
  simp only [uBindingBreite, aliasContext, ↓reduceIte]
  apply range_alias_binding_refused _ _ _ 0 15 32 (by cbv)
  · apply alias_width _ _ 32 (by cbv)
    have bits : ("Small" ++ "#bits") = "Small#bits" := rfl
    simp only [uSuch, bits, strEq_self, ↓reduceIte]
    rfl
  · cbv
  · decide

/-- Reuse the local width law without evaluating any unrelated context fields. -/
theorem local_popcount (ctx : UCtx) (name error : String) (position width : Nat)
    (records : ctx.records = []) (integer : uTypName ctx.alias "popcount" = .error error)
    (resolved : uParamNr ctx name = .ok position) (kind : uArtBei ctx.kinds position = .ok .int)
    (declared : ctx.bits[position]? = some width) (positive : 0 < width) :
    uWertBody ctx (.call "popcount" [.variable name]) = .ok (.ib1 .popcount width (.param name)) := by
  have stored := local_width ctx name position width resolved declared positive
  have builtin : uBitEin "popcount" = some .popcount := by cbv
  simp only [uWertBody, uRechne, records, List.find?_nil, integer, builtin,
    uWertBlatt, resolved, kind, stored]

/-- Both rotation operands are read independently of the stored width. -/
theorem local_rotl (ctx : UCtx) (name : String) (position width : Nat)
    (records : ctx.records = []) (resolved : uParamNr ctx name = .ok position)
    (kind : uArtBei ctx.kinds position = .ok .int)
    (declared : ctx.bits[position]? = some width) (positive : 0 < width) :
    uWertBody ctx (.call "rotl" [.variable name, .lit 1]) =
      .ok (.ib2 .rotl width (.param name) (.lit 1)) := by
  have stored := local_width ctx name position width resolved declared positive
  have builtin : uRotEin "rotl" = some .rotl := by cbv
  simp only [uWertBody, uRechne, records, List.find?_nil, builtin,
    uWertBlatt, resolved, kind, stored]
  rfl

theorem alias_builtin_zeuge :
    uWertBody aliasContext (.call "popcount" [.variable "x"]) = .ok (.ib1 .popcount 32 (.param "x")) := by
  apply local_popcount _ _ "type unknown: popcount" 0 32 rfl (by cbv)
  · simp only [uParamNr, aliasContext, uParamNrAux, strEq_self, ↓reduceIte]
  · rfl
  · rfl
  · decide

def wordRecord : URecord :=
  { name := "R"
    identity := 0
    fields := [("value", .int 0 4294967295)]
    breiten := [("value", 32)] }

def storageContext : UCtx :=
  { aliasContext with
    names := ["record"]
    kinds := [.wert]
    types := [wordRecord.ty]
    bits := [0]
    records := [wordRecord]
    globs := [{ name := "G"
                ty := .int 0 4294967295
                init := 0
                breite := 32 }]
    tabs := [{ name := "T"
               count := 2
               cols := [("value", (0, 4294967295))]
               breiten := [("value", 32)] },
             { name := "A"
               count := 2
               arena := true
               cols := [("wert", (0, 4294967295))]
               breiten := [("wert", 32)] }] }

theorem declaration_sources_zeuge :
    uBreite storageContext (.field (.variable "record") "value") = some 32 ∧
    uBreite storageContext (.variable "G") = some 32 ∧
    uBreite storageContext (.field (.index (.field (.variable "T") "slots") (.lit 0)) "value") = some 32 ∧
    uBreite storageContext (.index (.variable "A") (.lit 0)) = some 32 ∧
    uBreite storageContext (.call "Word" [.lit 1]) = some 32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [record_field_width _ _ _ wordRecord.ty wordRecord]
    · simp only [wordRecord, List.find?_cons, strEq_self, Option.map_some]
    · simp only [uStorageValueType, uParamNr, storageContext, uParamNrAux, strEq_self,
        ↓reduceIte, List.getElem?_cons_zero]
    · change [wordRecord].find? (fun entry => decide (entry.ty = wordRecord.ty)) = some wordRecord
      cbv
  · let global : UGlob :=
      { name := "G"
        ty := .int 0 4294967295
        init := 0
        breite := 32 }
    exact static_width _ _ "name unknown: G" global
      (by change uParamNrAux ["record"] 0 "G" = _; cbv)
      (by simp only [storageContext]; cbv) (by decide)
  · let table : UTab :=
      { name := "T"
        count := 2
        cols := [("value", (0, 4294967295))]
        breiten := [("value", 32)] }
    rw [table_field_width _ _ _ "name unknown: T" _ table
      (by change uParamNrAux ["record"] 0 "T" = _; cbv)
      (by simp only [storageContext]; cbv)]
    simp only [uFeldBreite, table, List.find?_cons, strEq_self, Option.map_some]
  · let table : UTab :=
      { name := "A"
        count := 2
        arena := true
        cols := [("wert", (0, 4294967295))]
        breiten := [("wert", 32)] }
    rw [arena_width _ _ _ table (by simp only [storageContext]; cbv) rfl]
    simp only [uFeldBreite, table, List.find?_cons, strEq_self, Option.map_some]
  · exact conversion_width _ _ _ 31 word_storage

end Gabbro.Grammatik.Parser.UebersetzeAllg.WidthSources
