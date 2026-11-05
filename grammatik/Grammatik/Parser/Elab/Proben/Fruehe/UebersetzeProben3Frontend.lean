module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3Lexical
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
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

namespace Gabbro.Grammatik.Parser.UebersetzeProben3

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

attribute [local cbv_opaque] lowStufe lowSeqL lowStructL
attribute [local cbv_eval] UebersetzeProben2.seq_select UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct

theorem entry1_ok_text : entry1_ok = String.ofList entry1_ok_characters := by cbv

theorem entry1_ok_parsed : (parseTopTief entry1_ok_tokens).toOption.isSome = true := by cbv
def entry1_ok_items : List SItemTief := (parseTopTief entry1_ok_tokens).toOption.get entry1_ok_parsed

theorem entry1_ok_elaborated : (elabU (pre108 entry1_ok_items)).toOption.isSome = true := by cbv
def entry1_ok_unit : Uebersetze.UProg := (elabU (pre108 entry1_ok_items)).toOption.get entry1_ok_elaborated

/-- The complete package is formed on the actual elaboration result before any caller index. -/
theorem entry1_ok_metadata : entry1_ok_unit.invs = [] ∧ contractGate entry1_ok_unit = true ∧
    (∀ f : Fin entry1_ok_unit.fns.length,
      (lowerFnAt entry1_ok_unit f).toOption.isSome = true ∧ (fnAt entry1_ok_unit f).decreases = none) ∧
    (entry1_ok_unit.roots, entry1_ok_unit.hands) = (["w"], []) := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 entry1_ok_items) = .ok unit ∧ unit.invs = [] ∧ contractGate unit = true ∧
      (∀ f : Fin unit.fns.length,
      (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none) ∧
      (unit.roots, unit.hands) = (["w"], []) := by
    refine ⟨?unit, ?elaborated, ?invariants, ?contracts, ?functions, ?observed⟩
    case elaborated => cbv <;> exact Eq.refl _
    case invariants => cbv
    case contracts => cbv
    case functions =>
      intro f
      rcases f with ⟨index, bound⟩
      have small : index < 2 := bound
      rcases (by omega : index = 0 ∨ index = 1) with rfl | rfl <;>
        constructor <;> cbv
    case observed => cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = entry1_ok_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 entry1_ok_items)) entry1_ok_elaborated))
  cases same
  exact facts

theorem entry1_ok_lowered : UebersetzeProben2.lowerStage entry1_ok_unit = "OK" :=
  UebersetzeProben2.lowerStage_ok entry1_ok_unit entry1_ok_metadata.1
    entry1_ok_metadata.2.2.1 entry1_ok_metadata.2.1

theorem entry_two_ok_text : entry_two_ok = String.ofList entry_two_ok_characters := by cbv

theorem entry_two_ok_parsed : (parseTopTief entry_two_ok_tokens).toOption.isSome = true := by cbv
def entry_two_ok_items : List SItemTief := (parseTopTief entry_two_ok_tokens).toOption.get entry_two_ok_parsed

theorem entry_two_ok_elaborated : (elabU (pre108 entry_two_ok_items)).toOption.isSome = true := by cbv
def entry_two_ok_unit : Uebersetze.UProg := (elabU (pre108 entry_two_ok_items)).toOption.get entry_two_ok_elaborated

/-- The complete package is formed on the actual elaboration result before any caller index. -/
theorem entry_two_ok_metadata : entry_two_ok_unit.invs = [] ∧ contractGate entry_two_ok_unit = true ∧
    ∀ f : Fin entry_two_ok_unit.fns.length,
      (lowerFnAt entry_two_ok_unit f).toOption.isSome = true ∧ (fnAt entry_two_ok_unit f).decreases = none := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 entry_two_ok_items) = .ok unit ∧ unit.invs = [] ∧ contractGate unit = true ∧
      ∀ f : Fin unit.fns.length,
      (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none := by
    refine ⟨?unit, ?elaborated, ?invariants, ?contracts, ?functions⟩
    case elaborated => cbv <;> exact Eq.refl _
    case invariants => cbv
    case contracts => cbv
    case functions =>
      intro f
      rcases f with ⟨index, bound⟩
      have small : index < 2 := bound
      rcases (by omega : index = 0 ∨ index = 1) with rfl | rfl <;>
        constructor <;> cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = entry_two_ok_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 entry_two_ok_items)) entry_two_ok_elaborated))
  cases same
  exact facts

theorem entry_two_ok_lowered : UebersetzeProben2.lowerStage entry_two_ok_unit = "OK" :=
  UebersetzeProben2.lowerStage_ok entry_two_ok_unit entry_two_ok_metadata.1
    entry_two_ok_metadata.2.2 entry_two_ok_metadata.2.1

theorem entry_via_ok_text : entry_via_ok = String.ofList entry_via_ok_characters := by cbv

theorem entry_via_ok_parsed : (parseTopTief entry_via_ok_tokens).toOption.isSome = true := by cbv
def entry_via_ok_items : List SItemTief := (parseTopTief entry_via_ok_tokens).toOption.get entry_via_ok_parsed

theorem entry_via_ok_elaborated : (elabU (pre108 entry_via_ok_items)).toOption.isSome = true := by cbv
def entry_via_ok_unit : Uebersetze.UProg := (elabU (pre108 entry_via_ok_items)).toOption.get entry_via_ok_elaborated

/-- The complete package is formed on the actual elaboration result before any caller index. -/
theorem entry_via_ok_metadata : entry_via_ok_unit.invs = [] ∧ contractGate entry_via_ok_unit = true ∧
    (∀ f : Fin entry_via_ok_unit.fns.length,
      (lowerFnAt entry_via_ok_unit f).toOption.isSome = true ∧ (fnAt entry_via_ok_unit f).decreases = none) ∧
    (entry_via_ok_unit.roots, entry_via_ok_unit.hands) = (["w"], ["w"]) := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 entry_via_ok_items) = .ok unit ∧ unit.invs = [] ∧ contractGate unit = true ∧
      (∀ f : Fin unit.fns.length,
      (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none) ∧
      (unit.roots, unit.hands) = (["w"], ["w"]) := by
    refine ⟨?unit, ?elaborated, ?invariants, ?contracts, ?functions, ?observed⟩
    case elaborated => cbv <;> exact Eq.refl _
    case invariants => cbv
    case contracts => cbv
    case functions =>
      intro f
      rcases f with ⟨index, bound⟩
      have small : index < 2 := bound
      rcases (by omega : index = 0 ∨ index = 1) with rfl | rfl <;>
        constructor <;> cbv
    case observed => cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = entry_via_ok_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 entry_via_ok_items)) entry_via_ok_elaborated))
  cases same
  exact facts

theorem entry_via_ok_lowered : UebersetzeProben2.lowerStage entry_via_ok_unit = "OK" :=
  UebersetzeProben2.lowerStage_ok entry_via_ok_unit entry_via_ok_metadata.1
    entry_via_ok_metadata.2.2.1 entry_via_ok_metadata.2.1

theorem entry_params_refused_text : entry_params_refused = String.ofList entry_params_refused_characters := by cbv

theorem entry_params_refused_parsed : (parseTopTief entry_params_refused_tokens).toOption.isSome = true := by cbv
def entry_params_refused_items : List SItemTief := (parseTopTief entry_params_refused_tokens).toOption.get entry_params_refused_parsed

theorem entry_params_refused_elaborated :
  elabU (pre108 entry_params_refused_items) = .error "dispatch names a function with parameters: no start-argument form: p" := by cbv

theorem entry_unknown_refused_text : entry_unknown_refused = String.ofList entry_unknown_refused_characters := by cbv

theorem entry_unknown_refused_parsed : (parseTopTief entry_unknown_refused_tokens).toOption.isSome = true := by cbv
def entry_unknown_refused_items : List SItemTief := (parseTopTief entry_unknown_refused_tokens).toOption.get entry_unknown_refused_parsed

theorem entry_unknown_refused_elaborated :
  elabU (pre108 entry_unknown_refused_items) = .error "dispatch names an unknown function: nix" := by cbv

theorem locks_plain_text : locks_plain = String.ofList locks_plain_characters := by cbv

theorem locks_plain_parsed : (parseTopTief locks_plain_tokens).toOption.isSome = true := by cbv
def locks_plain_items : List SItemTief := (parseTopTief locks_plain_tokens).toOption.get locks_plain_parsed

theorem locks_plain_elaborated : (elabU (pre108 locks_plain_items)).toOption.isSome = true := by cbv
def locks_plain_unit : Uebersetze.UProg := (elabU (pre108 locks_plain_items)).toOption.get locks_plain_elaborated

/-- The complete package is formed on the actual elaboration result before any caller index. -/
theorem locks_plain_metadata : locks_plain_unit.locks.map (·.masks) = [false] := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 locks_plain_items) = .ok unit ∧ unit.locks.map (·.masks) = [false] := by
    refine ⟨?unit, ?elaborated, ?observed⟩
    case elaborated => cbv <;> exact Eq.refl _
    case observed => cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = locks_plain_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_plain_items)) locks_plain_elaborated))
  cases same
  exact facts

theorem conc_ok_text : conc_ok = String.ofList conc_ok_characters := by cbv

theorem conc_ok_parsed : (parseTopTief conc_ok_tokens).toOption.isSome = true := by cbv
def conc_ok_items : List SItemTief := (parseTopTief conc_ok_tokens).toOption.get conc_ok_parsed

theorem conc_ok_elaborated : (elabU (pre108 conc_ok_items)).toOption.isSome = true := by cbv
def conc_ok_unit : Uebersetze.UProg := (elabU (pre108 conc_ok_items)).toOption.get conc_ok_elaborated

/-- The complete package is formed on the actual elaboration result before any caller index. -/
theorem conc_ok_metadata : (conc_ok_unit.roots, conc_ok_unit.hands) = (["w", "v"], []) := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 conc_ok_items) = .ok unit ∧ (unit.roots, unit.hands) = (["w", "v"], []) := by
    refine ⟨?unit, ?elaborated, ?observed⟩
    case elaborated => cbv <;> exact Eq.refl _
    case observed => cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = conc_ok_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 conc_ok_items)) conc_ok_elaborated))
  cases same
  exact facts

theorem conc_first_text : conc_first = String.ofList conc_first_characters := by cbv

theorem conc_first_parsed : (parseTopTief conc_first_tokens).toOption.isSome = true := by cbv
def conc_first_items : List SItemTief := (parseTopTief conc_first_tokens).toOption.get conc_first_parsed

theorem conc_first_elaborated : (elabU (pre108 conc_first_items)).toOption.isSome = true := by cbv
def conc_first_unit : Uebersetze.UProg := (elabU (pre108 conc_first_items)).toOption.get conc_first_elaborated

/-- The complete package is formed on the actual elaboration result before any caller index. -/
theorem conc_first_metadata : (conc_first_unit.roots, conc_first_unit.hands) = (["w", "v"], []) := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 conc_first_items) = .ok unit ∧ (unit.roots, unit.hands) = (["w", "v"], []) := by
    refine ⟨?unit, ?elaborated, ?observed⟩
    case elaborated => cbv <;> exact Eq.refl _
    case observed => cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = conc_first_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 conc_first_items)) conc_first_elaborated))
  cases same
  exact facts

theorem conc_args_ok_text : conc_args_ok = String.ofList conc_args_ok_characters := by cbv

theorem conc_args_ok_parsed : (parseTopTief conc_args_ok_tokens).toOption.isSome = true := by cbv
def conc_args_ok_items : List SItemTief := (parseTopTief conc_args_ok_tokens).toOption.get conc_args_ok_parsed

theorem conc_args_ok_elaborated : (elabU (pre108 conc_args_ok_items)).toOption.isSome = true := by cbv
def conc_args_ok_unit : Uebersetze.UProg := (elabU (pre108 conc_args_ok_items)).toOption.get conc_args_ok_elaborated

/-- The complete package is formed on the actual elaboration result before any caller index. -/
theorem conc_args_ok_metadata : (conc_args_ok_unit.roots, conc_args_ok_unit.hands) = (["p"], []) := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 conc_args_ok_items) = .ok unit ∧ (unit.roots, unit.hands) = (["p"], []) := by
    refine ⟨?unit, ?elaborated, ?observed⟩
    case elaborated => cbv <;> exact Eq.refl _
    case observed => cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = conc_args_ok_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 conc_args_ok_items)) conc_args_ok_elaborated))
  cases same
  exact facts

theorem conc_params_refused_text : conc_params_refused = String.ofList conc_params_refused_characters := by cbv

theorem conc_params_refused_parsed : (parseTopTief conc_params_refused_tokens).toOption.isSome = true := by cbv
def conc_params_refused_items : List SItemTief := (parseTopTief conc_params_refused_tokens).toOption.get conc_params_refused_parsed

theorem conc_params_refused_elaborated :
  elabU (pre108 conc_params_refused_items) = .error "concurrent member with 0 arguments for 1 parameters: p" := by cbv

theorem conc_arg_range_refused_text : conc_arg_range_refused = String.ofList conc_arg_range_refused_characters := by cbv

theorem conc_arg_range_refused_parsed : (parseTopTief conc_arg_range_refused_tokens).toOption.isSome = true := by cbv
def conc_arg_range_refused_items : List SItemTief := (parseTopTief conc_arg_range_refused_tokens).toOption.get conc_arg_range_refused_parsed

theorem conc_arg_range_refused_elaborated :
  elabU (pre108 conc_arg_range_refused_items) = .error "concurrent member with an argument outside its parameter's type: p" := by cbv

theorem conc_ptr_ok_text : conc_ptr_ok = String.ofList conc_ptr_ok_characters := by cbv

theorem conc_ptr_ok_parsed : (parseTopTief conc_ptr_ok_tokens).toOption.isSome = true := by cbv
def conc_ptr_ok_items : List SItemTief := (parseTopTief conc_ptr_ok_tokens).toOption.get conc_ptr_ok_parsed

theorem conc_ptr_ok_elaborated : (elabU (pre108 conc_ptr_ok_items)).toOption.isSome = true := by cbv
def conc_ptr_ok_unit : Uebersetze.UProg := (elabU (pre108 conc_ptr_ok_items)).toOption.get conc_ptr_ok_elaborated

/-- The complete package is formed on the actual elaboration result before any caller index. -/
theorem conc_ptr_ok_metadata : (conc_ptr_ok_unit.roots, conc_ptr_ok_unit.hands) = (["p"], []) := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 conc_ptr_ok_items) = .ok unit ∧ (unit.roots, unit.hands) = (["p"], []) := by
    refine ⟨?unit, ?elaborated, ?observed⟩
    case elaborated => cbv <;> exact Eq.refl _
    case observed => cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = conc_ptr_ok_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 conc_ptr_ok_items)) conc_ptr_ok_elaborated))
  cases same
  exact facts

theorem conc_ptr_refused_text : conc_ptr_refused = String.ofList conc_ptr_refused_characters := by cbv

theorem conc_ptr_refused_parsed : (parseTopTief conc_ptr_refused_tokens).toOption.isSome = true := by cbv
def conc_ptr_refused_items : List SItemTief := (parseTopTief conc_ptr_refused_tokens).toOption.get conc_ptr_refused_parsed

theorem conc_ptr_refused_elaborated :
  elabU (pre108 conc_ptr_refused_items) = .error "concurrent member with an argument outside its parameter's type: p" := by cbv

theorem conc_unknown_refused_text : conc_unknown_refused = String.ofList conc_unknown_refused_characters := by cbv

theorem conc_unknown_refused_parsed : (parseTopTief conc_unknown_refused_tokens).toOption.isSome = true := by cbv
def conc_unknown_refused_items : List SItemTief := (parseTopTief conc_unknown_refused_tokens).toOption.get conc_unknown_refused_parsed

theorem conc_unknown_refused_elaborated :
  elabU (pre108 conc_unknown_refused_items) = .error "concurrent member names an unknown function: nix" := by cbv

theorem mask_src_text : mask_src = String.ofList mask_src_characters := by cbv

theorem mask_src_parsed : (parseTopTief mask_src_tokens).toOption.isSome = true := by cbv
def mask_src_items : List SItemTief := (parseTopTief mask_src_tokens).toOption.get mask_src_parsed

theorem mask_src_elaborated : (elabU (pre108 mask_src_items)).toOption.isSome = true := by cbv
def mask_src_unit : Uebersetze.UProg := (elabU (pre108 mask_src_items)).toOption.get mask_src_elaborated

/-- The complete package is formed on the actual elaboration result before any caller index. -/
theorem mask_src_metadata : mask_src_unit.invs = [] ∧ contractGate mask_src_unit = true ∧
    (∀ f : Fin mask_src_unit.fns.length,
      (lowerFnAt mask_src_unit f).toOption.isSome = true ∧ (fnAt mask_src_unit f).decreases = none) ∧
    mask_src_unit.locks.map (·.masks) = [true] := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 mask_src_items) = .ok unit ∧ unit.invs = [] ∧ contractGate unit = true ∧
      (∀ f : Fin unit.fns.length,
      (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none) ∧
      unit.locks.map (·.masks) = [true] := by
    refine ⟨?unit, ?elaborated, ?invariants, ?contracts, ?functions, ?observed⟩
    case elaborated => cbv <;> exact Eq.refl _
    case invariants => cbv
    case contracts => cbv
    case functions =>
      intro f
      rcases f with ⟨index, bound⟩
      have small : index < 1 := bound
      have zero : index = 0 := by omega
      subst index
      constructor <;> cbv
    case observed => cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = mask_src_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 mask_src_items)) mask_src_elaborated))
  cases same
  exact facts

theorem mask_src_lowered : UebersetzeProben2.lowerStage mask_src_unit = "OK" :=
  UebersetzeProben2.lowerStage_ok mask_src_unit mask_src_metadata.1
    mask_src_metadata.2.2.1 mask_src_metadata.2.1

theorem other_mask_text : "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0 masks nmi; }" = String.ofList other_mask_characters := by cbv

theorem other_mask_parsed : (parseTopTief other_mask_tokens).toOption.isSome = true := by cbv
def other_mask_items : List SItemTief := (parseTopTief other_mask_tokens).toOption.get other_mask_parsed

theorem other_mask_elaborated :
  elabU (pre108 other_mask_items) = .error "lock masks something but irqs: no G form" := by cbv

end Gabbro.Grammatik.Parser.UebersetzeProben3
