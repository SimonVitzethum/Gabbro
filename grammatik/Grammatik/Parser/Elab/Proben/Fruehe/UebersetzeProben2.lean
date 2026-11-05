/-
  File:      Grammatik/Parser/UebersetzeProben2.lean
  Subject:   Sieve (a), parser lane: witnesses and planted defects of walls 6 (`locks` blocks) and 7
             (`entry` roots). A second file because the kernel probes of one file share one memory
             budget (measured 2026-09-30: the first file alone passes 7 GB with these twelve added).
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben2Lexical
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben2

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

-- Keep the canonical fuel record symbolic: evaluate its selected operation, not all 100000 levels.
-- These local proof rules are equations of the unchanged producer, not another lowering path.
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL
attribute [local cbv_eval] seq_select struct_select lowStufe_seq lowStufe_struct

-- Build each complete indexed package at the actual elaboration result, then transport
-- the whole package to the extracted unit. Do not normalize a caller-indexed opaque unit.

/-! WALL 6 (2026-09-30): `locks L { ... }` -- read as flat markers, lowered to `Stmt.locks` with the rank
    rule (`H006`) as a Bool the kernel decides; a nested take of the same lock and a rank that does not
    grow are refused by the lowering, a call that needs the held lock's set is refused by the elaborator. -/

private theorem locks1_ok_parsed :
    (parseTopTief locks1_ok_tokens).toOption.isSome = true := by cbv
private def locks1_ok_items := (parseTopTief locks1_ok_tokens).toOption.get locks1_ok_parsed

private theorem locks1_ok_elaborated :
    (elabU (pre108 locks1_ok_items)).toOption.isSome = true := by cbv
private def locks1_ok_unit := (elabU (pre108 locks1_ok_items)).toOption.get locks1_ok_elaborated

private theorem locks1_ok_metadata : locks1_ok_unit.invs = [] ∧
    contractGate locks1_ok_unit = true ∧ ∀ f : Fin locks1_ok_unit.fns.length,
      (lowerFnAt locks1_ok_unit f).toOption.isSome = true ∧
        (fnAt locks1_ok_unit f).decreases = none := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 locks1_ok_items) = .ok unit ∧ unit.invs = [] ∧ contractGate unit = true ∧
      ∀ f : Fin unit.fns.length,
        (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none := by
    refine ⟨?unit, ?elaborated, ?invariants, ?contracts, ?functions⟩
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
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = locks1_ok_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks1_ok_items)) locks1_ok_elaborated))
  cases same
  exact facts

private theorem locks1_ok_functions (f : Fin locks1_ok_unit.fns.length) :
    (lowerFnAt locks1_ok_unit f).toOption.isSome = true ∧
      (fnAt locks1_ok_unit f).decreases = none := locks1_ok_metadata.2.2 f

private theorem locks1_ok_lowered : lowerStage locks1_ok_unit = "OK" :=
  lowerStage_ok locks1_ok_unit locks1_ok_metadata.1 locks1_ok_functions locks1_ok_metadata.2.1

theorem locks1_ok_stufe : stufe locks1_ok = "OK" :=
  stufe_phases (source := locks1_ok) (characters := locks1_ok_characters)
    (tokens := locks1_ok_tokens) (items := locks1_ok_items) (unit := locks1_ok_unit) (answer := "OK")
    (by cbv) locks1_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks1_ok_tokens) locks1_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks1_ok_items)) locks1_ok_elaborated) locks1_ok_lowered

private theorem locks2_ok_parsed :
    (parseTopTief locks2_ok_tokens).toOption.isSome = true := by cbv
private def locks2_ok_items := (parseTopTief locks2_ok_tokens).toOption.get locks2_ok_parsed

private theorem locks2_ok_elaborated :
    (elabU (pre108 locks2_ok_items)).toOption.isSome = true := by cbv
private def locks2_ok_unit := (elabU (pre108 locks2_ok_items)).toOption.get locks2_ok_elaborated

private theorem locks2_ok_metadata : locks2_ok_unit.invs = [] ∧
    contractGate locks2_ok_unit = true ∧ ∀ f : Fin locks2_ok_unit.fns.length,
      (lowerFnAt locks2_ok_unit f).toOption.isSome = true ∧
        (fnAt locks2_ok_unit f).decreases = none := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 locks2_ok_items) = .ok unit ∧ unit.invs = [] ∧ contractGate unit = true ∧
      ∀ f : Fin unit.fns.length,
        (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none := by
    refine ⟨?unit, ?elaborated, ?invariants, ?contracts, ?functions⟩
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
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = locks2_ok_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks2_ok_items)) locks2_ok_elaborated))
  cases same
  exact facts

private theorem locks2_ok_functions (f : Fin locks2_ok_unit.fns.length) :
    (lowerFnAt locks2_ok_unit f).toOption.isSome = true ∧
      (fnAt locks2_ok_unit f).decreases = none := locks2_ok_metadata.2.2 f

private theorem locks2_ok_lowered : lowerStage locks2_ok_unit = "OK" :=
  lowerStage_ok locks2_ok_unit locks2_ok_metadata.1 locks2_ok_functions locks2_ok_metadata.2.1

theorem locks2_ok_stufe : stufe locks2_ok = "OK" :=
  stufe_phases (source := locks2_ok) (characters := locks2_ok_characters)
    (tokens := locks2_ok_tokens) (items := locks2_ok_items) (unit := locks2_ok_unit) (answer := "OK")
    (by cbv) locks2_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks2_ok_tokens) locks2_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks2_ok_items)) locks2_ok_elaborated) locks2_ok_lowered

private theorem locks_nested_same_parsed :
    (parseTopTief locks_nested_same_tokens).toOption.isSome = true := by cbv
private def locks_nested_same_items := (parseTopTief locks_nested_same_tokens).toOption.get locks_nested_same_parsed

private theorem locks_nested_same_elaborated :
    (elabU (pre108 locks_nested_same_items)).toOption.isSome = true := by cbv
private def locks_nested_same_unit := (elabU (pre108 locks_nested_same_items)).toOption.get locks_nested_same_elaborated

private theorem locks_nested_same_metadata : locks_nested_same_unit.invs = [] ∧
    (∀ f : Fin locks_nested_same_unit.fns.length, lowerFnAt locks_nested_same_unit f = .error "lower: locks against a held lock of higher or equal rank") ∧
    ∃ f : Fin locks_nested_same_unit.fns.length, lowerFnAt locks_nested_same_unit f = .error "lower: locks against a held lock of higher or equal rank" := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 locks_nested_same_items) = .ok unit ∧ unit.invs = [] ∧
      (∀ f : Fin unit.fns.length, lowerFnAt unit f = .error "lower: locks against a held lock of higher or equal rank") ∧
      ∃ f : Fin unit.fns.length, lowerFnAt unit f = .error "lower: locks against a held lock of higher or equal rank" := by
    refine ⟨?unit, ?elaborated, ?invariants, ?functions, ?bad⟩
    case elaborated => cbv <;> exact Eq.refl _
    case invariants => cbv
    case functions =>
      intro f
      rcases f with ⟨index, bound⟩
      have small : index < 1 := bound
      have zero : index = 0 := by omega
      subst index
      cbv
    case bad =>
      refine ⟨⟨0, by decide⟩, ?_⟩
      cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = locks_nested_same_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_nested_same_items)) locks_nested_same_elaborated))
  cases same
  exact facts

private theorem locks_nested_same_failed (f : Fin locks_nested_same_unit.fns.length) :
    lowerFnAt locks_nested_same_unit f = .error "lower: locks against a held lock of higher or equal rank" := locks_nested_same_metadata.2.1 f

private theorem locks_nested_same_lowered : lowerStage locks_nested_same_unit = "lower: lower: locks against a held lock of higher or equal rank" :=
  lowerStage_error locks_nested_same_unit "lower: locks against a held lock of higher or equal rank" locks_nested_same_metadata.1
    (fun f => Or.inl (locks_nested_same_failed f)) locks_nested_same_metadata.2.2

theorem locks_nested_same_stufe : stufe locks_nested_same = "lower: lower: locks against a held lock of higher or equal rank" :=
  stufe_phases (source := locks_nested_same) (characters := locks_nested_same_characters)
    (tokens := locks_nested_same_tokens) (items := locks_nested_same_items) (unit := locks_nested_same_unit) (answer := "lower: lower: locks against a held lock of higher or equal rank")
    (by cbv) locks_nested_same_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks_nested_same_tokens) locks_nested_same_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_nested_same_items)) locks_nested_same_elaborated) locks_nested_same_lowered

private theorem locks_rank_ok_parsed :
    (parseTopTief locks_rank_ok_tokens).toOption.isSome = true := by cbv
private def locks_rank_ok_items := (parseTopTief locks_rank_ok_tokens).toOption.get locks_rank_ok_parsed

private theorem locks_rank_ok_elaborated :
    (elabU (pre108 locks_rank_ok_items)).toOption.isSome = true := by cbv
private def locks_rank_ok_unit := (elabU (pre108 locks_rank_ok_items)).toOption.get locks_rank_ok_elaborated

private theorem locks_rank_ok_metadata : locks_rank_ok_unit.invs = [] ∧
    contractGate locks_rank_ok_unit = true ∧ ∀ f : Fin locks_rank_ok_unit.fns.length,
      (lowerFnAt locks_rank_ok_unit f).toOption.isSome = true ∧
        (fnAt locks_rank_ok_unit f).decreases = none := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 locks_rank_ok_items) = .ok unit ∧ unit.invs = [] ∧ contractGate unit = true ∧
      ∀ f : Fin unit.fns.length,
        (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none := by
    refine ⟨?unit, ?elaborated, ?invariants, ?contracts, ?functions⟩
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
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = locks_rank_ok_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_rank_ok_items)) locks_rank_ok_elaborated))
  cases same
  exact facts

private theorem locks_rank_ok_functions (f : Fin locks_rank_ok_unit.fns.length) :
    (lowerFnAt locks_rank_ok_unit f).toOption.isSome = true ∧
      (fnAt locks_rank_ok_unit f).decreases = none := locks_rank_ok_metadata.2.2 f

private theorem locks_rank_ok_lowered : lowerStage locks_rank_ok_unit = "OK" :=
  lowerStage_ok locks_rank_ok_unit locks_rank_ok_metadata.1 locks_rank_ok_functions locks_rank_ok_metadata.2.1

theorem locks_rank_ok_stufe : stufe locks_rank_ok = "OK" :=
  stufe_phases (source := locks_rank_ok) (characters := locks_rank_ok_characters)
    (tokens := locks_rank_ok_tokens) (items := locks_rank_ok_items) (unit := locks_rank_ok_unit) (answer := "OK")
    (by cbv) locks_rank_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks_rank_ok_tokens) locks_rank_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_rank_ok_items)) locks_rank_ok_elaborated) locks_rank_ok_lowered

private theorem locks_rank_down_parsed :
    (parseTopTief locks_rank_down_tokens).toOption.isSome = true := by cbv
private def locks_rank_down_items := (parseTopTief locks_rank_down_tokens).toOption.get locks_rank_down_parsed

private theorem locks_rank_down_elaborated :
    (elabU (pre108 locks_rank_down_items)).toOption.isSome = true := by cbv
private def locks_rank_down_unit := (elabU (pre108 locks_rank_down_items)).toOption.get locks_rank_down_elaborated

private theorem locks_rank_down_metadata : locks_rank_down_unit.invs = [] ∧
    (∀ f : Fin locks_rank_down_unit.fns.length, lowerFnAt locks_rank_down_unit f = .error "lower: locks against a held lock of higher or equal rank") ∧
    ∃ f : Fin locks_rank_down_unit.fns.length, lowerFnAt locks_rank_down_unit f = .error "lower: locks against a held lock of higher or equal rank" := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 locks_rank_down_items) = .ok unit ∧ unit.invs = [] ∧
      (∀ f : Fin unit.fns.length, lowerFnAt unit f = .error "lower: locks against a held lock of higher or equal rank") ∧
      ∃ f : Fin unit.fns.length, lowerFnAt unit f = .error "lower: locks against a held lock of higher or equal rank" := by
    refine ⟨?unit, ?elaborated, ?invariants, ?functions, ?bad⟩
    case elaborated => cbv <;> exact Eq.refl _
    case invariants => cbv
    case functions =>
      intro f
      rcases f with ⟨index, bound⟩
      have small : index < 1 := bound
      have zero : index = 0 := by omega
      subst index
      cbv
    case bad =>
      refine ⟨⟨0, by decide⟩, ?_⟩
      cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = locks_rank_down_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_rank_down_items)) locks_rank_down_elaborated))
  cases same
  exact facts

private theorem locks_rank_down_failed (f : Fin locks_rank_down_unit.fns.length) :
    lowerFnAt locks_rank_down_unit f = .error "lower: locks against a held lock of higher or equal rank" := locks_rank_down_metadata.2.1 f

private theorem locks_rank_down_lowered : lowerStage locks_rank_down_unit = "lower: lower: locks against a held lock of higher or equal rank" :=
  lowerStage_error locks_rank_down_unit "lower: locks against a held lock of higher or equal rank" locks_rank_down_metadata.1
    (fun f => Or.inl (locks_rank_down_failed f)) locks_rank_down_metadata.2.2

theorem locks_rank_down_stufe : stufe locks_rank_down = "lower: lower: locks against a held lock of higher or equal rank" :=
  stufe_phases (source := locks_rank_down) (characters := locks_rank_down_characters)
    (tokens := locks_rank_down_tokens) (items := locks_rank_down_items) (unit := locks_rank_down_unit) (answer := "lower: lower: locks against a held lock of higher or equal rank")
    (by cbv) locks_rank_down_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks_rank_down_tokens) locks_rank_down_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_rank_down_items)) locks_rank_down_elaborated) locks_rank_down_lowered

private theorem locks_call_needing_it_parsed :
    (parseTopTief locks_call_needing_it_tokens).toOption.isSome = true := by cbv
private def locks_call_needing_it_items := (parseTopTief locks_call_needing_it_tokens).toOption.get locks_call_needing_it_parsed

private theorem locks_call_needing_it_elaborated :
    (elabU (pre108 locks_call_needing_it_items)).toOption.isSome = true := by cbv
private def locks_call_needing_it_unit := (elabU (pre108 locks_call_needing_it_items)).toOption.get locks_call_needing_it_elaborated

private theorem locks_call_needing_it_metadata : locks_call_needing_it_unit.invs = [] ∧
    (∀ f : Fin locks_call_needing_it_unit.fns.length,
      lowerFnAt locks_call_needing_it_unit f = .error "call: a held lock does not rank below the callee's floor" ∨
        (lowerFnAt locks_call_needing_it_unit f).toOption.isSome = true) ∧
    ∃ f : Fin locks_call_needing_it_unit.fns.length, lowerFnAt locks_call_needing_it_unit f =
      .error "call: a held lock does not rank below the callee's floor" := by
  have certificate : ∃ unit : Uebersetze.UProg,
      elabU (pre108 locks_call_needing_it_items) = .ok unit ∧ unit.invs = [] ∧
      (∀ f : Fin unit.fns.length,
        lowerFnAt unit f = .error "call: a held lock does not rank below the callee's floor" ∨
          (lowerFnAt unit f).toOption.isSome = true) ∧
      ∃ f : Fin unit.fns.length, lowerFnAt unit f = .error "call: a held lock does not rank below the callee's floor" := by
    refine ⟨?unit, ?elaborated, ?invariants, ?outcomes, ?bad⟩
    case elaborated => cbv <;> exact Eq.refl _
    case invariants => cbv
    case outcomes =>
      intro f
      rcases f with ⟨index, bound⟩
      have small : index < 2 := bound
      rcases (by omega : index = 0 ∨ index = 1) with rfl | rfl
      · right
        cbv
      · left
        cbv
    case bad =>
      refine ⟨⟨1, by decide⟩, ?_⟩
      cbv
  obtain ⟨unit, elaborated, facts⟩ := certificate
  have same : unit = locks_call_needing_it_unit := Except.ok.inj (elaborated.symm.trans
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_call_needing_it_items)) locks_call_needing_it_elaborated))
  cases same
  exact facts

private theorem locks_call_needing_it_outcomes (f : Fin locks_call_needing_it_unit.fns.length) :
    lowerFnAt locks_call_needing_it_unit f = .error "call: a held lock does not rank below the callee's floor" ∨
      (lowerFnAt locks_call_needing_it_unit f).toOption.isSome = true := locks_call_needing_it_metadata.2.1 f

private theorem locks_call_needing_it_lowered :
    lowerStage locks_call_needing_it_unit = "lower: call: a held lock does not rank below the callee's floor" :=
  lowerStage_error locks_call_needing_it_unit "call: a held lock does not rank below the callee's floor" locks_call_needing_it_metadata.1
    locks_call_needing_it_outcomes locks_call_needing_it_metadata.2.2

theorem locks_call_needing_it_stufe : stufe locks_call_needing_it = "lower: call: a held lock does not rank below the callee's floor" :=
  stufe_phases (source := locks_call_needing_it) (characters := locks_call_needing_it_characters)
    (tokens := locks_call_needing_it_tokens) (items := locks_call_needing_it_items) (unit := locks_call_needing_it_unit) (answer := "lower: call: a held lock does not rank below the callee's floor")
    (by cbv) locks_call_needing_it_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks_call_needing_it_tokens) locks_call_needing_it_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_call_needing_it_items)) locks_call_needing_it_elaborated) locks_call_needing_it_lowered

end Gabbro.Grammatik.Parser.UebersetzeProben2
