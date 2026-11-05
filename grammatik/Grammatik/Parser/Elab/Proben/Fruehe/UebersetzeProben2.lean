/-
  File:      Grammatik/Parser/UebersetzeProben2.lean
  Subject:   Sieve (a), parser lane: witnesses and planted defects of walls 6 (`locks` blocks) and 7
             (`entry` roots). A second file because the kernel probes of one file share one memory
             budget (measured 2026-09-30: the first file alone passes 7 GB with these twelve added).
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben2Basis
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

/-- Compose fully instantiated scanner equations; no source suffix is inferred by rewriting. -/
private theorem scan_compose {source rest : List Char} {fuel remaining : Nat}
    {emitted tokens : List Token} (tail : scan false rest remaining = .ok tokens)
    (head : scan false source fuel = emitted.foldr (fun t result => Except.map (t :: ·) result) (scan false rest remaining)) :
    scan false source fuel = .ok (emitted ++ tokens) := by
  simpa only [tail, token_maps, Except.map] using head

/-! WALL 6 (2026-09-30): `locks L { ... }` -- read as flat markers, lowered to `Stmt.locks` with the rank
    rule (`H006`) as a Bool the kernel decides; a nested take of the same lock and a rank that does not
    grow are refused by the lowering, a call that needs the held lock's set is refused by the elaborator. -/

def locks1_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; } } }"

private def locks1_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't',
   ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}',
   ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r',
   'a', 'n', 'k', ' ', '0', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':', ' ', 'p', 't', 'r',
   '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' ', 'i', ' ', ':', ' ', 'i', 'n', 'd', 'e',
   'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't',
   'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '}', ' ', '{', ' ',
   'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=',
   ' ', '1', ';', ' ', '}', ' ', '}', ' ', '}']

private def locks1_ok_tokens : List Token :=
    table_tokens ++ [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++ effect_tokens ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 1 ++ [.zeichen "}", .zeichen "}", .zeichen "}", .ende]

private theorem locks1_ok_lexed : lexL locks1_ok_characters = .ok locks1_ok_tokens := by
  change scan false locks1_ok_characters 202 = .ok locks1_ok_tokens
  have composed := scan_compose (scan_end 78) (scan_close (locks1_ok_characters.drop 200) 79)
  have composed := scan_compose composed (scan_close (locks1_ok_characters.drop 198) 81)
  have composed := scan_compose composed (scan_write_one (locks1_ok_characters.drop 196) 83)
  have composed := scan_compose composed (scan_take (locks1_ok_characters.drop 178) 97)
  have composed := scan_compose composed (scan_open (locks1_ok_characters.drop 168) 103)
  have composed := scan_compose composed (scan_close (locks1_ok_characters.drop 166) 105)
  have composed := scan_compose composed (scan_effects (locks1_ok_characters.drop 164) 107)
  have composed := scan_compose composed (scan_parameters (locks1_ok_characters.drop 140) 118)
  have composed := scan_compose composed (scan_writer (locks1_ok_characters.drop 112) 133)
  have composed := scan_compose composed (scan_lock (locks1_ok_characters.drop 79) 154)
  have composed := scan_compose composed (scan_slot (locks1_ok_characters.drop 49) 171)
  exact scan_compose composed (scan_prelude (locks1_ok_characters.drop 29) 186)

private theorem locks1_ok_parsed :
    (parseTopTief locks1_ok_tokens).toOption.isSome = true := by cbv
private def locks1_ok_items := (parseTopTief locks1_ok_tokens).toOption.get locks1_ok_parsed

private theorem locks1_ok_elaborated :
    (elabU (pre108 locks1_ok_items)).toOption.isSome = true := by cbv
private def locks1_ok_unit := (elabU (pre108 locks1_ok_items)).toOption.get locks1_ok_elaborated

private theorem locks1_ok_count : locks1_ok_unit.fns.length = 1 := by cbv

private theorem locks1_ok_functions (f : Fin locks1_ok_unit.fns.length) :
    (lowerFnAt locks1_ok_unit f).toOption.isSome = true ∧
      (fnAt locks1_ok_unit f).decreases = none :=
  singleFn_all locks1_ok_unit locks1_ok_count
    (fun f => (lowerFnAt locks1_ok_unit f).toOption.isSome = true ∧
      (fnAt locks1_ok_unit f).decreases = none) (by constructor <;> cbv <;> rfl) f

private theorem locks1_ok_lowered : lowerStage locks1_ok_unit = "OK" :=
  lowerStage_ok locks1_ok_unit (by cbv) locks1_ok_functions (by cbv)

theorem locks1_ok_stufe : stufe locks1_ok = "OK" :=
  stufe_phases (source := locks1_ok) (characters := locks1_ok_characters)
    (tokens := locks1_ok_tokens) (items := locks1_ok_items) (unit := locks1_ok_unit) (answer := "OK")
    (by cbv) locks1_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks1_ok_tokens) locks1_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks1_ok_items)) locks1_ok_elaborated) locks1_ok_lowered

def locks2_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; k.slots[i].v = 2; } locks L { k.slots[i].v = 3; } } }"

private def locks2_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't',
   ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}',
   ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r',
   'a', 'n', 'k', ' ', '0', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':', ' ', 'p', 't', 'r',
   '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' ', 'i', ' ', ':', ' ', 'i', 'n', 'd', 'e',
   'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't',
   'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '}', ' ', '{', ' ',
   'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=',
   ' ', '1', ';', ' ', 'k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '2', ';', ' ', '}', ' ',
   'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=',
   ' ', '3', ';', ' ', '}', ' ', '}', ' ', '}']

private def locks2_ok_tokens : List Token :=
    table_tokens ++ [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++ effect_tokens ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 1 ++ write_tokens 2 ++ [.zeichen "}"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 3 ++ [.zeichen "}", .zeichen "}", .zeichen "}", .ende]

private theorem locks2_ok_lexed : lexL locks2_ok_characters = .ok locks2_ok_tokens := by
  change scan false locks2_ok_characters 250 = .ok locks2_ok_tokens
  have composed := scan_compose (scan_end 90) (scan_close (locks2_ok_characters.drop 248) 91)
  have composed := scan_compose composed (scan_close (locks2_ok_characters.drop 246) 93)
  have composed := scan_compose composed (scan_write_three (locks2_ok_characters.drop 244) 95)
  have composed := scan_compose composed (scan_take (locks2_ok_characters.drop 226) 109)
  have composed := scan_compose composed (scan_close (locks2_ok_characters.drop 216) 115)
  have composed := scan_compose composed (scan_write_two (locks2_ok_characters.drop 214) 117)
  have composed := scan_compose composed (scan_write_one (locks2_ok_characters.drop 196) 131)
  have composed := scan_compose composed (scan_take (locks2_ok_characters.drop 178) 145)
  have composed := scan_compose composed (scan_open (locks2_ok_characters.drop 168) 151)
  have composed := scan_compose composed (scan_close (locks2_ok_characters.drop 166) 153)
  have composed := scan_compose composed (scan_effects (locks2_ok_characters.drop 164) 155)
  have composed := scan_compose composed (scan_parameters (locks2_ok_characters.drop 140) 166)
  have composed := scan_compose composed (scan_writer (locks2_ok_characters.drop 112) 181)
  have composed := scan_compose composed (scan_lock (locks2_ok_characters.drop 79) 202)
  have composed := scan_compose composed (scan_slot (locks2_ok_characters.drop 49) 219)
  exact scan_compose composed (scan_prelude (locks2_ok_characters.drop 29) 234)

private theorem locks2_ok_parsed :
    (parseTopTief locks2_ok_tokens).toOption.isSome = true := by cbv
private def locks2_ok_items := (parseTopTief locks2_ok_tokens).toOption.get locks2_ok_parsed

private theorem locks2_ok_elaborated :
    (elabU (pre108 locks2_ok_items)).toOption.isSome = true := by cbv
private def locks2_ok_unit := (elabU (pre108 locks2_ok_items)).toOption.get locks2_ok_elaborated

private theorem locks2_ok_count : locks2_ok_unit.fns.length = 1 := by cbv

private theorem locks2_ok_functions (f : Fin locks2_ok_unit.fns.length) :
    (lowerFnAt locks2_ok_unit f).toOption.isSome = true ∧
      (fnAt locks2_ok_unit f).decreases = none :=
  singleFn_all locks2_ok_unit locks2_ok_count
    (fun f => (lowerFnAt locks2_ok_unit f).toOption.isSome = true ∧
      (fnAt locks2_ok_unit f).decreases = none) (by constructor <;> cbv <;> rfl) f

private theorem locks2_ok_lowered : lowerStage locks2_ok_unit = "OK" :=
  lowerStage_ok locks2_ok_unit (by cbv) locks2_ok_functions (by cbv)

theorem locks2_ok_stufe : stufe locks2_ok = "OK" :=
  stufe_phases (source := locks2_ok) (characters := locks2_ok_characters)
    (tokens := locks2_ok_tokens) (items := locks2_ok_items) (unit := locks2_ok_unit) (answer := "OK")
    (by cbv) locks2_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks2_ok_tokens) locks2_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks2_ok_items)) locks2_ok_elaborated) locks2_ok_lowered

def locks_nested_same : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { locks L { k.slots[i].v = 1; } } } }"

private def locks_nested_same_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't',
   ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}',
   ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r',
   'a', 'n', 'k', ' ', '0', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':', ' ', 'p', 't', 'r',
   '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' ', 'i', ' ', ':', ' ', 'i', 'n', 'd', 'e',
   'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't',
   'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '}', ' ', '{', ' ',
   'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'k', '.', 's', 'l',
   'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '1', ';', ' ', '}', ' ', '}', ' ', '}', ' ', '}']

private def locks_nested_same_tokens : List Token :=
    table_tokens ++ [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++ effect_tokens ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 1 ++ [.zeichen "}", .zeichen "}", .zeichen "}", .zeichen "}", .ende]

private theorem locks_nested_same_lexed : lexL locks_nested_same_characters = .ok locks_nested_same_tokens := by
  change scan false locks_nested_same_characters 214 = .ok locks_nested_same_tokens
  have composed := scan_compose (scan_end 82) (scan_close (locks_nested_same_characters.drop 212) 83)
  have composed := scan_compose composed (scan_close (locks_nested_same_characters.drop 210) 85)
  have composed := scan_compose composed (scan_close (locks_nested_same_characters.drop 208) 87)
  have composed := scan_compose composed (scan_write_one (locks_nested_same_characters.drop 206) 89)
  have composed := scan_compose composed (scan_take (locks_nested_same_characters.drop 188) 103)
  have composed := scan_compose composed (scan_take (locks_nested_same_characters.drop 178) 109)
  have composed := scan_compose composed (scan_open (locks_nested_same_characters.drop 168) 115)
  have composed := scan_compose composed (scan_close (locks_nested_same_characters.drop 166) 117)
  have composed := scan_compose composed (scan_effects (locks_nested_same_characters.drop 164) 119)
  have composed := scan_compose composed (scan_parameters (locks_nested_same_characters.drop 140) 130)
  have composed := scan_compose composed (scan_writer (locks_nested_same_characters.drop 112) 145)
  have composed := scan_compose composed (scan_lock (locks_nested_same_characters.drop 79) 166)
  have composed := scan_compose composed (scan_slot (locks_nested_same_characters.drop 49) 183)
  exact scan_compose composed (scan_prelude (locks_nested_same_characters.drop 29) 198)

private theorem locks_nested_same_parsed :
    (parseTopTief locks_nested_same_tokens).toOption.isSome = true := by cbv
private def locks_nested_same_items := (parseTopTief locks_nested_same_tokens).toOption.get locks_nested_same_parsed

private theorem locks_nested_same_elaborated :
    (elabU (pre108 locks_nested_same_items)).toOption.isSome = true := by cbv
private def locks_nested_same_unit := (elabU (pre108 locks_nested_same_items)).toOption.get locks_nested_same_elaborated

private theorem locks_nested_same_count : locks_nested_same_unit.fns.length = 1 := by cbv

private theorem locks_nested_same_failed (f : Fin locks_nested_same_unit.fns.length) :
    lowerFnAt locks_nested_same_unit f = .error "lower: locks against a held lock of higher or equal rank" :=
  singleFn_all locks_nested_same_unit locks_nested_same_count
    (fun f => lowerFnAt locks_nested_same_unit f = .error "lower: locks against a held lock of higher or equal rank")
    (by cbv <;> rfl) f

private theorem locks_nested_same_lowered : lowerStage locks_nested_same_unit = "lower: lower: locks against a held lock of higher or equal rank" :=
  lowerStage_error locks_nested_same_unit "lower: locks against a held lock of higher or equal rank" (by cbv)
    (fun f => Or.inl (locks_nested_same_failed f))
    ⟨singleFn locks_nested_same_unit locks_nested_same_count, locks_nested_same_failed _⟩

theorem locks_nested_same_stufe : stufe locks_nested_same = "lower: lower: locks against a held lock of higher or equal rank" :=
  stufe_phases (source := locks_nested_same) (characters := locks_nested_same_characters)
    (tokens := locks_nested_same_tokens) (items := locks_nested_same_items) (unit := locks_nested_same_unit) (answer := "lower: lower: locks against a held lock of higher or equal rank")
    (by cbv) locks_nested_same_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks_nested_same_tokens) locks_nested_same_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_nested_same_items)) locks_nested_same_elaborated) locks_nested_same_lowered

def locks_rank_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; lock M protects { } rank 1; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L, locks M } { locks L { locks M { k.slots[i].v = 1; } } } }"

private def locks_rank_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't',
   ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}',
   ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r',
   'a', 'n', 'k', ' ', '0', ';', ' ', 'l', 'o', 'c', 'k', ' ', 'M', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{',
   ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '1', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':',
   ' ', 'p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' ', 'i', ' ', ':', ' ',
   'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ',
   'w', 'r', 'i', 't', 'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ',',
   ' ', 'l', 'o', 'c', 'k', 's', ' ', 'M', ' ', '}', ' ', '{', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'l',
   'o', 'c', 'k', 's', ' ', 'M', ' ', '{', ' ', 'k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ',
   '1', ';', ' ', '}', ' ', '}', ' ', '}', ' ', '}']

private def locks_rank_ok_tokens : List Token :=
    table_tokens ++ [.wort "lock", .ident "M", .wort "protects", .zeichen "{", .zeichen "}", .wort "rank", .num 1, .zeichen ";"] ++ [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++
    [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L", .zeichen ",", .wort "locks", .ident "M"] ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ [.wort "locks", .ident "M", .zeichen "{"] ++ write_tokens 1 ++ [.zeichen "}", .zeichen "}", .zeichen "}", .zeichen "}", .ende]

private theorem locks_rank_ok_lexed : lexL locks_rank_ok_characters = .ok locks_rank_ok_tokens := by
  change scan false locks_rank_ok_characters 251 = .ok locks_rank_ok_tokens
  have composed := scan_compose (scan_end 99) (scan_close (locks_rank_ok_characters.drop 249) 100)
  have composed := scan_compose composed (scan_close (locks_rank_ok_characters.drop 247) 102)
  have composed := scan_compose composed (scan_close (locks_rank_ok_characters.drop 245) 104)
  have composed := scan_compose composed (scan_write_one (locks_rank_ok_characters.drop 243) 106)
  have composed := scan_compose composed (scan_take_second (locks_rank_ok_characters.drop 225) 120)
  have composed := scan_compose composed (scan_take (locks_rank_ok_characters.drop 215) 126)
  have composed := scan_compose composed (scan_open (locks_rank_ok_characters.drop 205) 132)
  have composed := scan_compose composed (scan_close (locks_rank_ok_characters.drop 203) 134)
  have composed := scan_compose composed (scan_two_effects (locks_rank_ok_characters.drop 201) 136)
  have composed := scan_compose composed (scan_parameters (locks_rank_ok_characters.drop 168) 152)
  have composed := scan_compose composed (scan_writer (locks_rank_ok_characters.drop 140) 167)
  have composed := scan_compose composed (scan_second_lock (locks_rank_ok_characters.drop 107) 188)
  have composed := scan_compose composed (scan_lock (locks_rank_ok_characters.drop 79) 203)
  have composed := scan_compose composed (scan_slot (locks_rank_ok_characters.drop 49) 220)
  exact scan_compose composed (scan_prelude (locks_rank_ok_characters.drop 29) 235)

private theorem locks_rank_ok_parsed :
    (parseTopTief locks_rank_ok_tokens).toOption.isSome = true := by cbv
private def locks_rank_ok_items := (parseTopTief locks_rank_ok_tokens).toOption.get locks_rank_ok_parsed

private theorem locks_rank_ok_elaborated :
    (elabU (pre108 locks_rank_ok_items)).toOption.isSome = true := by cbv
private def locks_rank_ok_unit := (elabU (pre108 locks_rank_ok_items)).toOption.get locks_rank_ok_elaborated

private theorem locks_rank_ok_count : locks_rank_ok_unit.fns.length = 1 := by cbv

private theorem locks_rank_ok_functions (f : Fin locks_rank_ok_unit.fns.length) :
    (lowerFnAt locks_rank_ok_unit f).toOption.isSome = true ∧
      (fnAt locks_rank_ok_unit f).decreases = none :=
  singleFn_all locks_rank_ok_unit locks_rank_ok_count
    (fun f => (lowerFnAt locks_rank_ok_unit f).toOption.isSome = true ∧
      (fnAt locks_rank_ok_unit f).decreases = none) (by constructor <;> cbv <;> rfl) f

private theorem locks_rank_ok_lowered : lowerStage locks_rank_ok_unit = "OK" :=
  lowerStage_ok locks_rank_ok_unit (by cbv) locks_rank_ok_functions (by cbv)

theorem locks_rank_ok_stufe : stufe locks_rank_ok = "OK" :=
  stufe_phases (source := locks_rank_ok) (characters := locks_rank_ok_characters)
    (tokens := locks_rank_ok_tokens) (items := locks_rank_ok_items) (unit := locks_rank_ok_unit) (answer := "OK")
    (by cbv) locks_rank_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks_rank_ok_tokens) locks_rank_ok_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_rank_ok_items)) locks_rank_ok_elaborated) locks_rank_ok_lowered

def locks_rank_down : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; lock M protects { } rank 1; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L, locks M } { locks M { locks L { k.slots[i].v = 1; } } } }"

private def locks_rank_down_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't',
   ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}',
   ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r',
   'a', 'n', 'k', ' ', '0', ';', ' ', 'l', 'o', 'c', 'k', ' ', 'M', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{',
   ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '1', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':',
   ' ', 'p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' ', 'i', ' ', ':', ' ',
   'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ',
   'w', 'r', 'i', 't', 'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ',',
   ' ', 'l', 'o', 'c', 'k', 's', ' ', 'M', ' ', '}', ' ', '{', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'M', ' ', '{', ' ', 'l',
   'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ',
   '1', ';', ' ', '}', ' ', '}', ' ', '}', ' ', '}']

private def locks_rank_down_tokens : List Token :=
    table_tokens ++ [.wort "lock", .ident "M", .wort "protects", .zeichen "{", .zeichen "}", .wort "rank", .num 1, .zeichen ";"] ++ [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++
    [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L", .zeichen ",", .wort "locks", .ident "M"] ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "M", .zeichen "{"] ++ [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 1 ++ [.zeichen "}", .zeichen "}", .zeichen "}", .zeichen "}", .ende]

private theorem locks_rank_down_lexed : lexL locks_rank_down_characters = .ok locks_rank_down_tokens := by
  change scan false locks_rank_down_characters 251 = .ok locks_rank_down_tokens
  have composed := scan_compose (scan_end 99) (scan_close (locks_rank_down_characters.drop 249) 100)
  have composed := scan_compose composed (scan_close (locks_rank_down_characters.drop 247) 102)
  have composed := scan_compose composed (scan_close (locks_rank_down_characters.drop 245) 104)
  have composed := scan_compose composed (scan_write_one (locks_rank_down_characters.drop 243) 106)
  have composed := scan_compose composed (scan_take (locks_rank_down_characters.drop 225) 120)
  have composed := scan_compose composed (scan_take_second (locks_rank_down_characters.drop 215) 126)
  have composed := scan_compose composed (scan_open (locks_rank_down_characters.drop 205) 132)
  have composed := scan_compose composed (scan_close (locks_rank_down_characters.drop 203) 134)
  have composed := scan_compose composed (scan_two_effects (locks_rank_down_characters.drop 201) 136)
  have composed := scan_compose composed (scan_parameters (locks_rank_down_characters.drop 168) 152)
  have composed := scan_compose composed (scan_writer (locks_rank_down_characters.drop 140) 167)
  have composed := scan_compose composed (scan_second_lock (locks_rank_down_characters.drop 107) 188)
  have composed := scan_compose composed (scan_lock (locks_rank_down_characters.drop 79) 203)
  have composed := scan_compose composed (scan_slot (locks_rank_down_characters.drop 49) 220)
  exact scan_compose composed (scan_prelude (locks_rank_down_characters.drop 29) 235)

private theorem locks_rank_down_parsed :
    (parseTopTief locks_rank_down_tokens).toOption.isSome = true := by cbv
private def locks_rank_down_items := (parseTopTief locks_rank_down_tokens).toOption.get locks_rank_down_parsed

private theorem locks_rank_down_elaborated :
    (elabU (pre108 locks_rank_down_items)).toOption.isSome = true := by cbv
private def locks_rank_down_unit := (elabU (pre108 locks_rank_down_items)).toOption.get locks_rank_down_elaborated

private theorem locks_rank_down_count : locks_rank_down_unit.fns.length = 1 := by cbv

private theorem locks_rank_down_failed (f : Fin locks_rank_down_unit.fns.length) :
    lowerFnAt locks_rank_down_unit f = .error "lower: locks against a held lock of higher or equal rank" :=
  singleFn_all locks_rank_down_unit locks_rank_down_count
    (fun f => lowerFnAt locks_rank_down_unit f = .error "lower: locks against a held lock of higher or equal rank")
    (by cbv <;> rfl) f

private theorem locks_rank_down_lowered : lowerStage locks_rank_down_unit = "lower: lower: locks against a held lock of higher or equal rank" :=
  lowerStage_error locks_rank_down_unit "lower: locks against a held lock of higher or equal rank" (by cbv)
    (fun f => Or.inl (locks_rank_down_failed f))
    ⟨singleFn locks_rank_down_unit locks_rank_down_count, locks_rank_down_failed _⟩

theorem locks_rank_down_stufe : stufe locks_rank_down = "lower: lower: locks against a held lock of higher or equal rank" :=
  stufe_phases (source := locks_rank_down) (characters := locks_rank_down_characters)
    (tokens := locks_rank_down_tokens) (items := locks_rank_down_items) (unit := locks_rank_down_unit) (answer := "lower: lower: locks against a held lock of higher or equal rank")
    (by cbv) locks_rank_down_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks_rank_down_tokens) locks_rank_down_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_rank_down_items)) locks_rank_down_elaborated) locks_rank_down_lowered

def locks_call_needing_it : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn g(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; } } impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { g(k, i); } } }"

private def locks_call_needing_it_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't',
   ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}',
   ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r',
   'a', 'n', 'k', ' ', '0', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'g', '(', 'k', ' ', ':', ' ', 'p', 't', 'r',
   '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' ', 'i', ' ', ':', ' ', 'i', 'n', 'd', 'e',
   'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't',
   'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '}', ' ', '{', ' ',
   'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=',
   ' ', '1', ';', ' ', '}', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':', ' ', 'p', 't',
   'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' ', 'i', ' ', ':', ' ', 'i', 'n', 'd',
   'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i',
   't', 'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '}', ' ', '{',
   ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'g', '(', 'k', ',', ' ', 'i', ')', ';', ' ', '}', ' ', '}', ' ',
   '}']

private def locks_call_needing_it_tokens : List Token :=
    table_tokens ++ [.wort "impl", .wort "fn", .ident "g"] ++ parameter_tokens ++ effect_tokens ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 1 ++ [.zeichen "}", .zeichen "}"] ++
    [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++ effect_tokens ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ [.ident "g", .zeichen "(", .ident "k", .zeichen ",", .ident "i", .zeichen ")", .zeichen ";"] ++ [.zeichen "}", .zeichen "}", .zeichen "}", .ende]

private theorem locks_call_needing_it_lexed : lexL locks_call_needing_it_characters = .ok locks_call_needing_it_tokens := by
  change scan false locks_call_needing_it_characters 314 = .ok locks_call_needing_it_tokens
  have composed := scan_compose (scan_end 120) (scan_close (locks_call_needing_it_characters.drop 312) 121)
  have composed := scan_compose composed (scan_close (locks_call_needing_it_characters.drop 310) 123)
  have composed := scan_compose composed (scan_call (locks_call_needing_it_characters.drop 308) 125)
  have composed := scan_compose composed (scan_take (locks_call_needing_it_characters.drop 299) 134)
  have composed := scan_compose composed (scan_open (locks_call_needing_it_characters.drop 289) 140)
  have composed := scan_compose composed (scan_close (locks_call_needing_it_characters.drop 287) 142)
  have composed := scan_compose composed (scan_effects (locks_call_needing_it_characters.drop 285) 144)
  have composed := scan_compose composed (scan_parameters (locks_call_needing_it_characters.drop 261) 155)
  have composed := scan_compose composed (scan_writer (locks_call_needing_it_characters.drop 233) 170)
  have composed := scan_compose composed (scan_close (locks_call_needing_it_characters.drop 200) 191)
  have composed := scan_compose composed (scan_close (locks_call_needing_it_characters.drop 198) 193)
  have composed := scan_compose composed (scan_write_one (locks_call_needing_it_characters.drop 196) 195)
  have composed := scan_compose composed (scan_take (locks_call_needing_it_characters.drop 178) 209)
  have composed := scan_compose composed (scan_open (locks_call_needing_it_characters.drop 168) 215)
  have composed := scan_compose composed (scan_close (locks_call_needing_it_characters.drop 166) 217)
  have composed := scan_compose composed (scan_effects (locks_call_needing_it_characters.drop 164) 219)
  have composed := scan_compose composed (scan_parameters (locks_call_needing_it_characters.drop 140) 230)
  have composed := scan_compose composed (scan_callee (locks_call_needing_it_characters.drop 112) 245)
  have composed := scan_compose composed (scan_lock (locks_call_needing_it_characters.drop 79) 266)
  have composed := scan_compose composed (scan_slot (locks_call_needing_it_characters.drop 49) 283)
  exact scan_compose composed (scan_prelude (locks_call_needing_it_characters.drop 29) 298)

private theorem locks_call_needing_it_parsed :
    (parseTopTief locks_call_needing_it_tokens).toOption.isSome = true := by cbv
private def locks_call_needing_it_items := (parseTopTief locks_call_needing_it_tokens).toOption.get locks_call_needing_it_parsed

private theorem locks_call_needing_it_elaborated :
    (elabU (pre108 locks_call_needing_it_items)).toOption.isSome = true := by cbv
private def locks_call_needing_it_unit := (elabU (pre108 locks_call_needing_it_items)).toOption.get locks_call_needing_it_elaborated

private theorem locks_call_needing_it_count : locks_call_needing_it_unit.fns.length = 2 := by cbv
private def callee : Fin locks_call_needing_it_unit.fns.length :=
  ⟨0, by rw [locks_call_needing_it_count]; decide⟩
private def caller : Fin locks_call_needing_it_unit.fns.length :=
  ⟨1, by rw [locks_call_needing_it_count]; decide⟩

private theorem callee_ok :
    (lowerFnAt locks_call_needing_it_unit callee).toOption.isSome = true := by cbv <;> rfl
private theorem caller_failed :
    lowerFnAt locks_call_needing_it_unit caller = .error "call: a held lock does not rank below the callee's floor" := by cbv <;> rfl

private theorem locks_call_needing_it_outcomes (f : Fin locks_call_needing_it_unit.fns.length) :
    lowerFnAt locks_call_needing_it_unit f = .error "call: a held lock does not rank below the callee's floor" ∨
      (lowerFnAt locks_call_needing_it_unit f).toOption.isSome = true := by
  have count := locks_call_needing_it_count
  have bound := f.isLt
  rcases (by omega : f.val = 0 ∨ f.val = 1) with zero | one
  · have same : f = callee := Fin.ext zero
    subst f
    exact Or.inr callee_ok
  · have same : f = caller := Fin.ext one
    subst f
    exact Or.inl caller_failed

private theorem locks_call_needing_it_lowered :
    lowerStage locks_call_needing_it_unit = "lower: call: a held lock does not rank below the callee's floor" :=
  lowerStage_error locks_call_needing_it_unit "call: a held lock does not rank below the callee's floor" (by cbv)
    locks_call_needing_it_outcomes ⟨caller, caller_failed⟩

theorem locks_call_needing_it_stufe : stufe locks_call_needing_it = "lower: call: a held lock does not rank below the callee's floor" :=
  stufe_phases (source := locks_call_needing_it) (characters := locks_call_needing_it_characters)
    (tokens := locks_call_needing_it_tokens) (items := locks_call_needing_it_items) (unit := locks_call_needing_it_unit) (answer := "lower: call: a held lock does not rank below the callee's floor")
    (by cbv) locks_call_needing_it_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks_call_needing_it_tokens) locks_call_needing_it_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_call_needing_it_items)) locks_call_needing_it_elaborated) locks_call_needing_it_lowered

end Gabbro.Grammatik.Parser.UebersetzeProben2
