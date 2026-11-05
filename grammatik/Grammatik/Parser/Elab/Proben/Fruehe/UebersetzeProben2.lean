/-
  File:      Grammatik/Parser/UebersetzeProben2.lean
  Subject:   Sieve (a), parser lane: witnesses and planted defects of walls 6 (`locks` blocks) and 7
             (`entry` roots). A second file because the kernel probes of one file share one memory
             budget (measured 2026-09-30: the first file alone passes 7 GB with these twelve added).
-/
module
public import Grammatik.Parser.Elab.UebersetzePipeline
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

/-- The stage of `uebersetzeAllg` that stops a source (`OK` when none does). -/
def stufe (s : String) : String :=
  match lex s with
  | .error _ => "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => "parse: " ++ e
    | .ok items =>
      match elabU (pre108 items) with
      | .error e => "elab: " ++ e
      | .ok u =>
        match lowerAllg u with
        | .error e => "lower: " ++ e
        | .ok _ => "OK"

/-- Link the actual phases without reducing the UTF-8 decoder inside later proofs. -/
private theorem stufe_phases {source : String} {characters : List Char} {tokens : List Token}
    {items : List SItemTief} {unit : Uebersetze.UProg} {answer : String}
    (text : source = String.ofList characters) (lexed : lexL characters = .ok tokens)
    (parsed : parseTopTief tokens = .ok items) (elaborated : elabU (pre108 items) = .ok unit)
    (lowered : (match lowerAllg unit with
      | .error error => "lower: " ++ error
      | .ok _ => "OK") = answer) : stufe source = answer := by
  rw [text]
  unfold stufe
  rw [lex_ofList, lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [elaborated]
  exact lowered

/-- The existing sequence selector takes one level only when its source run needs it. -/
private theorem seq_succ (u : Uebersetze.UProg) (caller : Fin u.fns.length) (n : Nat)
    {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (pe : AtTop u caller Λ) (ss : List UStmt) :
    lowSeqL (l := l) u caller Γ fn (n + 1) Λ pe ss =
      lowSeqStep u caller (lowStufe u caller n) Γ fn Λ pe ss := rfl

-- Keep the canonical fuel record symbolic: evaluate its selected operation, not all 100000 levels.
-- These local proof rules are equations of the unchanged producer, not another lowering path.
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL
attribute [local cbv_eval] seq_succ lowStructL_succ lowStufe_seq lowStufe_struct

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

private theorem locks1_ok_lexed :
    (lexL locks1_ok_characters).toOption.isSome = true := by cbv
private def locks1_ok_tokens := (lexL locks1_ok_characters).toOption.get locks1_ok_lexed

private theorem locks1_ok_parsed :
    (parseTopTief locks1_ok_tokens).toOption.isSome = true := by cbv
private def locks1_ok_items := (parseTopTief locks1_ok_tokens).toOption.get locks1_ok_parsed

private theorem locks1_ok_elaborated :
    (elabU (pre108 locks1_ok_items)).toOption.isSome = true := by cbv
private def locks1_ok_unit := (elabU (pre108 locks1_ok_items)).toOption.get locks1_ok_elaborated

private theorem locks1_ok_lowered :
    (match lowerAllg locks1_ok_unit with
      | .error error => "lower: " ++ error
      | .ok _ => "OK") = "OK" := by cbv

theorem locks1_ok_stufe : stufe locks1_ok = "OK" :=
  stufe_phases (characters := locks1_ok_characters) (by cbv)
    (except_ok_get locks1_ok_lexed) (except_ok_get locks1_ok_parsed)
    (except_ok_get locks1_ok_elaborated) locks1_ok_lowered

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

private theorem locks2_ok_lexed :
    (lexL locks2_ok_characters).toOption.isSome = true := by cbv
private def locks2_ok_tokens := (lexL locks2_ok_characters).toOption.get locks2_ok_lexed

private theorem locks2_ok_parsed :
    (parseTopTief locks2_ok_tokens).toOption.isSome = true := by cbv
private def locks2_ok_items := (parseTopTief locks2_ok_tokens).toOption.get locks2_ok_parsed

private theorem locks2_ok_elaborated :
    (elabU (pre108 locks2_ok_items)).toOption.isSome = true := by cbv
private def locks2_ok_unit := (elabU (pre108 locks2_ok_items)).toOption.get locks2_ok_elaborated

private theorem locks2_ok_lowered :
    (match lowerAllg locks2_ok_unit with
      | .error error => "lower: " ++ error
      | .ok _ => "OK") = "OK" := by cbv

theorem locks2_ok_stufe : stufe locks2_ok = "OK" :=
  stufe_phases (characters := locks2_ok_characters) (by cbv)
    (except_ok_get locks2_ok_lexed) (except_ok_get locks2_ok_parsed)
    (except_ok_get locks2_ok_elaborated) locks2_ok_lowered

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

private theorem locks_nested_same_lexed :
    (lexL locks_nested_same_characters).toOption.isSome = true := by cbv
private def locks_nested_same_tokens := (lexL locks_nested_same_characters).toOption.get locks_nested_same_lexed

private theorem locks_nested_same_parsed :
    (parseTopTief locks_nested_same_tokens).toOption.isSome = true := by cbv
private def locks_nested_same_items := (parseTopTief locks_nested_same_tokens).toOption.get locks_nested_same_parsed

private theorem locks_nested_same_elaborated :
    (elabU (pre108 locks_nested_same_items)).toOption.isSome = true := by cbv
private def locks_nested_same_unit := (elabU (pre108 locks_nested_same_items)).toOption.get locks_nested_same_elaborated

private theorem locks_nested_same_lowered :
    (match lowerAllg locks_nested_same_unit with
      | .error error => "lower: " ++ error
      | .ok _ => "OK") = "lower: lower: locks against a held lock of higher or equal rank" := by cbv

theorem locks_nested_same_stufe : stufe locks_nested_same = "lower: lower: locks against a held lock of higher or equal rank" :=
  stufe_phases (characters := locks_nested_same_characters) (by cbv)
    (except_ok_get locks_nested_same_lexed) (except_ok_get locks_nested_same_parsed)
    (except_ok_get locks_nested_same_elaborated) locks_nested_same_lowered

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

private theorem locks_rank_ok_lexed :
    (lexL locks_rank_ok_characters).toOption.isSome = true := by cbv
private def locks_rank_ok_tokens := (lexL locks_rank_ok_characters).toOption.get locks_rank_ok_lexed

private theorem locks_rank_ok_parsed :
    (parseTopTief locks_rank_ok_tokens).toOption.isSome = true := by cbv
private def locks_rank_ok_items := (parseTopTief locks_rank_ok_tokens).toOption.get locks_rank_ok_parsed

private theorem locks_rank_ok_elaborated :
    (elabU (pre108 locks_rank_ok_items)).toOption.isSome = true := by cbv
private def locks_rank_ok_unit := (elabU (pre108 locks_rank_ok_items)).toOption.get locks_rank_ok_elaborated

private theorem locks_rank_ok_lowered :
    (match lowerAllg locks_rank_ok_unit with
      | .error error => "lower: " ++ error
      | .ok _ => "OK") = "OK" := by cbv

theorem locks_rank_ok_stufe : stufe locks_rank_ok = "OK" :=
  stufe_phases (characters := locks_rank_ok_characters) (by cbv)
    (except_ok_get locks_rank_ok_lexed) (except_ok_get locks_rank_ok_parsed)
    (except_ok_get locks_rank_ok_elaborated) locks_rank_ok_lowered

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

private theorem locks_rank_down_lexed :
    (lexL locks_rank_down_characters).toOption.isSome = true := by cbv
private def locks_rank_down_tokens := (lexL locks_rank_down_characters).toOption.get locks_rank_down_lexed

private theorem locks_rank_down_parsed :
    (parseTopTief locks_rank_down_tokens).toOption.isSome = true := by cbv
private def locks_rank_down_items := (parseTopTief locks_rank_down_tokens).toOption.get locks_rank_down_parsed

private theorem locks_rank_down_elaborated :
    (elabU (pre108 locks_rank_down_items)).toOption.isSome = true := by cbv
private def locks_rank_down_unit := (elabU (pre108 locks_rank_down_items)).toOption.get locks_rank_down_elaborated

private theorem locks_rank_down_lowered :
    (match lowerAllg locks_rank_down_unit with
      | .error error => "lower: " ++ error
      | .ok _ => "OK") = "lower: lower: locks against a held lock of higher or equal rank" := by cbv

theorem locks_rank_down_stufe : stufe locks_rank_down = "lower: lower: locks against a held lock of higher or equal rank" :=
  stufe_phases (characters := locks_rank_down_characters) (by cbv)
    (except_ok_get locks_rank_down_lexed) (except_ok_get locks_rank_down_parsed)
    (except_ok_get locks_rank_down_elaborated) locks_rank_down_lowered

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

private theorem locks_call_needing_it_lexed :
    (lexL locks_call_needing_it_characters).toOption.isSome = true := by cbv
private def locks_call_needing_it_tokens := (lexL locks_call_needing_it_characters).toOption.get locks_call_needing_it_lexed

private theorem locks_call_needing_it_parsed :
    (parseTopTief locks_call_needing_it_tokens).toOption.isSome = true := by cbv
private def locks_call_needing_it_items := (parseTopTief locks_call_needing_it_tokens).toOption.get locks_call_needing_it_parsed

private theorem locks_call_needing_it_elaborated :
    (elabU (pre108 locks_call_needing_it_items)).toOption.isSome = true := by cbv
private def locks_call_needing_it_unit := (elabU (pre108 locks_call_needing_it_items)).toOption.get locks_call_needing_it_elaborated

private theorem locks_call_needing_it_lowered :
    (match lowerAllg locks_call_needing_it_unit with
      | .error error => "lower: " ++ error
      | .ok _ => "OK") = "lower: call: a held lock does not rank below the callee's floor" := by cbv

theorem locks_call_needing_it_stufe : stufe locks_call_needing_it = "lower: call: a held lock does not rank below the callee's floor" :=
  stufe_phases (characters := locks_call_needing_it_characters) (by cbv)
    (except_ok_get locks_call_needing_it_lexed) (except_ok_get locks_call_needing_it_parsed)
    (except_ok_get locks_call_needing_it_elaborated) locks_call_needing_it_lowered

end Gabbro.Grammatik.Parser.UebersetzeProben2
