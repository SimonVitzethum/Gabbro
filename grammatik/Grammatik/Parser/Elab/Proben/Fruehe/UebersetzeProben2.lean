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

/-- Small equations of the existing scanner, with an unevaluated continuation.
    Each whitespace-terminated fragment consumes exactly its tokens and spaces. -/
private theorem scan_prelude (rest : List Char) (n : Nat) :
    scan false (['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', '{', ' '] ++ rest) (n + 16) =
    [.wort "module", .ident "m", .zeichen "{", .wort "table", .ident "T", .wort "count", .num 2, .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_slot (rest : List Char) (n : Nat) :
    scan false (['s', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}', ' '] ++ rest) (n + 15) =
    [.wort "slot", .zeichen "{", .ident "v", .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}", .zeichen "}"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_lock (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '0', ';', ' '] ++ rest) (n + 17) =
    [.wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "T", .zeichen "}", .wort "rank", .num 0, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_second_lock (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', ' ', 'M', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '1', ';', ' '] ++ rest) (n + 15) =
    [.wort "lock", .ident "M", .wort "protects", .zeichen "{", .zeichen "}", .wort "rank", .num 1, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_writer (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':', ' ', 'p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' '] ++ rest) (n + 21) =
    [.wort "impl", .wort "fn", .wort "w", .zeichen "(", .ident "k", .zeichen ":", .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "rw", .zeichen ">", .ident "T", .zeichen ","].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_callee (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'g', '(', 'k', ' ', ':', ' ', 'p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' '] ++ rest) (n + 21) =
    [.wort "impl", .wort "fn", .ident "g", .zeichen "(", .ident "k", .zeichen ":", .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "rw", .zeichen ">", .ident "T", .zeichen ","].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_parameters (rest : List Char) (n : Nat) :
    scan false (['i', ' ', ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' '] ++ rest) (n + 15) =
    [.ident "i", .zeichen ":", .wort "index", .wort "into", .ident "T", .zeichen ")", .wort "effects", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_effects (rest : List Char) (n : Nat) :
    scan false (['w', 'r', 'i', 't', 'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' '] ++ rest) (n + 11) =
    [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_two_effects (rest : List Char) (n : Nat) :
    scan false (['w', 'r', 'i', 't', 'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'M', ' '] ++ rest) (n + 16) =
    [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L", .zeichen ",", .wort "locks", .ident "M"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_open (rest : List Char) (n : Nat) :
    scan false (['{', ' '] ++ rest) (n + 2) =
    [.zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_take (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' '] ++ rest) (n + 6) =
    [.wort "locks", .ident "L", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_take_second (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', 's', ' ', 'M', ' ', '{', ' '] ++ rest) (n + 6) =
    [.wort "locks", .ident "M", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_write_one (rest : List Char) (n : Nat) :
    scan false (['k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '1', ';', ' '] ++ rest) (n + 14) =
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num 1, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_write_two (rest : List Char) (n : Nat) :
    scan false (['k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '2', ';', ' '] ++ rest) (n + 14) =
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num 2, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_write_three (rest : List Char) (n : Nat) :
    scan false (['k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '3', ';', ' '] ++ rest) (n + 14) =
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num 3, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_close (rest : List Char) (n : Nat) :
    scan false (['}', ' '] ++ rest) (n + 2) =
    [.zeichen "}"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_call (rest : List Char) (n : Nat) :
    scan false (['g', '(', 'k', ',', ' ', 'i', ')', ';', ' '] ++ rest) (n + 9) =
    [.ident "g", .zeichen "(", .ident "k", .zeichen ",", .ident "i", .zeichen ")", .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem scan_end (n : Nat) :
    scan false ['}'] (n + 1) = .ok [.zeichen "}", .ende] := by cbv

private theorem token_maps (prefix : List Token) (result : Except LexFehler (List Token)) :
    prefix.foldr (fun t answer => Except.map (t :: ·) answer) result =
      Except.map (prefix ++ ·) result := by
  induction prefix with
  | nil => cases result <;> rfl
  | cons t ts ih =>
    simp only [List.foldr, ih]
    cases result <;> rfl

/-- Canonical token snapshots shared by the six unchanged source texts. -/
private def table_tokens : List Token :=
    [.wort "module", .ident "m", .zeichen "{", .wort "table", .ident "T", .wort "count", .num 2, .zeichen "{", .wort "slot", .zeichen "{", .ident "v", .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}", .zeichen "}", .wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "T", .zeichen "}", .wort "rank", .num 0, .zeichen ";"]

private def parameter_tokens : List Token :=
    [.zeichen "(", .ident "k", .zeichen ":", .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "rw", .zeichen ">", .ident "T", .zeichen ",", .ident "i", .zeichen ":", .wort "index", .wort "into", .ident "T", .zeichen ")", .wort "effects", .zeichen "{"]

private def effect_tokens : List Token := [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L"]

private def write_tokens (n : Nat) : List Token :=
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num n, .zeichen ";"]

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
  simp only [locks1_ok_characters, locks1_ok_tokens, table_tokens, parameter_tokens,
    effect_tokens, write_tokens, scan_prelude, scan_slot, scan_lock, scan_second_lock, scan_writer, scan_callee,
    scan_parameters, scan_effects, scan_two_effects, scan_open, scan_take, scan_take_second,
    scan_write_one, scan_write_two, scan_write_three, scan_close, scan_call, scan_end, token_maps, Except.map]

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
  simp only [locks2_ok_characters, locks2_ok_tokens, table_tokens, parameter_tokens,
    effect_tokens, write_tokens, scan_prelude, scan_slot, scan_lock, scan_second_lock, scan_writer, scan_callee,
    scan_parameters, scan_effects, scan_two_effects, scan_open, scan_take, scan_take_second,
    scan_write_one, scan_write_two, scan_write_three, scan_close, scan_call, scan_end, token_maps, Except.map]

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
  simp only [locks_nested_same_characters, locks_nested_same_tokens, table_tokens, parameter_tokens,
    effect_tokens, write_tokens, scan_prelude, scan_slot, scan_lock, scan_second_lock, scan_writer, scan_callee,
    scan_parameters, scan_effects, scan_two_effects, scan_open, scan_take, scan_take_second,
    scan_write_one, scan_write_two, scan_write_three, scan_close, scan_call, scan_end, token_maps, Except.map]

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
  simp only [locks_rank_ok_characters, locks_rank_ok_tokens, table_tokens, parameter_tokens,
    effect_tokens, write_tokens, scan_prelude, scan_slot, scan_lock, scan_second_lock, scan_writer, scan_callee,
    scan_parameters, scan_effects, scan_two_effects, scan_open, scan_take, scan_take_second,
    scan_write_one, scan_write_two, scan_write_three, scan_close, scan_call, scan_end, token_maps, Except.map]

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
  simp only [locks_rank_down_characters, locks_rank_down_tokens, table_tokens, parameter_tokens,
    effect_tokens, write_tokens, scan_prelude, scan_slot, scan_lock, scan_second_lock, scan_writer, scan_callee,
    scan_parameters, scan_effects, scan_two_effects, scan_open, scan_take, scan_take_second,
    scan_write_one, scan_write_two, scan_write_three, scan_close, scan_call, scan_end, token_maps, Except.map]

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
  simp only [locks_call_needing_it_characters, locks_call_needing_it_tokens, table_tokens, parameter_tokens,
    effect_tokens, write_tokens, scan_prelude, scan_slot, scan_lock, scan_second_lock, scan_writer, scan_callee,
    scan_parameters, scan_effects, scan_two_effects, scan_open, scan_take, scan_take_second,
    scan_write_one, scan_write_two, scan_write_three, scan_close, scan_call, scan_end, token_maps, Except.map]

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
  stufe_phases (source := locks_call_needing_it) (characters := locks_call_needing_it_characters)
    (tokens := locks_call_needing_it_tokens) (items := locks_call_needing_it_items) (unit := locks_call_needing_it_unit) (answer := "lower: call: a held lock does not rank below the callee's floor")
    (by cbv) locks_call_needing_it_lexed
    (except_ok_get (ε := String) (α := List SItemTief) (x := parseTopTief locks_call_needing_it_tokens) locks_call_needing_it_parsed)
    (except_ok_get (ε := String) (α := Uebersetze.UProg)
      (x := elabU (pre108 locks_call_needing_it_items)) locks_call_needing_it_elaborated) locks_call_needing_it_lowered

end Gabbro.Grammatik.Parser.UebersetzeProben2
