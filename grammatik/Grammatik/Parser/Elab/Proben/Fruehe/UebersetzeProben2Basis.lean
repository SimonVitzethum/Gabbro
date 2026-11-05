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
theorem stufe_phases {source : String} {characters : List Char} {tokens : List Token}
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
theorem seq_succ (u : Uebersetze.UProg) (caller : Fin u.fns.length) (n : Nat)
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
theorem scan_prelude (rest : List Char) (n : Nat) :
    scan false (['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', '{', ' '] ++ rest) (n + 16) =
    [.wort "module", .ident "m", .zeichen "{", .wort "table", .ident "T", .wort "count", .num 2, .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_slot (rest : List Char) (n : Nat) :
    scan false (['s', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}', ' '] ++ rest) (n + 15) =
    [.wort "slot", .zeichen "{", .ident "v", .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}", .zeichen "}"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_lock (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '0', ';', ' '] ++ rest) (n + 17) =
    [.wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "T", .zeichen "}", .wort "rank", .num 0, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_second_lock (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', ' ', 'M', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '1', ';', ' '] ++ rest) (n + 15) =
    [.wort "lock", .ident "M", .wort "protects", .zeichen "{", .zeichen "}", .wort "rank", .num 1, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_writer (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':', ' ', 'p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' '] ++ rest) (n + 21) =
    [.wort "impl", .wort "fn", .wort "w", .zeichen "(", .ident "k", .zeichen ":", .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "rw", .zeichen ">", .ident "T", .zeichen ","].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_callee (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'g', '(', 'k', ' ', ':', ' ', 'p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' '] ++ rest) (n + 21) =
    [.wort "impl", .wort "fn", .ident "g", .zeichen "(", .ident "k", .zeichen ":", .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "rw", .zeichen ">", .ident "T", .zeichen ","].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_parameters (rest : List Char) (n : Nat) :
    scan false (['i', ' ', ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' '] ++ rest) (n + 15) =
    [.ident "i", .zeichen ":", .wort "index", .wort "into", .ident "T", .zeichen ")", .wort "effects", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_effects (rest : List Char) (n : Nat) :
    scan false (['w', 'r', 'i', 't', 'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' '] ++ rest) (n + 11) =
    [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_two_effects (rest : List Char) (n : Nat) :
    scan false (['w', 'r', 'i', 't', 'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'M', ' '] ++ rest) (n + 16) =
    [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L", .zeichen ",", .wort "locks", .ident "M"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_open (rest : List Char) (n : Nat) :
    scan false (['{', ' '] ++ rest) (n + 2) =
    [.zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_take (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' '] ++ rest) (n + 6) =
    [.wort "locks", .ident "L", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_take_second (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', 's', ' ', 'M', ' ', '{', ' '] ++ rest) (n + 6) =
    [.wort "locks", .ident "M", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_write_one (rest : List Char) (n : Nat) :
    scan false (['k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '1', ';', ' '] ++ rest) (n + 14) =
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num 1, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_write_two (rest : List Char) (n : Nat) :
    scan false (['k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '2', ';', ' '] ++ rest) (n + 14) =
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num 2, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_write_three (rest : List Char) (n : Nat) :
    scan false (['k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '3', ';', ' '] ++ rest) (n + 14) =
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num 3, .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_close (rest : List Char) (n : Nat) :
    scan false (['}', ' '] ++ rest) (n + 2) =
    [.zeichen "}"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_call (rest : List Char) (n : Nat) :
    scan false (['g', '(', 'k', ',', ' ', 'i', ')', ';', ' '] ++ rest) (n + 9) =
    [.ident "g", .zeichen "(", .ident "k", .zeichen ",", .ident "i", .zeichen ")", .zeichen ";"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

theorem scan_end (n : Nat) :
    scan false ['}'] (n + 1) = .ok [.zeichen "}", .ende] := by cbv

theorem token_maps (tokens : List Token) (result : Except LexFehler (List Token)) :
    tokens.foldr (fun t answer => Except.map (t :: ·) answer) result =
      Except.map (tokens ++ ·) result := by
  induction tokens with
  | nil => cases result <;> rfl
  | cons t ts ih =>
    simp only [List.foldr, ih]
    cases result <;> rfl

/-- Canonical token snapshots shared by the six unchanged source texts. -/
def table_tokens : List Token :=
    [.wort "module", .ident "m", .zeichen "{", .wort "table", .ident "T", .wort "count", .num 2, .zeichen "{", .wort "slot", .zeichen "{", .ident "v", .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}", .zeichen "}", .wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "T", .zeichen "}", .wort "rank", .num 0, .zeichen ";"]

def parameter_tokens : List Token :=
    [.zeichen "(", .ident "k", .zeichen ":", .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "rw", .zeichen ">", .ident "T", .zeichen ",", .ident "i", .zeichen ":", .wort "index", .wort "into", .ident "T", .zeichen ")", .wort "effects", .zeichen "{"]

def effect_tokens : List Token := [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L"]

def write_tokens (n : Nat) : List Token :=
    [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num n, .zeichen ";"]

end Gabbro.Grammatik.Parser.UebersetzeProben2
