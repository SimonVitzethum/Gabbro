module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben2Basis
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

/-- The elaborated roots and handlers of a source (`none` when a stage stops it). -/
def roots (s : String) : Option (List String × List String) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some (u.roots, u.hands)

def maskFlags (s : String) : Option (List Bool) :=
  match lex s with
  | .error _ => none
  | .ok toks =>
    match parseTopTief toks with
    | .error _ => none
    | .ok items =>
      match elabU (pre108 items) with
      | .error _ => none
      | .ok u => some (u.locks.map (·.masks))

/-- Link the existing stage observer to its actual frontend and lowering certificates. -/
theorem stufe_after {source : String} {characters : List Char} {tokens : List Token}
    {items : List SItemTief} {unit : Uebersetze.UProg} {answer : String}
    (text : source = String.ofList characters) (lexed : lexL characters = .ok tokens)
    (parsed : parseTopTief tokens = .ok items) (elaborated : elabU (pre108 items) = .ok unit)
    (lowered : UebersetzeProben2.lowerStage unit = answer) : stufe source = answer := by
  rw [text]
  unfold stufe
  rw [lex_ofList, lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [elaborated]
  change UebersetzeProben2.lowerStage unit = answer
  exact lowered

theorem stufe_elab_error {source : String} {characters : List Char} {tokens : List Token}
    {items : List SItemTief} {error : String}
    (text : source = String.ofList characters) (lexed : lexL characters = .ok tokens)
    (parsed : parseTopTief tokens = .ok items) (elaborated : elabU (pre108 items) = .error error) :
    stufe source = "elab: " ++ error := by
  rw [text]
  unfold stufe
  rw [lex_ofList, lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [elaborated]

theorem roots_after {source : String} {characters : List Char} {tokens : List Token}
    {items : List SItemTief} {unit : Uebersetze.UProg} {value : List String × List String}
    (text : source = String.ofList characters) (lexed : lexL characters = .ok tokens)
    (parsed : parseTopTief tokens = .ok items) (elaborated : elabU (pre108 items) = .ok unit)
    (observed : (unit.roots, unit.hands) = value) : roots source = some value := by
  rw [text]
  unfold roots
  rw [lex_ofList, lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [elaborated]
  exact congrArg some observed

theorem masks_after {source : String} {characters : List Char} {tokens : List Token}
    {items : List SItemTief} {unit : Uebersetze.UProg} {value : List Bool}
    (text : source = String.ofList characters) (lexed : lexL characters = .ok tokens)
    (parsed : parseTopTief tokens = .ok items) (elaborated : elabU (pre108 items) = .ok unit)
    (observed : unit.locks.map (·.masks) = value) : maskFlags source = some value := by
  rw [text]
  unfold maskFlags
  rw [lex_ofList, lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [elaborated]
  exact congrArg some observed

/-! Exact token snapshots and small equations of the production scanner. -/

def tokens_module : List Token :=
  [.wort "module", .ident "m", .zeichen "{"]

theorem scan3_module (rest : List Char) (n : Nat) :
    scan false (['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' '] ++ rest) (n + 6) =
      tokens_module.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_fn_w : List Token :=
  [.wort "impl", .wort "fn", .wort "w", .zeichen "(", .zeichen ")", .zeichen "{", .zeichen "}"]

theorem scan3_fn_w (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', ')', ' ', '{', ' ', '}', ' '] ++ rest) (n + 12) =
      tokens_fn_w.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_fn_v : List Token :=
  [.wort "impl", .wort "fn", .ident "v", .zeichen "(", .zeichen ")", .zeichen "{", .zeichen "}"]

theorem scan3_fn_v (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'v', '(', ')', ' ', '{', ' ', '}', ' '] ++ rest) (n + 12) =
      tokens_fn_v.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_int_head : List Token :=
  [.wort "impl", .wort "fn", .ident "p", .zeichen "(", .ident "i", .zeichen ":", .wort "u32", .wort "in", .num 0, .zeichen ".."]

theorem scan3_int_head (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'i', ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' '] ++ rest) (n + 18) =
      tokens_int_head.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_int_tail : List Token :=
  [.num 1, .zeichen ")", .zeichen "{", .zeichen "}"]

theorem scan3_int_tail (rest : List Char) (n : Nat) :
    scan false (['1', ')', ' ', '{', ' ', '}', ' '] ++ rest) (n + 7) =
      tokens_int_tail.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_args_tail : List Token :=
  [.num 1, .zeichen ",", .ident "b", .zeichen ":", .wort "bool", .zeichen ")", .zeichen "{", .zeichen "}"]

theorem scan3_args_tail (rest : List Char) (n : Nat) :
    scan false (['1', ',', ' ', 'b', ' ', ':', ' ', 'b', 'o', 'o', 'l', ')', ' ', '{', ' ', '}', ' '] ++ rest) (n + 14) =
      tokens_args_tail.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_ptr_head : List Token :=
  [.wort "impl", .wort "fn", .ident "p", .zeichen "(", .ident "k", .zeichen ":"]

theorem scan3_ptr_head (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'k', ' ', ':', ' '] ++ rest) (n + 10) =
      tokens_ptr_head.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_ptr_tail : List Token :=
  [.wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "r", .zeichen ">", .ident "T", .zeichen ")", .zeichen "{", .zeichen "}"]

theorem scan3_ptr_tail (rest : List Char) (n : Nat) :
    scan false (['p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', '>', ' ', 'T', ')', ' ', '{', ' ', '}', ' '] ++ rest) (n + 15) =
      tokens_ptr_tail.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_entry_e : List Token :=
  [.wort "entry", .ident "e", .wort "vector", .num 1]

theorem scan3_entry_e (rest : List Char) (n : Nat) :
    scan false (['e', 'n', 't', 'r', 'y', ' ', 'e', ' ', 'v', 'e', 'c', 't', 'o', 'r', ' ', '1', ' '] ++ rest) (n + 8) =
      tokens_entry_e.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_entry_f : List Token :=
  [.wort "entry", .ident "f", .wort "vector", .num 1]

theorem scan3_entry_f (rest : List Char) (n : Nat) :
    scan false (['e', 'n', 't', 'r', 'y', ' ', 'f', ' ', 'v', 'e', 'c', 't', 'o', 'r', ' ', '1', ' '] ++ rest) (n + 8) =
      tokens_entry_f.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_via : List Token :=
  [.wort "via", .ident "idt"]

theorem scan3_via (rest : List Char) (n : Nat) :
    scan false (['v', 'i', 'a', ' ', 'i', 'd', 't', ' '] ++ rest) (n + 4) =
      tokens_via.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_arch : List Token :=
  [.wort "arch", .ident "x86_64", .zeichen "{"]

theorem scan3_arch (rest : List Char) (n : Nat) :
    scan false (['a', 'r', 'c', 'h', ' ', 'x', '8', '6', '_', '6', '4', ' ', '{', ' '] ++ rest) (n + 6) =
      tokens_arch.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_regs : List Token :=
  [.wort "regs", .wort "in", .zeichen "{", .zeichen "}", .wort "regs", .wort "out", .zeichen "{", .zeichen "}"]

theorem scan3_regs (rest : List Char) (n : Nat) :
    scan false (['r', 'e', 'g', 's', ' ', 'i', 'n', ' ', '{', ' ', '}', ' ', 'r', 'e', 'g', 's', ' ', 'o', 'u', 't', ' ', '{', ' ', '}', ' '] ++ rest) (n + 16) =
      tokens_regs.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_preserves : List Token :=
  [.wort "preserves", .zeichen "{", .zeichen "}", .wort "clobbers", .zeichen "{", .zeichen "}"]

theorem scan3_preserves (rest : List Char) (n : Nat) :
    scan false (['p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 's', ' ', '{', ' ', '}', ' ', 'c', 'l', 'o', 'b', 'b', 'e', 'r', 's', ' ', '{', ' ', '}', ' '] ++ rest) (n + 12) =
      tokens_preserves.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_stack : List Token :=
  [.wort "stack", .ident "k", .wort "per", .wort "cpu", .wort "nested", .wort "never"]

theorem scan3_stack (rest : List Char) (n : Nat) :
    scan false (['s', 't', 'a', 'c', 'k', ' ', 'k', ' ', 'p', 'e', 'r', ' ', 'c', 'p', 'u', ' ', 'n', 'e', 's', 't', 'e', 'd', ' ', 'n', 'e', 'v', 'e', 'r', ' '] ++ rest) (n + 12) =
      tokens_stack.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_dispatch_w : List Token :=
  [.wort "dispatch", .ident "m", .zeichen "::", .wort "w", .zeichen ";"]

theorem scan3_dispatch_w (rest : List Char) (n : Nat) :
    scan false (['d', 'i', 's', 'p', 'a', 't', 'c', 'h', ' ', 'm', ':', ':', 'w', ';', ' '] ++ rest) (n + 7) =
      tokens_dispatch_w.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_dispatch_v : List Token :=
  [.wort "dispatch", .ident "m", .zeichen "::", .ident "v", .zeichen ";"]

theorem scan3_dispatch_v (rest : List Char) (n : Nat) :
    scan false (['d', 'i', 's', 'p', 'a', 't', 'c', 'h', ' ', 'm', ':', ':', 'v', ';', ' '] ++ rest) (n + 7) =
      tokens_dispatch_v.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_dispatch_p : List Token :=
  [.wort "dispatch", .ident "m", .zeichen "::", .ident "p", .zeichen ";"]

theorem scan3_dispatch_p (rest : List Char) (n : Nat) :
    scan false (['d', 'i', 's', 'p', 'a', 't', 'c', 'h', ' ', 'm', ':', ':', 'p', ';', ' '] ++ rest) (n + 7) =
      tokens_dispatch_p.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_dispatch_unknown : List Token :=
  [.wort "dispatch", .ident "m", .zeichen "::", .ident "nix", .zeichen ";"]

theorem scan3_dispatch_unknown (rest : List Char) (n : Nat) :
    scan false (['d', 'i', 's', 'p', 'a', 't', 'c', 'h', ' ', 'm', ':', ':', 'n', 'i', 'x', ';', ' '] ++ rest) (n + 7) =
      tokens_dispatch_unknown.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_concurrent : List Token :=
  [.wort "concurrent", .zeichen "{"]

theorem scan3_concurrent (rest : List Char) (n : Nat) :
    scan false (['c', 'o', 'n', 'c', 'u', 'r', 'r', 'e', 'n', 't', ' ', '{', ' '] ++ rest) (n + 4) =
      tokens_concurrent.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_roots_two : List Token :=
  [.wort "w", .zeichen ",", .ident "v", .zeichen "}", .zeichen ";"]

theorem scan3_roots_two (rest : List Char) (n : Nat) :
    scan false (['w', ',', ' ', 'v', ' ', '}', ';', ' '] ++ rest) (n + 8) =
      tokens_roots_two.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_root_w : List Token :=
  [.wort "w", .zeichen "}", .zeichen ";"]

theorem scan3_root_w (rest : List Char) (n : Nat) :
    scan false (['w', ' ', '}', ';', ' '] ++ rest) (n + 5) =
      tokens_root_w.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_root_p : List Token :=
  [.ident "p", .zeichen "}", .zeichen ";"]

theorem scan3_root_p (rest : List Char) (n : Nat) :
    scan false (['p', ' ', '}', ';', ' '] ++ rest) (n + 5) =
      tokens_root_p.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_root_unknown : List Token :=
  [.ident "nix", .zeichen "}", .zeichen ";"]

theorem scan3_root_unknown (rest : List Char) (n : Nat) :
    scan false (['n', 'i', 'x', ' ', '}', ';', ' '] ++ rest) (n + 5) =
      tokens_root_unknown.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_start_args : List Token :=
  [.ident "p", .zeichen "(", .num 1, .zeichen ",", .wort "true", .zeichen ")", .zeichen "}", .zeichen ";"]

theorem scan3_start_args (rest : List Char) (n : Nat) :
    scan false (['p', '(', '1', ',', ' ', 't', 'r', 'u', 'e', ')', ' ', '}', ';', ' '] ++ rest) (n + 11) =
      tokens_start_args.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_start_range : List Token :=
  [.ident "p", .zeichen "(", .num 2, .zeichen ")", .zeichen "}", .zeichen ";"]

theorem scan3_start_range (rest : List Char) (n : Nat) :
    scan false (['p', '(', '2', ')', ' ', '}', ';', ' '] ++ rest) (n + 8) =
      tokens_start_range.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_start_ptr_t : List Token :=
  [.ident "p", .zeichen "(", .zeichen "&", .ident "T", .zeichen ")", .zeichen "}", .zeichen ";"]

theorem scan3_start_ptr_t (rest : List Char) (n : Nat) :
    scan false (['p', '(', '&', 'T', ')', ' ', '}', ';', ' '] ++ rest) (n + 9) =
      tokens_start_ptr_t.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_start_ptr_u : List Token :=
  [.ident "p", .zeichen "(", .zeichen "&", .ident "U", .zeichen ")", .zeichen "}", .zeichen ";"]

theorem scan3_start_ptr_u (rest : List Char) (n : Nat) :
    scan false (['p', '(', '&', 'U', ')', ' ', '}', ';', ' '] ++ rest) (n + 9) =
      tokens_start_ptr_u.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_table_u : List Token :=
  [.wort "table", .ident "U", .wort "count", .num 2, .zeichen "{"]

theorem scan3_table_u (rest : List Char) (n : Nat) :
    scan false (['t', 'a', 'b', 'l', 'e', ' ', 'U', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', '{', ' '] ++ rest) (n + 10) =
      tokens_table_u.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_lock_head : List Token :=
  [.wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "T", .zeichen "}", .wort "rank", .num 0]

theorem scan3_lock_head (rest : List Char) (n : Nat) :
    scan false (['l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '0', ' '] ++ rest) (n + 16) =
      tokens_lock_head.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_mask_irqs : List Token :=
  [.wort "masks", .ident "irqs", .zeichen ";"]

theorem scan3_mask_irqs (rest : List Char) (n : Nat) :
    scan false (['m', 'a', 's', 'k', 's', ' ', 'i', 'r', 'q', 's', ';', ' '] ++ rest) (n + 5) =
      tokens_mask_irqs.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_mask_other : List Token :=
  [.wort "masks", .ident "nmi", .zeichen ";"]

theorem scan3_mask_other (rest : List Char) (n : Nat) :
    scan false (['m', 'a', 's', 'k', 's', ' ', 'n', 'm', 'i', ';', ' '] ++ rest) (n + 5) =
      tokens_mask_other.foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

def tokens_prelude : List Token :=
  [.wort "module", .ident "m", .zeichen "{", .wort "table", .ident "T", .wort "count", .num 2, .zeichen "{"]

def tokens_slot : List Token :=
  [.wort "slot", .zeichen "{", .ident "v", .zeichen ":", .wort "u32", .zeichen ",", .zeichen "}", .zeichen "}"]

def tokens_lock : List Token :=
  [.wort "lock", .ident "L", .wort "protects", .zeichen "{", .ident "T", .zeichen "}", .wort "rank", .num 0, .zeichen ";"]

def tokens_writer : List Token :=
  [.wort "impl", .wort "fn", .wort "w", .zeichen "(", .ident "k", .zeichen ":", .wort "ptr", .zeichen "<", .wort "normal", .zeichen ",", .wort "rw", .zeichen ">", .ident "T", .zeichen ","]

def tokens_parameters : List Token :=
  [.ident "i", .zeichen ":", .wort "index", .wort "into", .ident "T", .zeichen ")", .wort "effects", .zeichen "{"]

def tokens_effects : List Token :=
  [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L"]

def tokens_open : List Token :=
  [.zeichen "{"]

def tokens_take : List Token :=
  [.wort "locks", .ident "L", .zeichen "{"]

def tokens_write_one : List Token :=
  [.ident "k", .zeichen ".", .wort "slots", .zeichen "[", .ident "i", .zeichen "]", .zeichen ".", .ident "v", .zeichen "=", .num 1, .zeichen ";"]

def tokens_close : List Token :=
  [.zeichen "}"]

end Gabbro.Grammatik.Parser.UebersetzeProben3
