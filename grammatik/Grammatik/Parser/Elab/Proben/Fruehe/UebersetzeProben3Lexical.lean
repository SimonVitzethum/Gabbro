module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3Basis
@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeProben3
open Gabbro.Grammatik Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-- Compose actual scanner results with fully instantiated source suffixes. -/
private theorem scan_compose {source rest : List Char} {fuel remaining : Nat}
    {emitted tokens : List Token} (tail : scan false rest remaining = .ok tokens)
    (head : scan false source fuel = emitted.foldr (fun t result => Except.map (t :: ·) result) (scan false rest remaining)) :
    scan false source fuel = .ok (emitted ++ tokens) := by
  rw [tail, UebersetzeProben2.token_maps] at head
  exact head

def entry1_ok : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"

def entry1_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', ')',
   ' ', '{', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'i', ' ', ':', ' ', 'u', '3', '2',
   ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ')', ' ', '{', ' ', '}', ' ', 'e', 'n', 't', 'r', 'y', ' ',
   'e', ' ', 'v', 'e', 'c', 't', 'o', 'r', ' ', '1', ' ', 'a', 'r', 'c', 'h', ' ', 'x', '8', '6', '_', '6', '4',
   ' ', '{', ' ', 'r', 'e', 'g', 's', ' ', 'i', 'n', ' ', '{', ' ', '}', ' ', 'r', 'e', 'g', 's', ' ', 'o', 'u',
   't', ' ', '{', ' ', '}', ' ', 'p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 's', ' ', '{', ' ', '}', ' ', 'c', 'l',
   'o', 'b', 'b', 'e', 'r', 's', ' ', '{', ' ', '}', ' ', 's', 't', 'a', 'c', 'k', ' ', 'k', ' ', 'p', 'e', 'r',
   ' ', 'c', 'p', 'u', ' ', 'n', 'e', 's', 't', 'e', 'd', ' ', 'n', 'e', 'v', 'e', 'r', ' ', 'd', 'i', 's', 'p',
   'a', 't', 'c', 'h', ' ', 'm', ':', ':', 'w', ';', ' ', '}', ' ', '}']

def entry1_ok_tokens : List Token :=
  tokens_module ++ tokens_fn_w ++ tokens_int_head ++ tokens_int_tail ++ tokens_entry_e ++ tokens_arch ++
   tokens_regs ++ tokens_preserves ++ tokens_stack ++ tokens_dispatch_w ++ tokens_close ++ [.zeichen "}", .ende]

theorem entry1_ok_lexed : lexL entry1_ok_characters = .ok entry1_ok_tokens := by
  change scan false entry1_ok_characters 191 = .ok entry1_ok_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 84) (UebersetzeProben2.scan_close (entry1_ok_characters.drop 189) 85)
  have composed := scan_compose composed (scan3_dispatch_w (entry1_ok_characters.drop 187) 87)
  have composed := scan_compose composed (scan3_stack (entry1_ok_characters.drop 172) 94)
  have composed := scan_compose composed (scan3_preserves (entry1_ok_characters.drop 143) 106)
  have composed := scan_compose composed (scan3_regs (entry1_ok_characters.drop 116) 118)
  have composed := scan_compose composed (scan3_arch (entry1_ok_characters.drop 91) 134)
  have composed := scan_compose composed (scan3_entry_e (entry1_ok_characters.drop 77) 140)
  have composed := scan_compose composed (scan3_int_tail (entry1_ok_characters.drop 60) 148)
  have composed := scan_compose composed (scan3_int_head (entry1_ok_characters.drop 53) 155)
  have composed := scan_compose composed (scan3_fn_w (entry1_ok_characters.drop 27) 173)
  have complete := scan_compose composed (scan3_module (entry1_ok_characters.drop 11) 185)
  exact complete

def entry_two_ok : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } entry f vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"

def entry_two_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', ')',
   ' ', '{', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'i', ' ', ':', ' ', 'u', '3', '2',
   ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ')', ' ', '{', ' ', '}', ' ', 'e', 'n', 't', 'r', 'y', ' ',
   'e', ' ', 'v', 'e', 'c', 't', 'o', 'r', ' ', '1', ' ', 'a', 'r', 'c', 'h', ' ', 'x', '8', '6', '_', '6', '4',
   ' ', '{', ' ', 'r', 'e', 'g', 's', ' ', 'i', 'n', ' ', '{', ' ', '}', ' ', 'r', 'e', 'g', 's', ' ', 'o', 'u',
   't', ' ', '{', ' ', '}', ' ', 'p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 's', ' ', '{', ' ', '}', ' ', 'c', 'l',
   'o', 'b', 'b', 'e', 'r', 's', ' ', '{', ' ', '}', ' ', 's', 't', 'a', 'c', 'k', ' ', 'k', ' ', 'p', 'e', 'r',
   ' ', 'c', 'p', 'u', ' ', 'n', 'e', 's', 't', 'e', 'd', ' ', 'n', 'e', 'v', 'e', 'r', ' ', 'd', 'i', 's', 'p',
   'a', 't', 'c', 'h', ' ', 'm', ':', ':', 'w', ';', ' ', '}', ' ', 'e', 'n', 't', 'r', 'y', ' ', 'f', ' ', 'v',
   'e', 'c', 't', 'o', 'r', ' ', '1', ' ', 'a', 'r', 'c', 'h', ' ', 'x', '8', '6', '_', '6', '4', ' ', '{', ' ',
   'r', 'e', 'g', 's', ' ', 'i', 'n', ' ', '{', ' ', '}', ' ', 'r', 'e', 'g', 's', ' ', 'o', 'u', 't', ' ', '{',
   ' ', '}', ' ', 'p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 's', ' ', '{', ' ', '}', ' ', 'c', 'l', 'o', 'b', 'b',
   'e', 'r', 's', ' ', '{', ' ', '}', ' ', 's', 't', 'a', 'c', 'k', ' ', 'k', ' ', 'p', 'e', 'r', ' ', 'c', 'p',
   'u', ' ', 'n', 'e', 's', 't', 'e', 'd', ' ', 'n', 'e', 'v', 'e', 'r', ' ', 'd', 'i', 's', 'p', 'a', 't', 'c',
   'h', ' ', 'm', ':', ':', 'w', ';', ' ', '}', ' ', '}']

def entry_two_ok_tokens : List Token :=
  tokens_module ++ tokens_fn_w ++ tokens_int_head ++ tokens_int_tail ++ tokens_entry_e ++ tokens_arch ++
   tokens_regs ++ tokens_preserves ++ tokens_stack ++ tokens_dispatch_w ++ tokens_close ++ tokens_entry_f ++
   tokens_arch ++ tokens_regs ++ tokens_preserves ++ tokens_stack ++ tokens_dispatch_w ++ tokens_close ++
   [.zeichen "}", .ende]

theorem entry_two_ok_lexed : lexL entry_two_ok_characters = .ok entry_two_ok_tokens := by
  change scan false entry_two_ok_characters 320 = .ok entry_two_ok_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 150) (UebersetzeProben2.scan_close (entry_two_ok_characters.drop 318) 151)
  have composed := scan_compose composed (scan3_dispatch_w (entry_two_ok_characters.drop 316) 153)
  have composed := scan_compose composed (scan3_stack (entry_two_ok_characters.drop 301) 160)
  have composed := scan_compose composed (scan3_preserves (entry_two_ok_characters.drop 272) 172)
  have composed := scan_compose composed (scan3_regs (entry_two_ok_characters.drop 245) 184)
  have composed := scan_compose composed (scan3_arch (entry_two_ok_characters.drop 220) 200)
  have composed := scan_compose composed (scan3_entry_f (entry_two_ok_characters.drop 206) 206)
  have composed := scan_compose composed (UebersetzeProben2.scan_close (entry_two_ok_characters.drop 189) 214)
  have composed := scan_compose composed (scan3_dispatch_w (entry_two_ok_characters.drop 187) 216)
  have composed := scan_compose composed (scan3_stack (entry_two_ok_characters.drop 172) 223)
  have composed := scan_compose composed (scan3_preserves (entry_two_ok_characters.drop 143) 235)
  have composed := scan_compose composed (scan3_regs (entry_two_ok_characters.drop 116) 247)
  have composed := scan_compose composed (scan3_arch (entry_two_ok_characters.drop 91) 263)
  have composed := scan_compose composed (scan3_entry_e (entry_two_ok_characters.drop 77) 269)
  have composed := scan_compose composed (scan3_int_tail (entry_two_ok_characters.drop 60) 277)
  have composed := scan_compose composed (scan3_int_head (entry_two_ok_characters.drop 53) 284)
  have composed := scan_compose composed (scan3_fn_w (entry_two_ok_characters.drop 27) 302)
  have complete := scan_compose composed (scan3_module (entry_two_ok_characters.drop 11) 314)
  exact complete

def entry_via_ok : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 via idt arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::w; } }"

def entry_via_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', ')',
   ' ', '{', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'i', ' ', ':', ' ', 'u', '3', '2',
   ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ')', ' ', '{', ' ', '}', ' ', 'e', 'n', 't', 'r', 'y', ' ',
   'e', ' ', 'v', 'e', 'c', 't', 'o', 'r', ' ', '1', ' ', 'v', 'i', 'a', ' ', 'i', 'd', 't', ' ', 'a', 'r', 'c',
   'h', ' ', 'x', '8', '6', '_', '6', '4', ' ', '{', ' ', 'r', 'e', 'g', 's', ' ', 'i', 'n', ' ', '{', ' ', '}',
   ' ', 'r', 'e', 'g', 's', ' ', 'o', 'u', 't', ' ', '{', ' ', '}', ' ', 'p', 'r', 'e', 's', 'e', 'r', 'v', 'e',
   's', ' ', '{', ' ', '}', ' ', 'c', 'l', 'o', 'b', 'b', 'e', 'r', 's', ' ', '{', ' ', '}', ' ', 's', 't', 'a',
   'c', 'k', ' ', 'k', ' ', 'p', 'e', 'r', ' ', 'c', 'p', 'u', ' ', 'n', 'e', 's', 't', 'e', 'd', ' ', 'n', 'e',
   'v', 'e', 'r', ' ', 'd', 'i', 's', 'p', 'a', 't', 'c', 'h', ' ', 'm', ':', ':', 'w', ';', ' ', '}', ' ', '}']

def entry_via_ok_tokens : List Token :=
  tokens_module ++ tokens_fn_w ++ tokens_int_head ++ tokens_int_tail ++ tokens_entry_e ++ tokens_via ++
   tokens_arch ++ tokens_regs ++ tokens_preserves ++ tokens_stack ++ tokens_dispatch_w ++ tokens_close ++
   [.zeichen "}", .ende]

theorem entry_via_ok_lexed : lexL entry_via_ok_characters = .ok entry_via_ok_tokens := by
  change scan false entry_via_ok_characters 199 = .ok entry_via_ok_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 88) (UebersetzeProben2.scan_close (entry_via_ok_characters.drop 197) 89)
  have composed := scan_compose composed (scan3_dispatch_w (entry_via_ok_characters.drop 195) 91)
  have composed := scan_compose composed (scan3_stack (entry_via_ok_characters.drop 180) 98)
  have composed := scan_compose composed (scan3_preserves (entry_via_ok_characters.drop 151) 110)
  have composed := scan_compose composed (scan3_regs (entry_via_ok_characters.drop 124) 122)
  have composed := scan_compose composed (scan3_arch (entry_via_ok_characters.drop 99) 138)
  have composed := scan_compose composed (scan3_via (entry_via_ok_characters.drop 85) 144)
  have composed := scan_compose composed (scan3_entry_e (entry_via_ok_characters.drop 77) 148)
  have composed := scan_compose composed (scan3_int_tail (entry_via_ok_characters.drop 60) 156)
  have composed := scan_compose composed (scan3_int_head (entry_via_ok_characters.drop 53) 163)
  have composed := scan_compose composed (scan3_fn_w (entry_via_ok_characters.drop 27) 181)
  have complete := scan_compose composed (scan3_module (entry_via_ok_characters.drop 11) 193)
  exact complete

def entry_params_refused : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::p; } }"

def entry_params_refused_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', ')',
   ' ', '{', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'i', ' ', ':', ' ', 'u', '3', '2',
   ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ')', ' ', '{', ' ', '}', ' ', 'e', 'n', 't', 'r', 'y', ' ',
   'e', ' ', 'v', 'e', 'c', 't', 'o', 'r', ' ', '1', ' ', 'a', 'r', 'c', 'h', ' ', 'x', '8', '6', '_', '6', '4',
   ' ', '{', ' ', 'r', 'e', 'g', 's', ' ', 'i', 'n', ' ', '{', ' ', '}', ' ', 'r', 'e', 'g', 's', ' ', 'o', 'u',
   't', ' ', '{', ' ', '}', ' ', 'p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 's', ' ', '{', ' ', '}', ' ', 'c', 'l',
   'o', 'b', 'b', 'e', 'r', 's', ' ', '{', ' ', '}', ' ', 's', 't', 'a', 'c', 'k', ' ', 'k', ' ', 'p', 'e', 'r',
   ' ', 'c', 'p', 'u', ' ', 'n', 'e', 's', 't', 'e', 'd', ' ', 'n', 'e', 'v', 'e', 'r', ' ', 'd', 'i', 's', 'p',
   'a', 't', 'c', 'h', ' ', 'm', ':', ':', 'p', ';', ' ', '}', ' ', '}']

def entry_params_refused_tokens : List Token :=
  tokens_module ++ tokens_fn_w ++ tokens_int_head ++ tokens_int_tail ++ tokens_entry_e ++ tokens_arch ++
   tokens_regs ++ tokens_preserves ++ tokens_stack ++ tokens_dispatch_p ++ tokens_close ++ [.zeichen "}", .ende]

theorem entry_params_refused_lexed : lexL entry_params_refused_characters = .ok entry_params_refused_tokens := by
  change scan false entry_params_refused_characters 191 = .ok entry_params_refused_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 84) (UebersetzeProben2.scan_close (entry_params_refused_characters.drop 189) 85)
  have composed := scan_compose composed (scan3_dispatch_p (entry_params_refused_characters.drop 187) 87)
  have composed := scan_compose composed (scan3_stack (entry_params_refused_characters.drop 172) 94)
  have composed := scan_compose composed (scan3_preserves (entry_params_refused_characters.drop 143) 106)
  have composed := scan_compose composed (scan3_regs (entry_params_refused_characters.drop 116) 118)
  have composed := scan_compose composed (scan3_arch (entry_params_refused_characters.drop 91) 134)
  have composed := scan_compose composed (scan3_entry_e (entry_params_refused_characters.drop 77) 140)
  have composed := scan_compose composed (scan3_int_tail (entry_params_refused_characters.drop 60) 148)
  have composed := scan_compose composed (scan3_int_head (entry_params_refused_characters.drop 53) 155)
  have composed := scan_compose composed (scan3_fn_w (entry_params_refused_characters.drop 27) 173)
  have complete := scan_compose composed (scan3_module (entry_params_refused_characters.drop 11) 185)
  exact complete

def entry_unknown_refused : String :=
  "module m { impl fn w() { } impl fn p(i : u32 in 0 .. 1) { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::nix; } }"

def entry_unknown_refused_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', ')',
   ' ', '{', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'i', ' ', ':', ' ', 'u', '3', '2',
   ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ')', ' ', '{', ' ', '}', ' ', 'e', 'n', 't', 'r', 'y', ' ',
   'e', ' ', 'v', 'e', 'c', 't', 'o', 'r', ' ', '1', ' ', 'a', 'r', 'c', 'h', ' ', 'x', '8', '6', '_', '6', '4',
   ' ', '{', ' ', 'r', 'e', 'g', 's', ' ', 'i', 'n', ' ', '{', ' ', '}', ' ', 'r', 'e', 'g', 's', ' ', 'o', 'u',
   't', ' ', '{', ' ', '}', ' ', 'p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 's', ' ', '{', ' ', '}', ' ', 'c', 'l',
   'o', 'b', 'b', 'e', 'r', 's', ' ', '{', ' ', '}', ' ', 's', 't', 'a', 'c', 'k', ' ', 'k', ' ', 'p', 'e', 'r',
   ' ', 'c', 'p', 'u', ' ', 'n', 'e', 's', 't', 'e', 'd', ' ', 'n', 'e', 'v', 'e', 'r', ' ', 'd', 'i', 's', 'p',
   'a', 't', 'c', 'h', ' ', 'm', ':', ':', 'n', 'i', 'x', ';', ' ', '}', ' ', '}']

def entry_unknown_refused_tokens : List Token :=
  tokens_module ++ tokens_fn_w ++ tokens_int_head ++ tokens_int_tail ++ tokens_entry_e ++ tokens_arch ++
   tokens_regs ++ tokens_preserves ++ tokens_stack ++ tokens_dispatch_unknown ++ tokens_close ++
   [.zeichen "}", .ende]

theorem entry_unknown_refused_lexed : lexL entry_unknown_refused_characters = .ok entry_unknown_refused_tokens := by
  change scan false entry_unknown_refused_characters 193 = .ok entry_unknown_refused_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 86) (UebersetzeProben2.scan_close (entry_unknown_refused_characters.drop 191) 87)
  have composed := scan_compose composed (scan3_dispatch_unknown (entry_unknown_refused_characters.drop 189) 89)
  have composed := scan_compose composed (scan3_stack (entry_unknown_refused_characters.drop 172) 96)
  have composed := scan_compose composed (scan3_preserves (entry_unknown_refused_characters.drop 143) 108)
  have composed := scan_compose composed (scan3_regs (entry_unknown_refused_characters.drop 116) 120)
  have composed := scan_compose composed (scan3_arch (entry_unknown_refused_characters.drop 91) 136)
  have composed := scan_compose composed (scan3_entry_e (entry_unknown_refused_characters.drop 77) 142)
  have composed := scan_compose composed (scan3_int_tail (entry_unknown_refused_characters.drop 60) 150)
  have composed := scan_compose composed (scan3_int_head (entry_unknown_refused_characters.drop 53) 157)
  have composed := scan_compose composed (scan3_fn_w (entry_unknown_refused_characters.drop 27) 175)
  have complete := scan_compose composed (scan3_module (entry_unknown_refused_characters.drop 11) 187)
  exact complete

def locks_plain : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w() { } }"

def locks_plain_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u',
   'n', 't', ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',',
   ' ', '}', ' ', '}', ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{',
   ' ', 'T', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '0', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w',
   '(', ')', ' ', '{', ' ', '}', ' ', '}']

def locks_plain_tokens : List Token :=
  tokens_prelude ++ tokens_slot ++ tokens_lock ++ tokens_fn_w ++ [.zeichen "}", .ende]

theorem locks_plain_lexed : lexL locks_plain_characters = .ok locks_plain_tokens := by
  change scan false locks_plain_characters 97 = .ok locks_plain_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 36) (scan3_fn_w (locks_plain_characters.drop 95) 37)
  have composed := scan_compose composed (UebersetzeProben2.scan_lock (locks_plain_characters.drop 79) 49)
  have composed := scan_compose composed (UebersetzeProben2.scan_slot (locks_plain_characters.drop 49) 66)
  have complete := scan_compose composed (UebersetzeProben2.scan_prelude (locks_plain_characters.drop 29) 81)
  exact complete

def conc_ok : String :=
  "module m { impl fn w() { } impl fn v() { } concurrent { w, v }; }"

def conc_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', ')',
   ' ', '{', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'v', '(', ')', ' ', '{', ' ', '}', ' ', 'c',
   'o', 'n', 'c', 'u', 'r', 'r', 'e', 'n', 't', ' ', '{', ' ', 'w', ',', ' ', 'v', ' ', '}', ';', ' ', '}']

def conc_ok_tokens : List Token :=
  tokens_module ++ tokens_fn_w ++ tokens_fn_v ++ tokens_concurrent ++ tokens_roots_two ++ [.zeichen "}", .ende]

theorem conc_ok_lexed : lexL conc_ok_characters = .ok conc_ok_tokens := by
  change scan false conc_ok_characters 66 = .ok conc_ok_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 23) (scan3_roots_two (conc_ok_characters.drop 64) 24)
  have composed := scan_compose composed (scan3_concurrent (conc_ok_characters.drop 56) 32)
  have composed := scan_compose composed (scan3_fn_v (conc_ok_characters.drop 43) 36)
  have composed := scan_compose composed (scan3_fn_w (conc_ok_characters.drop 27) 48)
  have complete := scan_compose composed (scan3_module (conc_ok_characters.drop 11) 60)
  exact complete

def conc_first : String :=
  "module m { impl fn w() { } impl fn v() { } entry e vector 1 arch x86_64 { regs in { } regs out { } preserves { } clobbers { } stack k per cpu nested never dispatch m::v; } concurrent { w }; }"

def conc_first_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', ')',
   ' ', '{', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'v', '(', ')', ' ', '{', ' ', '}', ' ', 'e',
   'n', 't', 'r', 'y', ' ', 'e', ' ', 'v', 'e', 'c', 't', 'o', 'r', ' ', '1', ' ', 'a', 'r', 'c', 'h', ' ', 'x',
   '8', '6', '_', '6', '4', ' ', '{', ' ', 'r', 'e', 'g', 's', ' ', 'i', 'n', ' ', '{', ' ', '}', ' ', 'r', 'e',
   'g', 's', ' ', 'o', 'u', 't', ' ', '{', ' ', '}', ' ', 'p', 'r', 'e', 's', 'e', 'r', 'v', 'e', 's', ' ', '{',
   ' ', '}', ' ', 'c', 'l', 'o', 'b', 'b', 'e', 'r', 's', ' ', '{', ' ', '}', ' ', 's', 't', 'a', 'c', 'k', ' ',
   'k', ' ', 'p', 'e', 'r', ' ', 'c', 'p', 'u', ' ', 'n', 'e', 's', 't', 'e', 'd', ' ', 'n', 'e', 'v', 'e', 'r',
   ' ', 'd', 'i', 's', 'p', 'a', 't', 'c', 'h', ' ', 'm', ':', ':', 'v', ';', ' ', '}', ' ', 'c', 'o', 'n', 'c',
   'u', 'r', 'r', 'e', 'n', 't', ' ', '{', ' ', 'w', ' ', '}', ';', ' ', '}']

def conc_first_tokens : List Token :=
  tokens_module ++ tokens_fn_w ++ tokens_fn_v ++ tokens_entry_e ++ tokens_arch ++ tokens_regs ++
   tokens_preserves ++ tokens_stack ++ tokens_dispatch_v ++ tokens_close ++ tokens_concurrent ++ tokens_root_w ++
   [.zeichen "}", .ende]

theorem conc_first_lexed : lexL conc_first_characters = .ok conc_first_tokens := by
  change scan false conc_first_characters 192 = .ok conc_first_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 89) (scan3_root_w (conc_first_characters.drop 190) 90)
  have composed := scan_compose composed (scan3_concurrent (conc_first_characters.drop 185) 95)
  have composed := scan_compose composed (UebersetzeProben2.scan_close (conc_first_characters.drop 172) 99)
  have composed := scan_compose composed (scan3_dispatch_v (conc_first_characters.drop 170) 101)
  have composed := scan_compose composed (scan3_stack (conc_first_characters.drop 155) 108)
  have composed := scan_compose composed (scan3_preserves (conc_first_characters.drop 126) 120)
  have composed := scan_compose composed (scan3_regs (conc_first_characters.drop 99) 132)
  have composed := scan_compose composed (scan3_arch (conc_first_characters.drop 74) 148)
  have composed := scan_compose composed (scan3_entry_e (conc_first_characters.drop 60) 154)
  have composed := scan_compose composed (scan3_fn_v (conc_first_characters.drop 43) 162)
  have composed := scan_compose composed (scan3_fn_w (conc_first_characters.drop 27) 174)
  have complete := scan_compose composed (scan3_module (conc_first_characters.drop 11) 186)
  exact complete

def conc_args_ok : String :=
  "module m { impl fn p(i : u32 in 0 .. 1, b : bool) { } concurrent { p(1, true) }; }"

def conc_args_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'i',
   ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ',', ' ', 'b', ' ', ':', ' ',
   'b', 'o', 'o', 'l', ')', ' ', '{', ' ', '}', ' ', 'c', 'o', 'n', 'c', 'u', 'r', 'r', 'e', 'n', 't', ' ', '{',
   ' ', 'p', '(', '1', ',', ' ', 't', 'r', 'u', 'e', ')', ' ', '}', ';', ' ', '}']

def conc_args_ok_tokens : List Token :=
  tokens_module ++ tokens_int_head ++ tokens_args_tail ++ tokens_concurrent ++ tokens_start_args ++
   [.zeichen "}", .ende]

theorem conc_args_ok_lexed : lexL conc_args_ok_characters = .ok conc_args_ok_tokens := by
  change scan false conc_args_ok_characters 83 = .ok conc_args_ok_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 29) (scan3_start_args (conc_args_ok_characters.drop 81) 30)
  have composed := scan_compose composed (scan3_concurrent (conc_args_ok_characters.drop 67) 41)
  have composed := scan_compose composed (scan3_args_tail (conc_args_ok_characters.drop 54) 45)
  have composed := scan_compose composed (scan3_int_head (conc_args_ok_characters.drop 37) 59)
  have complete := scan_compose composed (scan3_module (conc_args_ok_characters.drop 11) 77)
  exact complete

def conc_params_refused : String :=
  "module m { impl fn p(i : u32 in 0 .. 1) { } concurrent { p }; }"

def conc_params_refused_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'i',
   ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ')', ' ', '{', ' ', '}', ' ',
   'c', 'o', 'n', 'c', 'u', 'r', 'r', 'e', 'n', 't', ' ', '{', ' ', 'p', ' ', '}', ';', ' ', '}']

def conc_params_refused_tokens : List Token :=
  tokens_module ++ tokens_int_head ++ tokens_int_tail ++ tokens_concurrent ++ tokens_root_p ++
   [.zeichen "}", .ende]

theorem conc_params_refused_lexed : lexL conc_params_refused_characters = .ok conc_params_refused_tokens := by
  change scan false conc_params_refused_characters 64 = .ok conc_params_refused_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 23) (scan3_root_p (conc_params_refused_characters.drop 62) 24)
  have composed := scan_compose composed (scan3_concurrent (conc_params_refused_characters.drop 57) 29)
  have composed := scan_compose composed (scan3_int_tail (conc_params_refused_characters.drop 44) 33)
  have composed := scan_compose composed (scan3_int_head (conc_params_refused_characters.drop 37) 40)
  have complete := scan_compose composed (scan3_module (conc_params_refused_characters.drop 11) 58)
  exact complete

def conc_arg_range_refused : String :=
  "module m { impl fn p(i : u32 in 0 .. 1) { } concurrent { p(2) }; }"

def conc_arg_range_refused_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'i',
   ' ', ':', ' ', 'u', '3', '2', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', ')', ' ', '{', ' ', '}', ' ',
   'c', 'o', 'n', 'c', 'u', 'r', 'r', 'e', 'n', 't', ' ', '{', ' ', 'p', '(', '2', ')', ' ', '}', ';', ' ', '}']

def conc_arg_range_refused_tokens : List Token :=
  tokens_module ++ tokens_int_head ++ tokens_int_tail ++ tokens_concurrent ++ tokens_start_range ++
   [.zeichen "}", .ende]

theorem conc_arg_range_refused_lexed : lexL conc_arg_range_refused_characters = .ok conc_arg_range_refused_tokens := by
  change scan false conc_arg_range_refused_characters 67 = .ok conc_arg_range_refused_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 23) (scan3_start_range (conc_arg_range_refused_characters.drop 65) 24)
  have composed := scan_compose composed (scan3_concurrent (conc_arg_range_refused_characters.drop 57) 32)
  have composed := scan_compose composed (scan3_int_tail (conc_arg_range_refused_characters.drop 44) 36)
  have composed := scan_compose composed (scan3_int_head (conc_arg_range_refused_characters.drop 37) 43)
  have complete := scan_compose composed (scan3_module (conc_arg_range_refused_characters.drop 11) 61)
  exact complete

def conc_ptr_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } impl fn p(k : ptr<normal, r> T) { } concurrent { p(&T) }; }"

def conc_ptr_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u',
   'n', 't', ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',',
   ' ', '}', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'k', ' ', ':', ' ', 'p', 't', 'r',
   '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', '>', ' ', 'T', ')', ' ', '{', ' ', '}', ' ', 'c', 'o', 'n',
   'c', 'u', 'r', 'r', 'e', 'n', 't', ' ', '{', ' ', 'p', '(', '&', 'T', ')', ' ', '}', ';', ' ', '}']

def conc_ptr_ok_tokens : List Token :=
  tokens_prelude ++ tokens_slot ++ tokens_ptr_head ++ tokens_ptr_tail ++ tokens_concurrent ++
   tokens_start_ptr_t ++ [.zeichen "}", .ende]

theorem conc_ptr_ok_lexed : lexL conc_ptr_ok_characters = .ok conc_ptr_ok_tokens := by
  change scan false conc_ptr_ok_characters 109 = .ok conc_ptr_ok_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 39) (scan3_start_ptr_t (conc_ptr_ok_characters.drop 107) 40)
  have composed := scan_compose composed (scan3_concurrent (conc_ptr_ok_characters.drop 98) 49)
  have composed := scan_compose composed (scan3_ptr_tail (conc_ptr_ok_characters.drop 85) 53)
  have composed := scan_compose composed (scan3_ptr_head (conc_ptr_ok_characters.drop 63) 68)
  have composed := scan_compose composed (UebersetzeProben2.scan_slot (conc_ptr_ok_characters.drop 49) 78)
  have complete := scan_compose composed (UebersetzeProben2.scan_prelude (conc_ptr_ok_characters.drop 29) 93)
  exact complete

def conc_ptr_refused : String :=
  "module m { table T count 2 { slot { v : u32, } } table U count 2 { slot { v : u32, } } impl fn p(k : ptr<normal, r> T) { } concurrent { p(&U) }; }"

def conc_ptr_refused_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u',
   'n', 't', ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',',
   ' ', '}', ' ', '}', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'U', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', '{',
   ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}', ' ', 'i',
   'm', 'p', 'l', ' ', 'f', 'n', ' ', 'p', '(', 'k', ' ', ':', ' ', 'p', 't', 'r', '<', 'n', 'o', 'r', 'm', 'a',
   'l', ',', ' ', 'r', '>', ' ', 'T', ')', ' ', '{', ' ', '}', ' ', 'c', 'o', 'n', 'c', 'u', 'r', 'r', 'e', 'n',
   't', ' ', '{', ' ', 'p', '(', '&', 'U', ')', ' ', '}', ';', ' ', '}']

def conc_ptr_refused_tokens : List Token :=
  tokens_prelude ++ tokens_slot ++ tokens_table_u ++ tokens_slot ++ tokens_ptr_head ++ tokens_ptr_tail ++
   tokens_concurrent ++ tokens_start_ptr_u ++ [.zeichen "}", .ende]

theorem conc_ptr_refused_lexed : lexL conc_ptr_refused_characters = .ok conc_ptr_refused_tokens := by
  change scan false conc_ptr_refused_characters 147 = .ok conc_ptr_refused_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 52) (scan3_start_ptr_u (conc_ptr_refused_characters.drop 145) 53)
  have composed := scan_compose composed (scan3_concurrent (conc_ptr_refused_characters.drop 136) 62)
  have composed := scan_compose composed (scan3_ptr_tail (conc_ptr_refused_characters.drop 123) 66)
  have composed := scan_compose composed (scan3_ptr_head (conc_ptr_refused_characters.drop 101) 81)
  have composed := scan_compose composed (UebersetzeProben2.scan_slot (conc_ptr_refused_characters.drop 87) 91)
  have composed := scan_compose composed (scan3_table_u (conc_ptr_refused_characters.drop 67) 106)
  have composed := scan_compose composed (UebersetzeProben2.scan_slot (conc_ptr_refused_characters.drop 49) 116)
  have complete := scan_compose composed (UebersetzeProben2.scan_prelude (conc_ptr_refused_characters.drop 29) 131)
  exact complete

def conc_unknown_refused : String :=
  "module m { impl fn w() { } concurrent { nix }; }"

def conc_unknown_refused_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', ')',
   ' ', '{', ' ', '}', ' ', 'c', 'o', 'n', 'c', 'u', 'r', 'r', 'e', 'n', 't', ' ', '{', ' ', 'n', 'i', 'x', ' ',
   '}', ';', ' ', '}']

def conc_unknown_refused_tokens : List Token :=
  tokens_module ++ tokens_fn_w ++ tokens_concurrent ++ tokens_root_unknown ++ [.zeichen "}", .ende]

theorem conc_unknown_refused_lexed : lexL conc_unknown_refused_characters = .ok conc_unknown_refused_tokens := by
  change scan false conc_unknown_refused_characters 49 = .ok conc_unknown_refused_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 21) (scan3_root_unknown (conc_unknown_refused_characters.drop 47) 22)
  have composed := scan_compose composed (scan3_concurrent (conc_unknown_refused_characters.drop 40) 27)
  have composed := scan_compose composed (scan3_fn_w (conc_unknown_refused_characters.drop 27) 31)
  have complete := scan_compose composed (scan3_module (conc_unknown_refused_characters.drop 11) 43)
  exact complete

def mask_src : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0 masks irqs; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; } } }"

def mask_src_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u',
   'n', 't', ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',',
   ' ', '}', ' ', '}', ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{',
   ' ', 'T', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '0', ' ', 'm', 'a', 's', 'k', 's', ' ', 'i', 'r', 'q', 's',
   ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':', ' ', 'p', 't', 'r', '<', 'n', 'o',
   'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' ', 'i', ' ', ':', ' ', 'i', 'n', 'd', 'e', 'x',
   ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i',
   't', 'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '}',
   ' ', '{', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'k', '.', 's', 'l', 'o', 't', 's', '[', 'i',
   ']', '.', 'v', ' ', '=', ' ', '1', ';', ' ', '}', ' ', '}', ' ', '}']

def mask_src_tokens : List Token :=
  tokens_prelude ++ tokens_slot ++ tokens_lock_head ++ tokens_mask_irqs ++ tokens_writer ++ tokens_parameters ++
   tokens_effects ++ tokens_close ++ tokens_open ++ tokens_take ++ tokens_write_one ++ tokens_close ++
   tokens_close ++ [.zeichen "}", .ende]

theorem mask_src_lexed : lexL mask_src_characters = .ok mask_src_tokens := by
  change scan false mask_src_characters 213 = .ok mask_src_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 85) (UebersetzeProben2.scan_close (mask_src_characters.drop 211) 86)
  have composed := scan_compose composed (UebersetzeProben2.scan_close (mask_src_characters.drop 209) 88)
  have composed := scan_compose composed (UebersetzeProben2.scan_write_one (mask_src_characters.drop 207) 90)
  have composed := scan_compose composed (UebersetzeProben2.scan_take (mask_src_characters.drop 189) 104)
  have composed := scan_compose composed (UebersetzeProben2.scan_open (mask_src_characters.drop 179) 110)
  have composed := scan_compose composed (UebersetzeProben2.scan_close (mask_src_characters.drop 177) 112)
  have composed := scan_compose composed (UebersetzeProben2.scan_effects (mask_src_characters.drop 175) 114)
  have composed := scan_compose composed (UebersetzeProben2.scan_parameters (mask_src_characters.drop 151) 125)
  have composed := scan_compose composed (UebersetzeProben2.scan_writer (mask_src_characters.drop 123) 140)
  have composed := scan_compose composed (scan3_mask_irqs (mask_src_characters.drop 90) 161)
  have composed := scan_compose composed (scan3_lock_head (mask_src_characters.drop 78) 166)
  have composed := scan_compose composed (UebersetzeProben2.scan_slot (mask_src_characters.drop 49) 182)
  have complete := scan_compose composed (UebersetzeProben2.scan_prelude (mask_src_characters.drop 29) 197)
  exact complete

def other_mask_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u',
   'n', 't', ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',',
   ' ', '}', ' ', '}', ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{',
   ' ', 'T', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', '0', ' ', 'm', 'a', 's', 'k', 's', ' ', 'n', 'm', 'i', ';',
   ' ', '}']

def other_mask_tokens : List Token :=
  tokens_prelude ++ tokens_slot ++ tokens_lock_head ++ tokens_mask_other ++ [.zeichen "}", .ende]

theorem other_mask_lexed : lexL other_mask_characters = .ok other_mask_tokens := by
  change scan false other_mask_characters 91 = .ok other_mask_tokens
  have composed := scan_compose (UebersetzeProben2.scan_end 38) (scan3_mask_other (other_mask_characters.drop 89) 39)
  have composed := scan_compose composed (scan3_lock_head (other_mask_characters.drop 78) 44)
  have composed := scan_compose composed (UebersetzeProben2.scan_slot (other_mask_characters.drop 49) 60)
  have complete := scan_compose composed (UebersetzeProben2.scan_prelude (other_mask_characters.drop 29) 75)
  exact complete

end Gabbro.Grammatik.Parser.UebersetzeProben3
