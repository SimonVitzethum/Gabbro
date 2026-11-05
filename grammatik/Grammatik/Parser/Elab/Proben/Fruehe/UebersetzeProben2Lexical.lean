module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben2Basis
@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeProben2

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

/-- Compose fully instantiated scanner equations; no source suffix is inferred by rewriting. -/
private theorem scan_compose {source rest : List Char} {fuel remaining : Nat}
    {emitted tokens : List Token} (tail : scan false rest remaining = .ok tokens)
    (head : scan false source fuel = emitted.foldr (fun t result => Except.map (t :: ·) result) (scan false rest remaining)) :
    scan false source fuel = .ok (emitted ++ tokens) := by
  rw [tail, token_maps] at head
  exact head

def locks1_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; } } }"

def locks1_ok_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't',
   ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}',
   ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r',
   'a', 'n', 'k', ' ', '0', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':', ' ', 'p', 't', 'r',
   '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' ', 'i', ' ', ':', ' ', 'i', 'n', 'd', 'e',
   'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't',
   'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '}', ' ', '{', ' ',
   'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'k', '.', 's', 'l', 'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=',
   ' ', '1', ';', ' ', '}', ' ', '}', ' ', '}']

def locks1_ok_tokens : List Token :=
    table_tokens ++ [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++ effect_tokens ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 1 ++ [.zeichen "}", .zeichen "}", .zeichen "}", .ende]

theorem locks1_ok_lexed : lexL locks1_ok_characters = .ok locks1_ok_tokens := by
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
  have complete := scan_compose composed (scan_prelude (locks1_ok_characters.drop 29) 186)
  exact complete


def locks2_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; k.slots[i].v = 2; } locks L { k.slots[i].v = 3; } } }"

def locks2_ok_characters : List Char :=
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

def locks2_ok_tokens : List Token :=
    table_tokens ++ [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++ effect_tokens ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 1 ++ write_tokens 2 ++ [.zeichen "}"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 3 ++ [.zeichen "}", .zeichen "}", .zeichen "}", .ende]

theorem locks2_ok_lexed : lexL locks2_ok_characters = .ok locks2_ok_tokens := by
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
  have complete := scan_compose composed (scan_prelude (locks2_ok_characters.drop 29) 234)
  exact complete


def locks_nested_same : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { locks L { k.slots[i].v = 1; } } } }"

def locks_nested_same_characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't',
   ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', ' ', ':', ' ', 'u', '3', '2', ',', ' ', '}', ' ', '}',
   ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r',
   'a', 'n', 'k', ' ', '0', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'w', '(', 'k', ' ', ':', ' ', 'p', 't', 'r',
   '<', 'n', 'o', 'r', 'm', 'a', 'l', ',', ' ', 'r', 'w', '>', ' ', 'T', ',', ' ', 'i', ' ', ':', ' ', 'i', 'n', 'd', 'e',
   'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'w', 'r', 'i', 't',
   'e', 's', ' ', 'k', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '}', ' ', '{', ' ',
   'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ', 'k', '.', 's', 'l',
   'o', 't', 's', '[', 'i', ']', '.', 'v', ' ', '=', ' ', '1', ';', ' ', '}', ' ', '}', ' ', '}', ' ', '}']

def locks_nested_same_tokens : List Token :=
    table_tokens ++ [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++ effect_tokens ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 1 ++ [.zeichen "}", .zeichen "}", .zeichen "}", .zeichen "}", .ende]

theorem locks_nested_same_lexed : lexL locks_nested_same_characters = .ok locks_nested_same_tokens := by
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
  have complete := scan_compose composed (scan_prelude (locks_nested_same_characters.drop 29) 198)
  exact complete


def locks_rank_ok : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; lock M protects { } rank 1; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L, locks M } { locks L { locks M { k.slots[i].v = 1; } } } }"

def locks_rank_ok_characters : List Char :=
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

def locks_rank_ok_tokens : List Token :=
    table_tokens ++ [.wort "lock", .ident "M", .wort "protects", .zeichen "{", .zeichen "}", .wort "rank", .num 1, .zeichen ";"] ++ [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++
    [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L", .zeichen ",", .wort "locks", .ident "M"] ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ [.wort "locks", .ident "M", .zeichen "{"] ++ write_tokens 1 ++ [.zeichen "}", .zeichen "}", .zeichen "}", .zeichen "}", .ende]

theorem locks_rank_ok_lexed : lexL locks_rank_ok_characters = .ok locks_rank_ok_tokens := by
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
  have complete := scan_compose composed (scan_prelude (locks_rank_ok_characters.drop 29) 235)
  exact complete


def locks_rank_down : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; lock M protects { } rank 1; impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L, locks M } { locks M { locks L { k.slots[i].v = 1; } } } }"

def locks_rank_down_characters : List Char :=
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

def locks_rank_down_tokens : List Token :=
    table_tokens ++ [.wort "lock", .ident "M", .wort "protects", .zeichen "{", .zeichen "}", .wort "rank", .num 1, .zeichen ";"] ++ [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++
    [.wort "writes", .ident "k", .zeichen ".", .wort "slots", .zeichen ",", .wort "locks", .ident "L", .zeichen ",", .wort "locks", .ident "M"] ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "M", .zeichen "{"] ++ [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 1 ++ [.zeichen "}", .zeichen "}", .zeichen "}", .zeichen "}", .ende]

theorem locks_rank_down_lexed : lexL locks_rank_down_characters = .ok locks_rank_down_tokens := by
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
  have complete := scan_compose composed (scan_prelude (locks_rank_down_characters.drop 29) 235)
  exact complete


def locks_call_needing_it : String :=
  "module m { table T count 2 { slot { v : u32, } } lock L protects { T } rank 0; impl fn g(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { k.slots[i].v = 1; } } impl fn w(k : ptr<normal, rw> T, i : index into T) effects { writes k.slots, locks L } { locks L { g(k, i); } } }"

def locks_call_needing_it_characters : List Char :=
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

def locks_call_needing_it_tokens : List Token :=
    table_tokens ++ [.wort "impl", .wort "fn", .ident "g"] ++ parameter_tokens ++ effect_tokens ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ write_tokens 1 ++ [.zeichen "}", .zeichen "}"] ++
    [.wort "impl", .wort "fn", .wort "w"] ++ parameter_tokens ++ effect_tokens ++ [.zeichen "}", .zeichen "{"] ++
    [.wort "locks", .ident "L", .zeichen "{"] ++ [.ident "g", .zeichen "(", .ident "k", .zeichen ",", .ident "i", .zeichen ")", .zeichen ";"] ++ [.zeichen "}", .zeichen "}", .zeichen "}", .ende]

theorem locks_call_needing_it_lexed : lexL locks_call_needing_it_characters = .ok locks_call_needing_it_tokens := by
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
  have complete := scan_compose composed (scan_prelude (locks_call_needing_it_characters.drop 29) 298)
  exact complete

end Gabbro.Grammatik.Parser.UebersetzeProben2
