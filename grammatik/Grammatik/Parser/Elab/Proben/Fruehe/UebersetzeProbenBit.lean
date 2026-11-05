/-
  File:      Grammatik/Parser/UebersetzeProben.lean
  Subject:   Sieve (a), parser lane: witnesses and planted defects for the widenings of the
             elaborator and the generic lowering.

  Every probe runs the WHOLE pipeline `uebersetzeAllg` on a small source text and names the stage
  where it stops (`stufe`). A WITNESS is a source that reaches `OK`; a PLANTED DEFECT is a source
  one token away that must stop, at the stage and with the message the widening promises. A
  widening whose defect also passes would be a widening that let something through.

  The texts are short on purpose: the kernel decodes a `String` per proof (O13).
  Pipeline certificates stop at elaboration and check the actual lowering phases separately.
  The source strings and all expected stage diagnostics stay pinned below.
  Corpus programs are pinned as characters in the chain instances, not here.

  WALL 1 (2026-09-30): units WITHOUT a table; integer arithmetic (`+`, `-`, `*`) in values, with
  the range of the result computed like `Expr.add`/`sub`/`mul` carry it; the built-in widths
  `uN`/`iN`; an omitted `effects` (derived by the checker) read as the empty set.
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProbenBasis
-- The shared phase executes these gates even when a source declares no checks or static parameters.
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
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


namespace Gabbro.Grammatik.Parser.UebersetzeProben

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

set_option maxRecDepth 100000

-- Keep the original proof-local logarithm reduction rule.
attribute [local cbv_eval] Nat.log2_def

/-- WITNESS (`beispiele/69`): `|` of two conversions, `^` with a limit word (`beispiele/62`), `&`. -/
def bit1 : String :=
  "module m { impl fn k(a : u32, b : u32) -> u64 { return u64(a) | u64(b); } impl fn i(w : u32) -> u32 { return w ^ u32::max; } impl fn m(a : u8, b : u8) -> u8 { return a & b; } }"
private def bit1Characters : List Char :=
  ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'k', '(', 'a', ' ', ':',
   ' ', 'u', '3', '2', ',', ' ', 'b', ' ', ':', ' ', 'u', '3', '2', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ', '{', ' ',
   'r', 'e', 't', 'u', 'r', 'n', ' ', 'u', '6', '4', '(', 'a', ')', ' ', '|', ' ', 'u', '6', '4', '(', 'b', ')', ';', ' ',
   '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'i', '(', 'w', ' ', ':', ' ', 'u', '3', '2', ')', ' ', '-', '>', ' ',
   'u', '3', '2', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'w', ' ', '^', ' ', 'u', '3', '2', ':', ':', 'm', 'a',
   'x', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', '(', 'a', ' ', ':', ' ', 'u', '8', ',', ' ', 'b',
   ' ', ':', ' ', 'u', '8', ')', ' ', '-', '>', ' ', 'u', '8', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'a', ' ',
   '&', ' ', 'b', ';', ' ', '}', ' ', '}']

private theorem bit1_text : bit1 = String.ofList bit1Characters := by cbv

-- Equations of the canonical scanner stop before their symbolic continuation.
private theorem bit_scan_module (rest : List Char) (n : Nat) :
    scan false (['m', 'o', 'd', 'u', 'l', 'e', ' ', 'm', ' ', '{', ' '] ++ rest) (n + 6) =
    [.wort "module", .ident "m", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem bit_scan_first_head (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'k', '(', 'a', ' ', ':', ' ', 'u', '3', '2', ',', ' ', 'b', ' ', ':', ' ', 'u', '3', '2', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ', '{', ' '] ++ rest) (n + 26) =
    [.wort "impl", .wort "fn", .ident "k", .zeichen "(", .ident "a", .zeichen ":", .wort "u32", .zeichen ",", .ident "b", .zeichen ":", .wort "u32", .zeichen ")", .zeichen "->", .wort "u64", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem bit_scan_first_body (rest : List Char) (n : Nat) :
    scan false (['r', 'e', 't', 'u', 'r', 'n', ' ', 'u', '6', '4', '(', 'a', ')', ' ', '|', ' ', 'u', '6', '4', '(', 'b', ')', ';', ' ', '}', ' '] ++ rest) (n + 17) =
    [.wort "return", .wort "u64", .zeichen "(", .ident "a", .zeichen ")", .zeichen "|", .wort "u64", .zeichen "(", .ident "b", .zeichen ")", .zeichen ";", .zeichen "}"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem bit_scan_second_head (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'i', '(', 'w', ' ', ':', ' ', 'u', '3', '2', ')', ' ', '-', '>', ' ', 'u', '3', '2', ' ', '{', ' '] ++ rest) (n + 19) =
    [.wort "impl", .wort "fn", .ident "i", .zeichen "(", .wort "w", .zeichen ":", .wort "u32", .zeichen ")", .zeichen "->", .wort "u32", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem bit_scan_second_body (rest : List Char) (n : Nat) :
    scan false (['r', 'e', 't', 'u', 'r', 'n', ' ', 'w', ' ', '^', ' ', 'u', '3', '2', ':', ':', 'm', 'a', 'x', ';', ' ', '}', ' '] ++ rest) (n + 13) =
    [.wort "return", .wort "w", .zeichen "^", .wort "u32", .zeichen "::", .wort "max", .zeichen ";", .zeichen "}"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem bit_scan_third_head (rest : List Char) (n : Nat) :
    scan false (['i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', '(', 'a', ' ', ':', ' ', 'u', '8', ',', ' ', 'b', ' ', ':', ' ', 'u', '8', ')', ' ', '-', '>', ' ', 'u', '8', ' ', '{', ' '] ++ rest) (n + 26) =
    [.wort "impl", .wort "fn", .ident "m", .zeichen "(", .ident "a", .zeichen ":", .wort "u8", .zeichen ",", .ident "b", .zeichen ":", .wort "u8", .zeichen ")", .zeichen "->", .wort "u8", .zeichen "{"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem bit_scan_third_body (rest : List Char) (n : Nat) :
    scan false (['r', 'e', 't', 'u', 'r', 'n', ' ', 'a', ' ', '&', ' ', 'b', ';', ' ', '}', ' '] ++ rest) (n + 11) =
    [.wort "return", .ident "a", .zeichen "&", .ident "b", .zeichen ";", .zeichen "}"].foldr (fun t result => Except.map (t :: ·) result) (scan false rest n) := by cbv

private theorem bit_scan_end (n : Nat) :
    scan false ['}'] (n + 1) = .ok [.zeichen "}", .ende] := by cbv

private theorem bit_token_maps (tokens : List Token) (result : Except LexFehler (List Token)) :
    tokens.foldr (fun t answer => Except.map (t :: ·) answer) result =
      Except.map (tokens ++ ·) result := by
  induction tokens with
  | nil => cases result <;> rfl
  | cons t ts ih => simp only [List.foldr, ih]; cases result <;> rfl

private def bit1Tokens : List Token :=
  [.wort "module", .ident "m", .zeichen "{", .wort "impl", .wort "fn", .ident "k", .zeichen "(", .ident "a", .zeichen ":", .wort "u32", .zeichen ",", .ident "b",
   .zeichen ":", .wort "u32", .zeichen ")", .zeichen "->", .wort "u64", .zeichen "{", .wort "return", .wort "u64", .zeichen "(", .ident "a", .zeichen ")", .zeichen "|",
   .wort "u64", .zeichen "(", .ident "b", .zeichen ")", .zeichen ";", .zeichen "}", .wort "impl", .wort "fn", .ident "i", .zeichen "(", .wort "w", .zeichen ":",
   .wort "u32", .zeichen ")", .zeichen "->", .wort "u32", .zeichen "{", .wort "return", .wort "w", .zeichen "^", .wort "u32", .zeichen "::", .wort "max", .zeichen ";",
   .zeichen "}", .wort "impl", .wort "fn", .ident "m", .zeichen "(", .ident "a", .zeichen ":", .wort "u8", .zeichen ",", .ident "b", .zeichen ":", .wort "u8",
   .zeichen ")", .zeichen "->", .wort "u8", .zeichen "{", .wort "return", .ident "a", .zeichen "&", .ident "b", .zeichen ";", .zeichen "}", .zeichen "}", .ende]

private theorem bit_scan_compose {source rest : List Char} {fuel remaining : Nat}
    {emitted tokens : List Token} (tail : scan false rest remaining = .ok tokens)
    (head : scan false source fuel = emitted.foldr (fun t result => Except.map (t :: ·) result)
      (scan false rest remaining)) : scan false source fuel = .ok (emitted ++ tokens) := by
  rw [tail, bit_token_maps] at head
  exact head

private theorem bit1_lexed : lexL bit1Characters = .ok bit1Tokens := by
  change scan false bit1Characters 177 = .ok bit1Tokens
  have composed := bit_scan_compose (bit_scan_end 58) (bit_scan_third_body (bit1Characters.drop 175) 59)
  have composed := bit_scan_compose composed (bit_scan_third_head (bit1Characters.drop 159) 70)
  have composed := bit_scan_compose composed (bit_scan_second_body (bit1Characters.drop 125) 96)
  have composed := bit_scan_compose composed (bit_scan_second_head (bit1Characters.drop 102) 109)
  have composed := bit_scan_compose composed (bit_scan_first_body (bit1Characters.drop 74) 128)
  have composed := bit_scan_compose composed (bit_scan_first_head (bit1Characters.drop 48) 145)
  have complete := bit_scan_compose composed (bit_scan_module (bit1Characters.drop 11) 171)
  exact complete

private theorem bit1_parsed : (parseTopTief bit1Tokens).toOption.isSome = true := by cbv
private def bit1Items : List SItemTief := (parseTopTief bit1Tokens).toOption.get bit1_parsed

private def bit1Unit : UProg :=
  { tabs := []
    locks := []
    fns := (scalarUnit "k" [("a", .int 0 4294967295), ("b", .int 0 4294967295)]
        (0, 18446744073709551615)
        (.bor (.conv 0 18446744073709551615 (.param "a"))
          (.conv 0 18446744073709551615 (.param "b")))).fns ++
      (scalarUnit "i" [("w", .int 0 4294967295)] (0, 4294967295)
        (.bxor (.param "w") (.lit 4294967295))).fns ++
      (scalarUnit "m" [("a", .int 0 255), ("b", .int 0 255)] (0, 255)
        (.band (.param "a") (.param "b"))).fns }

private theorem bit1_elaborated : elabU (pre108 bit1Items) = .ok bit1Unit := by cbv

private theorem bit1_front : Frontend bit1 bit1Unit := by
  have lexed : lex bit1 = .ok bit1Tokens := by
    rw [bit1_text, lex_ofList]
    exact bit1_lexed
  have parsed : parseTopTief bit1Tokens = .ok bit1Items := except_ok_get bit1_parsed
  intro after
  rw [lexed]
  dsimp only
  rw [parsed]
  dsimp only
  rw [bit1_elaborated]

private theorem bit1_function0 :
    (lowerFnAt bit1Unit ⟨0, by decide⟩).toOption.isSome = true := by cbv
private theorem bit1_function1 :
    (lowerFnAt bit1Unit ⟨1, by decide⟩).toOption.isSome = true := by cbv
private theorem bit1_function2 :
    (lowerFnAt bit1Unit ⟨2, by decide⟩).toOption.isSome = true := by cbv

private theorem bit1_functions : lowerEach bit1Unit (List.finRange bit1Unit.fns.length) = .ok () := by
  change lowerEach bit1Unit [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] = .ok ()
  rw [lowerEach, except_ok_get bit1_function0, lowerEach, except_ok_get bit1_function1,
    lowerEach, except_ok_get bit1_function2, lowerEach]

private theorem bit1_contracts : contractGate bit1Unit = true := by cbv
private theorem bit1_measures : (Measures.lowerMeasures bit1Unit).toOption.isSome = true := by cbv

private theorem bit1_lowered : (lowerAllg bit1Unit).toOption.isSome = true :=
  lowering_ok bit1Unit rfl bit1_functions bit1_contracts bit1_measures
    (by simp [bit1Unit, scalarUnit])

theorem bit1_ok : stufe bit1 = "OK" := stufe_ok bit1_front bit1_lowered

/-- PLANTED DEFECT: a bit operation over a signed range (M137 allows non-negative ranges only). -/
def bit1_vorz : String :=
  "module m { impl fn m(a : i32, b : i32) -> i32 { return a & b; } }"
theorem bit1_vorz_refused : stufe bit1_vorz = "lower: bit operation over a negative range" := by
  let unit : UProg := scalarUnit "m" [("a", .int (-2147483648) 2147483647), ("b", .int (-2147483648) 2147483647)] (-2147483648, 2147483647) (.band (.param "a") (.param "b"))
  have front : Frontend bit1_vorz unit := by intro after; cbv
  exact stufe_error front (lowering_error unit "bit operation over a negative range" rfl (by cbv))

end Gabbro.Grammatik.Parser.UebersetzeProben
