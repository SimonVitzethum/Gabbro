module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
import Grammatik.Parser.Stmt.LibraryFixtureScanning
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
import all Grammatik.Parser.Item.ElementTief.Defs5
import all Grammatik.Parser.Item.ElementTief.Defs7
import all Grammatik.Parser.Stmt.LibraryFixtureScanning

import all Init.Data.List.MapIdx
import all Init.Data.Repr
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
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
import all Init.Data.String.ToSlice
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Extra
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Legacy
import all Init.Data.String.Termination

@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Uebersetzung.LibraryFixtureScanning

/-- The counterprobe unit: the probe answers `false`, the external probe `ext`
    with its text is bound to the check. -/
def checkTextSonde : String :=
  "impl fn g() { return; } impl fn ext() -> bool { return false; } check p { claim \"c\" measures x gates g can_fail { let x: u64 = 3; return x < 0; } counterprobe \"ext text\" expects ext }"

-- Each cut proves the existing scanner's arbitrary-suffix equation. The
-- complete source uses its original character-count fuel, never a new lexer.
scoped macro "counterprobe_cut " name:ident " as " text:str
    " tokens " emitted:term " steps " count:num : command => do
  let literal : Lean.TSyntax `term := ⟨text.raw⟩
  let fuel : Lean.TSyntax `term := ⟨count.raw⟩
  `(command| private def $name : Chunk where
    characters := ($literal).toList
    tokens := $emitted
    steps := $fuel
    scanned := by intro rest remaining; cbv)

open scoped Gabbro.Grammatik.Parser.Uebersetze

counterprobe_cut sondeGate as "impl fn g() { return; } "
  tokens [.wort "impl", .wort "fn", .ident "g", .zeichen "(", .zeichen ")",
    .zeichen "{", .wort "return", .zeichen ";", .zeichen "}"] steps 15
counterprobe_cut sondeExternal as "impl fn ext() -> bool { return false; } "
  tokens [.wort "impl", .wort "fn", .ident "ext", .zeichen "(", .zeichen ")",
    .zeichen "->", .wort "bool", .zeichen "{", .wort "return", .wort "false",
    .zeichen ";", .zeichen "}"] steps 21
counterprobe_cut sondeHeadP as "check p { claim "
  tokens [.wort "check", .ident "p", .zeichen "{", .wort "claim"] steps 8
counterprobe_cut sondeHeadQ as "check q { claim "
  tokens [.wort "check", .ident "q", .zeichen "{", .wort "claim"] steps 8
counterprobe_cut sondeMeasure as "\"c\" measures x gates g "
  tokens [.text "c", .wort "measures", .wort "x", .wort "gates", .ident "g"] steps 10
counterprobe_cut sondeBodyHead as "can_fail { "
  tokens [.wort "can_fail", .zeichen "{"] steps 4
counterprobe_cut sondeBinding as "let x: u64 = 3; "
  tokens [.wort "let", .wort "x", .zeichen ":", .wort "u64", .zeichen "=",
    .num 3, .zeichen ";"] steps 12
counterprobe_cut sondeFalse as "return false; } "
  tokens [.wort "return", .wort "false", .zeichen ";", .zeichen "}"] steps 7
counterprobe_cut sondeComparison as "return x < 0; } "
  tokens [.wort "return", .wort "x", .zeichen "<", .num 0, .zeichen ";",
    .zeichen "}"] steps 11
counterprobe_cut sondeBindingText as "counterprobe \"ext text\" expects ext }"
  tokens [.wort "counterprobe", .text "ext text", .wort "expects", .ident "ext",
    .zeichen "}"] steps 9
counterprobe_cut sondeBindingOne as "counterprobe \"one\" expects ext } "
  tokens [.wort "counterprobe", .text "one", .wort "expects", .ident "ext",
    .zeichen "}"] steps 10
counterprobe_cut sondeBindingTwo as "counterprobe \"two\" expects ext }"
  tokens [.wort "counterprobe", .text "two", .wort "expects", .ident "ext",
    .zeichen "}"] steps 9

private def sondeChunks : List Chunk :=
  [sondeGate, sondeExternal, sondeHeadP, sondeMeasure, sondeBodyHead,
    sondeBinding, sondeComparison, sondeBindingText]
private def sondeUnboundChunks : List Chunk :=
  [sondeGate, sondeHeadP, sondeMeasure, sondeBodyHead, sondeFalse, sondeBindingText]
private def sondeDuplicateChunks : List Chunk :=
  [sondeGate, sondeExternal, sondeHeadP, sondeMeasure, sondeBodyHead, sondeFalse,
    sondeBindingOne, sondeHeadQ, sondeMeasure, sondeBodyHead, sondeFalse, sondeBindingTwo]

private theorem sonde_source : checkTextSonde = String.ofList (characters sondeChunks) := by
  rw [characters_join]
  cbv
private theorem sonde_unbound_source :
    "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"ext text\" expects ext }" =
      String.ofList (characters sondeUnboundChunks) := by
  rw [characters_join]
  cbv
private theorem sonde_duplicate_source :
    "impl fn g() { return; } impl fn ext() -> bool { return false; } check p { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"one\" expects ext } check q { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"two\" expects ext }" =
      String.ofList (characters sondeDuplicateChunks) := by
  rw [characters_join]
  cbv

private theorem sonde_lexed : lexL (characters sondeChunks) = .ok (tokens sondeChunks) :=
  lex_chunks sondeChunks (Nat.le_trans (steps_le_length sondeChunks (by cbv)) (Nat.le_succ _))
private theorem sonde_unbound_lexed :
    lexL (characters sondeUnboundChunks) = .ok (tokens sondeUnboundChunks) :=
  lex_chunks sondeUnboundChunks
    (Nat.le_trans (steps_le_length sondeUnboundChunks (by cbv)) (Nat.le_succ _))
private theorem sonde_duplicate_lexed :
    lexL (characters sondeDuplicateChunks) = .ok (tokens sondeDuplicateChunks) :=
  lex_chunks sondeDuplicateChunks
    (Nat.le_trans (steps_le_length sondeDuplicateChunks (by cbv)) (Nat.le_succ _))

-- Infer the complete parser results only from the actual successful equations.
private def sondeParsed : {items : List SItemTief //
    parseTopTief (tokens sondeChunks) = .ok items} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def sondeUnboundParsed : {items : List SItemTief //
    parseTopTief (tokens sondeUnboundChunks) = .ok items} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def sondeDuplicateParsed : {items : List SItemTief //
    parseTopTief (tokens sondeDuplicateChunks) = .ok items} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem sonde_text_phase : elabText checkTextSonde = elabU sondeParsed.val :=
  elabText_phases sonde_source sonde_lexed sondeParsed.property
private theorem sonde_unbound_phase :
    elabText "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"ext text\" expects ext }" =
      elabU sondeUnboundParsed.val :=
  elabText_phases sonde_unbound_source sonde_unbound_lexed sondeUnboundParsed.property
private theorem sonde_duplicate_phase :
    elabText "impl fn g() { return; } impl fn ext() -> bool { return false; } check p { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"one\" expects ext } check q { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"two\" expects ext }" =
      elabU sondeDuplicateParsed.val :=
  elabText_phases sonde_duplicate_source sonde_duplicate_lexed sondeDuplicateParsed.property

end Gabbro.Grammatik.Parser.Uebersetze
