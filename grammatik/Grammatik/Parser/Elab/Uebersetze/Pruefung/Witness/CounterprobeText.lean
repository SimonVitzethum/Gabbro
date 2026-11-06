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
    " lexemes " emitted:term " fuelUsed " count:num : command => do
  let literal : Lean.TSyntax `term := ⟨text.raw⟩
  let fuel : Lean.TSyntax `term := ⟨count.raw⟩
  let decoded := Lean.mkIdentFrom name (name.getId.appendAfter "_text")
  let bounded := Lean.mkIdentFrom name (name.getId.appendAfter "_bounded")
  let data : Lean.TSyntax `command ← `(command| private def $name : Chunk where
    characters := ($literal).toList
    tokens := $emitted
    steps := $fuel
    scanned := by intro rest remaining; cbv)
  let spelling : Lean.TSyntax `command ← `(command|
    private theorem $decoded : String.ofList ($name).characters = $literal := by
      change String.ofList (($literal).toList) = $literal
      exact String.ofList_toList)
  let room : Lean.TSyntax `command ← `(command|
    private theorem $bounded : decide (($name).steps ≤ ($name).characters.length) = true := by cbv)
  return ⟨Lean.mkNullNode #[data, spelling, room]⟩

open scoped Gabbro.Grammatik.Parser.Uebersetze

counterprobe_cut sondeGate as "impl fn g() { return; } "
  lexemes [.wort "impl", .wort "fn", .ident "g", .zeichen "(", .zeichen ")",
    .zeichen "{", .wort "return", .zeichen ";", .zeichen "}"] fuelUsed 15
counterprobe_cut sondeExternal as "impl fn ext() -> bool { return false; } "
  lexemes [.wort "impl", .wort "fn", .ident "ext", .zeichen "(", .zeichen ")",
    .zeichen "->", .wort "bool", .zeichen "{", .wort "return", .wort "false",
    .zeichen ";", .zeichen "}"] fuelUsed 21
counterprobe_cut sondeHeadP as "check p { claim "
  lexemes [.wort "check", .ident "p", .zeichen "{", .wort "claim"] fuelUsed 8
counterprobe_cut sondeHeadQ as "check q { claim "
  lexemes [.wort "check", .ident "q", .zeichen "{", .wort "claim"] fuelUsed 8
counterprobe_cut sondeMeasure as "\"c\" measures x gates g "
  lexemes [.text "c", .wort "measures", .wort "x", .wort "gates", .ident "g"] fuelUsed 10
counterprobe_cut sondeBodyHead as "can_fail { "
  lexemes [.wort "can_fail", .zeichen "{"] fuelUsed 4
counterprobe_cut sondeBinding as "let x: u64 = 3; "
  lexemes [.wort "let", .wort "x", .zeichen ":", .wort "u64", .zeichen "=",
    .num 3, .zeichen ";"] fuelUsed 12
counterprobe_cut sondeFalse as "return false; } "
  lexemes [.wort "return", .wort "false", .zeichen ";", .zeichen "}"] fuelUsed 7
counterprobe_cut sondeComparison as "return x < 0; } "
  lexemes [.wort "return", .wort "x", .zeichen "<", .num 0, .zeichen ";",
    .zeichen "}"] fuelUsed 11
counterprobe_cut sondeBindingText as "counterprobe \"ext text\" expects ext }"
  lexemes [.wort "counterprobe", .text "ext text", .wort "expects", .ident "ext",
    .zeichen "}"] fuelUsed 9
counterprobe_cut sondeBindingOne as "counterprobe \"one\" expects ext } "
  lexemes [.wort "counterprobe", .text "one", .wort "expects", .ident "ext",
    .zeichen "}"] fuelUsed 10
counterprobe_cut sondeBindingTwo as "counterprobe \"two\" expects ext }"
  lexemes [.wort "counterprobe", .text "two", .wort "expects", .ident "ext",
    .zeichen "}"] fuelUsed 9

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
  simp only [sondeChunks, List.map_cons, List.map_nil, sondeGate_text,
    sondeExternal_text, sondeHeadP_text, sondeMeasure_text, sondeBodyHead_text,
    sondeBinding_text, sondeComparison_text, sondeBindingText_text] <;> cbv
private theorem sonde_unbound_source :
    "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"ext text\" expects ext }" =
      String.ofList (characters sondeUnboundChunks) := by
  rw [characters_join]
  simp only [sondeUnboundChunks, List.map_cons, List.map_nil, sondeGate_text,
    sondeHeadP_text, sondeMeasure_text, sondeBodyHead_text, sondeFalse_text,
    sondeBindingText_text] <;> cbv
private theorem sonde_duplicate_source :
    "impl fn g() { return; } impl fn ext() -> bool { return false; } check p { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"one\" expects ext } check q { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"two\" expects ext }" =
      String.ofList (characters sondeDuplicateChunks) := by
  rw [characters_join]
  simp only [sondeDuplicateChunks, List.map_cons, List.map_nil, sondeGate_text,
    sondeExternal_text, sondeHeadP_text, sondeMeasure_text, sondeBodyHead_text,
    sondeFalse_text, sondeBindingOne_text, sondeHeadQ_text, sondeBindingTwo_text] <;> cbv

-- Certify each short fragment's room once, then compose only opaque Bool facts.
-- No List.all proof decodes a complete source or traverses its scanner payload.
private theorem sonde_bound : steps sondeChunks ≤ (characters sondeChunks).length := by
  apply steps_le_length
  simp only [sondeChunks, List.all_cons, List.all_nil, sondeGate_bounded,
    sondeExternal_bounded, sondeHeadP_bounded, sondeMeasure_bounded,
    sondeBodyHead_bounded, sondeBinding_bounded, sondeComparison_bounded,
    sondeBindingText_bounded, Bool.and_self]

private theorem sonde_unbound_bound :
    steps sondeUnboundChunks ≤ (characters sondeUnboundChunks).length := by
  apply steps_le_length
  simp only [sondeUnboundChunks, List.all_cons, List.all_nil, sondeGate_bounded,
    sondeHeadP_bounded, sondeMeasure_bounded, sondeBodyHead_bounded,
    sondeFalse_bounded, sondeBindingText_bounded, Bool.and_self]

private theorem sonde_duplicate_bound :
    steps sondeDuplicateChunks ≤ (characters sondeDuplicateChunks).length := by
  apply steps_le_length
  simp only [sondeDuplicateChunks, List.all_cons, List.all_nil, sondeGate_bounded,
    sondeExternal_bounded, sondeHeadP_bounded, sondeMeasure_bounded,
    sondeBodyHead_bounded, sondeFalse_bounded, sondeBindingOne_bounded,
    sondeHeadQ_bounded, sondeBindingTwo_bounded, Bool.and_self]

-- Adapt the canonical room certificate while every character list is symbolic.
-- Concrete applications then compare the complete lexical proposition directly,
-- without inferring Nat.le_trans's intermediate length from an expanded source.
private theorem counterprobe_lexed_of_room (chunks : List Chunk)
    (room : steps chunks ≤ (characters chunks).length) :
    lexL (characters chunks) = .ok (tokens chunks) :=
  lex_chunks chunks (Nat.le_trans room (Nat.le_succ _))

private theorem sonde_lexed : lexL (characters sondeChunks) = .ok (tokens sondeChunks) :=
  counterprobe_lexed_of_room sondeChunks sonde_bound
private theorem sonde_unbound_lexed :
    lexL (characters sondeUnboundChunks) = .ok (tokens sondeUnboundChunks) :=
  counterprobe_lexed_of_room sondeUnboundChunks sonde_unbound_bound
private theorem sonde_duplicate_lexed :
    lexL (characters sondeDuplicateChunks) = .ok (tokens sondeDuplicateChunks) :=
  counterprobe_lexed_of_room sondeDuplicateChunks sonde_duplicate_bound

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
