module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
import all Grammatik.Parser.Lex.Lexer.Teil1
import all Grammatik.Parser.Item.ElementTief.Defs5
import all Grammatik.Parser.Item.ElementTief.Defs7

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

public section
namespace Gabbro.Grammatik.Parser.Uebersetze

-- Reuse the certified gate/check/measurement prefix of the end-to-end exporter.
private def passingTail : List Char :=
  ['c', 'a', 'n', '_', 'f', 'a', 'i', 'l', ' ', '{', ' ', 'l', 'e', 't', ' ', 'x', ':', ' ',
    'u', '6', '4', ' ', '=', ' ', '3', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ' ',
    '>', '=', ' ', '2', ';', ' ', '}', ' ', 'f', 'l', 'o', 'o', 'r', ' ', 'x', ' ', '>', '=',
    ' ', '2', ' ', '}']
-- Built-in widths are vocabulary words in the actual lexer, including u64.
private def passingTailTokens : List Token :=
  [.wort "can_fail", .zeichen "{", .wort "let", .wort "x", .zeichen ":", .wort "u64",
    .zeichen "=", .num 3, .zeichen ";", .wort "return", .wort "x", .zeichen ">=",
    .num 2, .zeichen ";", .zeichen "}", .wort "floor", .wort "x", .zeichen ">=",
    .num 2, .zeichen "}"]

private theorem passing_scan (rest : List Char) (fuel : Nat) :
    scan false (passingTail ++ rest) (fuel + 36) =
      passingTailTokens.foldr (fun token result => Except.map (token :: ·) result)
        (scan false rest fuel) := by cbv

private def passingCharacters : List Char :=
  gateCharacters ++ headCharacters ++ measureCharacters 'c' 'g' ++ passingTail
private def passingTokens : List Token :=
  gateTokens ++ headTokens ++ measureTokens "c" "g" ++ passingTailTokens ++ [.ende]

private theorem passing_lexed :
    lexL passingCharacters = .ok passingTokens := by
  change scan false passingCharacters 122 = _
  have complete := scan_compose (rfl : scan false [] 53 = .ok [.ende]) (passing_scan [] 53)
  have complete := scan_compose complete (scan_measure_cg passingTail 89)
  have complete := scan_compose complete
    (scan_head (measureCharacters 'c' 'g' ++ passingTail) 99)
  have complete := scan_compose complete
    (scan_gate (headCharacters ++ measureCharacters 'c' 'g' ++ passingTail) 107)
  simpa only [passingCharacters, passingTokens, List.append_assoc, List.append_nil] using complete

private def failingTail : List Char :=
  ['c', 'a', 'n', '_', 'f', 'a', 'i', 'l', ' ', '{', ' ', 'l', 'e', 't', ' ', 'x', ':', ' ',
    'u', '6', '4', ' ', '=', ' ', '3', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ' ',
    '>', '=', ' ', '4', ';', ' ', '}', ' ', 'f', 'l', 'o', 'o', 'r', ' ', 'x', ' ', '>', '=',
    ' ', '4', ' ', '}']
private def failingTailTokens : List Token :=
  [.wort "can_fail", .zeichen "{", .wort "let", .wort "x", .zeichen ":", .wort "u64",
    .zeichen "=", .num 3, .zeichen ";", .wort "return", .wort "x", .zeichen ">=",
    .num 4, .zeichen ";", .zeichen "}", .wort "floor", .wort "x", .zeichen ">=",
    .num 4, .zeichen "}"]

private theorem failing_scan (rest : List Char) (fuel : Nat) :
    scan false (failingTail ++ rest) (fuel + 36) =
      failingTailTokens.foldr (fun token result => Except.map (token :: ·) result)
        (scan false rest fuel) := by cbv

private def failingCharacters : List Char :=
  gateCharacters ++ headCharacters ++ measureCharacters 'c' 'g' ++ failingTail
private def failingTokens : List Token :=
  gateTokens ++ headTokens ++ measureTokens "c" "g" ++ failingTailTokens ++ [.ende]

private theorem failing_lexed :
    lexL failingCharacters = .ok failingTokens := by
  change scan false failingCharacters 122 = _
  have complete := scan_compose (rfl : scan false [] 53 = .ok [.ende]) (failing_scan [] 53)
  have complete := scan_compose complete (scan_measure_cg failingTail 89)
  have complete := scan_compose complete
    (scan_head (measureCharacters 'c' 'g' ++ failingTail) 99)
  have complete := scan_compose complete
    (scan_gate (headCharacters ++ measureCharacters 'c' 'g' ++ failingTail) 107)
  simpa only [failingCharacters, failingTokens, List.append_assoc, List.append_nil] using complete

private def absentTail : List Char :=
  ['c', 'a', 'n', '_', 'f', 'a', 'i', 'l', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ',
    't', 'r', 'u', 'e', ';', ' ', '}', ' ', 'f', 'l', 'o', 'o', 'r', ' ', 'x', ' ', '>', '=',
    ' ', '2', ' ', '}']
private def absentTailTokens : List Token :=
  [.wort "can_fail", .zeichen "{", .wort "return", .wort "true", .zeichen ";", .zeichen "}",
    .wort "floor", .wort "x", .zeichen ">=", .num 2, .zeichen "}"]

private theorem absent_scan (rest : List Char) (fuel : Nat) :
    scan false (absentTail ++ rest) (fuel + 20) =
      absentTailTokens.foldr (fun token result => Except.map (token :: ·) result)
        (scan false rest fuel) := by cbv

private def absentCharacters : List Char :=
  gateCharacters ++ headCharacters ++ measureCharacters 'c' 'g' ++ absentTail
private def absentTokens : List Token :=
  gateTokens ++ headTokens ++ measureTokens "c" "g" ++ absentTailTokens ++ [.ende]

private theorem absent_lexed :
    lexL absentCharacters = .ok absentTokens := by
  change scan false absentCharacters 104 = _
  have complete := scan_compose (rfl : scan false [] 51 = .ok [.ende]) (absent_scan [] 51)
  have complete := scan_compose complete (scan_measure_cg absentTail 71)
  have complete := scan_compose complete
    (scan_head (measureCharacters 'c' 'g' ++ absentTail) 81)
  have complete := scan_compose complete
    (scan_gate (headCharacters ++ measureCharacters 'c' 'g' ++ absentTail) 89)
  simpa only [absentCharacters, absentTokens, List.append_assoc, List.append_nil] using complete

private def bypassTail : List Char :=
  ['c', 'a', 'n', '_', 'f', 'a', 'i', 'l', ' ', '{', ' ', 'l', 'e', 't', ' ', 'x', ':', ' ',
    'u', '6', '4', ' ', '=', ' ', '3', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 't', 'r',
    'u', 'e', ';', ' ', '}', ' ', 'f', 'l', 'o', 'o', 'r', ' ', 'x', ' ', '>', '=', ' ', '4',
    ' ', '}']
private def bypassTailTokens : List Token :=
  [.wort "can_fail", .zeichen "{", .wort "let", .wort "x", .zeichen ":", .wort "u64",
    .zeichen "=", .num 3, .zeichen ";", .wort "return", .wort "true", .zeichen ";",
    .zeichen "}", .wort "floor", .wort "x", .zeichen ">=", .num 4, .zeichen "}"]

private theorem bypass_scan (rest : List Char) (fuel : Nat) :
    scan false (bypassTail ++ rest) (fuel + 32) =
      bypassTailTokens.foldr (fun token result => Except.map (token :: ·) result)
        (scan false rest fuel) := by cbv

private def bypassCharacters : List Char :=
  gateCharacters ++ headCharacters ++ measureCharacters 'c' 'g' ++ bypassTail
private def bypassTokens : List Token :=
  gateTokens ++ headTokens ++ measureTokens "c" "g" ++ bypassTailTokens ++ [.ende]

private theorem bypass_lexed :
    lexL bypassCharacters = .ok bypassTokens := by
  change scan false bypassCharacters 120 = _
  have complete := scan_compose (rfl : scan false [] 55 = .ok [.ende]) (bypass_scan [] 55)
  have complete := scan_compose complete (scan_measure_cg bypassTail 87)
  have complete := scan_compose complete
    (scan_head (measureCharacters 'c' 'g' ++ bypassTail) 97)
  have complete := scan_compose complete
    (scan_gate (headCharacters ++ measureCharacters 'c' 'g' ++ bypassTail) 105)
  simpa only [bypassCharacters, bypassTokens, List.append_assoc, List.append_nil] using complete

-- The unchanged parser must certify the complete block, bound and floor.
private def floorItems (bound : Nat) (localValue compare : Bool) : List SItemTief :=
  [textGate, .checkT {
    cname := "p"
    claim := "c"
    misst := [.variable "x"]
    gates := ["g"]
    canFail := .block
      (if localValue then [.bind false "x" (some (.atom "u64")) (.lit 3)] else [])
      (some (.ret (some (if compare then .bin ">=" (.variable "x") (.lit bound) else .tru))))
    boden := [.bin ">=" (.variable "x") (.lit bound)]
    sonde := none }]

private theorem passing_parsed : parseTopTief passingTokens = .ok (floorItems 2 true true) := by cbv
private theorem failing_parsed : parseTopTief failingTokens = .ok (floorItems 4 true true) := by cbv
private theorem absent_parsed : parseTopTief absentTokens = .ok (floorItems 2 false false) := by cbv
private theorem bypass_parsed : parseTopTief bypassTokens = .ok (floorItems 4 true false) := by cbv

end Gabbro.Grammatik.Parser.Uebersetze
