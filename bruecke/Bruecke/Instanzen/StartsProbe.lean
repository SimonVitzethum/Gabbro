module
public import Bruecke.Kette.Quelle
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben2
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
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


/-! Wall 7 witness on the bridge side: an `entry` really becomes a declared start of `einheitAllg`
(the statement of `nutzer_aus_quelleG` is then about a unit WITH a thread root, not about the empty
start list), and a unit without an entry keeps none. -/

namespace Gabbro.Bruecke

open Gabbro.Grammatik.Parser.UebersetzeProben2 Gabbro.Grammatik.Parser.UebersetzeProben3
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

private theorem starts_after {source : String} {characters : List Char} {tokens : List Token}
    {items : List SItemTief} (count : Nat)
    (text : source = String.ofList characters) (lexed : lexL characters = .ok tokens)
    (parsed : parseTopTief tokens = .ok items)
    (made : ∃ unit : UProg, elabU (pre108 items) = .ok unit ∧ (startsAllg unit).length = count)
    (accepted : UebersetzeProben2.stufe source = "OK") :
    (uOf source).map (fun unit => (startsAllg unit).length) = some count := by
  obtain ⟨unit, elaborated, counted⟩ := made
  have finished : lowerStage unit = "OK" :=
    (stufe_phases text lexed parsed elaborated rfl).symm.trans accepted
  cases lowered : lowerAllg unit with
  | error message =>
    simp only [lowerStage, lowered] at finished
    have lengths := congrArg String.length finished
    simp only [String.length_append] at lengths
    change 7 + message.length = 2 at lengths
    omega
  | ok result =>
    rcases result with ⟨program, functions⟩
    have compiled := uebersetzeAllg_von_zeichen lexed parsed elaborated lowered
    rw [← text] at compiled
    unfold uOf
    rw [compiled]
    exact congrArg some counted

@[expose] public section

theorem entry_ist_start :
    (uOf entry1_ok).map (fun u => (startsAllg u).length) = some 1 := by
  apply starts_after (source := entry1_ok) (items := entry1_ok_items) 1
    entry1_ok_text entry1_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief entry1_ok_tokens) entry1_ok_parsed) ?_
    ((congrFun (show UebersetzeProben2.stufe = UebersetzeProben3.stufe from rfl)
      entry1_ok).trans entry1_ok_stufe)
  refine ⟨?unit, ?elaborated, ?counted⟩
  case elaborated => cbv <;> exact Eq.refl _
  case counted => cbv

theorem zwei_entries_zwei_starts :
    (uOf entry_two_ok).map (fun u => (startsAllg u).length) = some 2 := by
  apply starts_after (source := entry_two_ok) (items := entry_two_ok_items) 2
    entry_two_ok_text entry_two_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief entry_two_ok_tokens) entry_two_ok_parsed) ?_
    ((congrFun (show UebersetzeProben2.stufe = UebersetzeProben3.stufe from rfl)
      entry_two_ok).trans entry_two_ok_stufe)
  refine ⟨?unit, ?elaborated, ?counted⟩
  case elaborated => cbv <;> exact Eq.refl _
  case counted => cbv

theorem ohne_entry_kein_start :
    (uOf locks1_ok).map (fun u => (startsAllg u).length) = some 0 := by
  have parsed : (parseTopTief locks1_ok_tokens).toOption.isSome = true := by cbv
  apply starts_after (source := locks1_ok) (characters := locks1_ok_characters) 0
    (by cbv) locks1_ok_lexed
    (except_ok_get (ε := String) (α := List SItemTief)
      (x := parseTopTief locks1_ok_tokens) parsed) ?_ locks1_ok_stufe
  refine ⟨?unit, ?elaborated, ?counted⟩
  case elaborated => cbv <;> exact Eq.refl _
  case counted => cbv

#print axioms entry_ist_start

end

end Gabbro.Bruecke
