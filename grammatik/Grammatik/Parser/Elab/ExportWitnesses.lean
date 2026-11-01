module
public import Grammatik.Parser.Elab.UebersetzePipeline
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportWitnesses
open Uebersetze UebersetzeAllg UebersetzeAllg2 ExportPreservation
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

def implicationCharacters : List Char := [
  'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 't',
  'r', 'u', 'e', ' ', '=', '>', ' ', 'r', 'e', 's', 'u', 'l', 't', ' ', '=', '=', ' ', '4', '2', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '4',
  '2', ';', ' ', '}']

def implicationText : String := String.ofList implicationCharacters

theorem implication_lexed : (lexL implicationCharacters).toOption.isSome = true := by decide +kernel
def implicationTokens := (lexL implicationCharacters).toOption.get implication_lexed

theorem implication_parsed : (parseTopTief implicationTokens).toOption.isSome = true := by decide +kernel
def implicationItems := (parseTopTief implicationTokens).toOption.get implication_parsed

theorem implication_elaborated : (elabU (pre108 implicationItems)).toOption.isSome = true := by decide +kernel
def implicationUnit := (elabU (pre108 implicationItems)).toOption.get implication_elaborated

theorem implication_lowered : (UebersetzeAllg2.lowerAllg implicationUnit).toOption.isSome = true := by decide +kernel

theorem implication_source_zeuge :
    (uebersetzeAllg implicationText).toOption.isSome = true := by
  have hl := except_ok_get implication_lexed
  have hp := except_ok_get implication_parsed
  have he := except_ok_get implication_elaborated
  have hw := except_ok_get implication_lowered
  have pipeline := uebersetzeAllg_von_zeichen hl hp he hw
  rw [show implicationText = String.ofList implicationCharacters from rfl, pipeline]
  rfl

def heldCharacters : List Char := [
  't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '1', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'x', ' ', ':', ' ', 'u',
  '8', ',', ' ', '}', ' ', '}', ' ', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c', 't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r',
  'a', 'n', 'k', ' ', '1', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'e', 'f',
  'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '}', ' ', '{', ' ', 'l', 'o', 'c', 'k', 's', ' ', 'L', ' ', '{', ' ',
  'l', 'e', 't', ' ', 'b', ' ', ':', ' ', 'b', 'o', 'o', 'l', ' ', '=', ' ', 'H', 'e', 'l', 'd', '(', 'L', ')', ';', ' ', '}', ' ', 'r', 'e', 't', 'u',
  'r', 'n', ' ', '4', '2', ';', ' ', '}']

def heldText : String := String.ofList heldCharacters

theorem held_lexed : (lexL heldCharacters).toOption.isSome = true := by decide +kernel
def heldTokens := (lexL heldCharacters).toOption.get held_lexed

theorem held_parsed : (parseTopTief heldTokens).toOption.isSome = true := by decide +kernel
def heldItems := (parseTopTief heldTokens).toOption.get held_parsed

theorem held_elaborated : (elabU (pre108 heldItems)).toOption.isSome = true := by decide +kernel
def heldUnit := (elabU (pre108 heldItems)).toOption.get held_elaborated

theorem held_lowered : (UebersetzeAllg2.lowerAllg heldUnit).toOption.isSome = true := by decide +kernel

theorem held_source_zeuge :
    (uebersetzeAllg heldText).toOption.isSome = true := by
  have hl := except_ok_get held_lexed
  have hp := except_ok_get held_parsed
  have he := except_ok_get held_elaborated
  have hw := except_ok_get held_lowered
  have pipeline := uebersetzeAllg_von_zeichen hl hp he hw
  rw [show heldText = String.ofList heldCharacters from rfl, pipeline]
  rfl

def nestedElseCharacters : List Char := [
  'r', 'e', 'a', 's', 'o', 'n', ' ', 'R', ' ', '{', ' ', 'B', 'a', 'd', ' ', '=', ' ', '7', ' ', '"', 'b', 'a', 'd', '"', ' ', 'e', 'x', 'h', 'a', 'u',
  's', 't', 'i', 'v', 'e', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'f', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'o', 'r', ' ', 'R',
  ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'R', ':', ':', 'B', 'a', 'd', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a',
  'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', '{', ' ', 'l', 'e', 't', ' ', 'a', ' ', '=', ' ', 'f', '(', ')', ' ', 'e', 'l', 's', 'e', ' ',
  '(', 'e', ')', ' ', '{', ' ', 'l', 'e', 't', ' ', 'b', ' ', '=', ' ', 'f', '(', ')', ' ', 'e', 'l', 's', 'e', ' ', '(', 'q', ')', ' ', '{', ' ', 'r',
  'e', 't', 'u', 'r', 'n', ' ', '4', '2', ';', ' ', '}', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'b', ';', ' ', '}', ' ', 'r', 'e', 't', 'u', 'r', 'n',
  ' ', 'a', ';', ' ', '}']

def nestedElseText : String := String.ofList nestedElseCharacters

theorem nestedElse_lexed : (lexL nestedElseCharacters).toOption.isSome = true := by decide +kernel
def nestedElseTokens := (lexL nestedElseCharacters).toOption.get nestedElse_lexed

theorem nestedElse_parsed : (parseTopTief nestedElseTokens).toOption.isSome = true := by decide +kernel
def nestedElseItems := (parseTopTief nestedElseTokens).toOption.get nestedElse_parsed

theorem nestedElse_elaborated : (elabU (pre108 nestedElseItems)).toOption.isSome = true := by decide +kernel
def nestedElseUnit := (elabU (pre108 nestedElseItems)).toOption.get nestedElse_elaborated

theorem nestedElse_lowered : (UebersetzeAllg2.lowerAllg nestedElseUnit).toOption.isSome = true := by decide +kernel

theorem nestedElse_source_zeuge :
    (uebersetzeAllg nestedElseText).toOption.isSome = true := by
  have hl := except_ok_get nestedElse_lexed
  have hp := except_ok_get nestedElse_parsed
  have he := except_ok_get nestedElse_elaborated
  have hw := except_ok_get nestedElse_lowered
  have pipeline := uebersetzeAllg_von_zeichen hl hp he hw
  rw [show nestedElseText = String.ofList nestedElseCharacters from rfl, pipeline]
  rfl

def resultScopeCharacters : List Char := [
  'm', 'o', 'd', 'u', 'l', 'e', ' ', 'i', 'r', '_', 'r', 'e', 's', 'u', 'l', 't', '_', 'q', 'u', 'a', 'n', 't', 'i', 'f', 'i', 'e', 'r', ' ', '{', '\n',
  't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'r', 'e', 'a', 'd', 'y',
  ' ', ':', ' ', 'b', 'o', 'o', 'l', ',', ' ', '}', ' ', '}', '\n', '\n', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-',
  '>', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ',
  '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '}', '\n', ' ', ' ', ' ', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ',
  'f', 'o', 'r', 'a', 'l', 'l', ' ', 'i', ' ', 'i', 'n', ' ', 's', 'l', 'o', 't', 's', ' ', 'o', 'f', ' ', 'T', ' ', ':', ' ', '!', 'T', '.', 's', 'l',
  'o', 't', 's', '[', 'i', ']', '.', 'r', 'e', 'a', 'd', 'y', '\n', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'S', 'o', 'm', 'e', '(', '1', ')', ';',
  ' ', '}', '\n', '}', '\n']

def resultScopeText : String := String.ofList resultScopeCharacters

theorem resultScope_lexed : (lexL resultScopeCharacters).toOption.isSome = true := by decide +kernel
def resultScopeTokens := (lexL resultScopeCharacters).toOption.get resultScope_lexed

theorem resultScope_parsed : (parseTopTief resultScopeTokens).toOption.isSome = true := by decide +kernel
def resultScopeItems := (parseTopTief resultScopeTokens).toOption.get resultScope_parsed

theorem resultScope_elaborated : (elabU (pre108 resultScopeItems)).toOption.isSome = true := by decide +kernel
def resultScopeUnit := (elabU (pre108 resultScopeItems)).toOption.get resultScope_elaborated

theorem resultScope_lowered : (UebersetzeAllg2.lowerAllg resultScopeUnit).toOption.isSome = true := by decide +kernel

theorem resultScope_source_zeuge :
    (uebersetzeAllg resultScopeText).toOption.isSome = true := by
  have hl := except_ok_get resultScope_lexed
  have hp := except_ok_get resultScope_parsed
  have he := except_ok_get resultScope_elaborated
  have hw := except_ok_get resultScope_lowered
  have pipeline := uebersetzeAllg_von_zeichen hl hp he hw
  rw [show resultScopeText = String.ofList resultScopeCharacters from rfl, pipeline]
  rfl

end Gabbro.Grammatik.Parser.ExportWitnesses
