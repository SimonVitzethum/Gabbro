import Grammatik.Parser.Elab.ExportQuantifiers
import Grammatik.Parser.Elab.ExportComparisons
import Grammatik.Parser.Elab.ExportArrays

namespace Gabbro.Grammatik.Parser.ExportWitnesses2
open Uebersetze UebersetzeAllg UebersetzeAllg2 ExportPreservation
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

def countCharacters : List Char := [
  'm', 'o', 'd', 'u', 'l', 'e', ' ', 'i', 'r', '_', 'c', 'o', 'n', 's', 't', 'a', 'n', 't', '_', 'h', 'e', 'a',
  'd', 'e', 'r', 's', ' ', '{', '\n', 'c', 'o', 'n', 's', 't', ' ', 'N', ' ', ':', ' ', 'u', '8', ' ', '=', ' ',
  '1', ';', '\n', 'c', 'o', 'n', 's', 't', ' ', 'R', 'A', 'N', 'K', ' ', ':', ' ', 'u', '8', ' ', '=', ' ', '2',
  ';', '\n', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '(', 'N', ' ', '+', ' ', '1',
  ')', ' ', '*', ' ', '2', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', 'a', 'l', 'u', 'e', ' ', ':',
  ' ', 'u', '8', ',', ' ', '}', ' ', '}', '\n', 'l', 'o', 'c', 'k', ' ', 'L', ' ', 'p', 'r', 'o', 't', 'e', 'c',
  't', 's', ' ', '{', ' ', 'T', ' ', '}', ' ', 'r', 'a', 'n', 'k', ' ', 'R', 'A', 'N', 'K', ' ', '+', ' ', '1',
  ';', '\n', 's', 't', 'a', 't', 'i', 'c', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ' ', ':', ' ', 'u', '8', ' ', '=',
  ' ', '(', '2', '0', ' ', '+', ' ', '1', ')', ' ', '*', ' ', '2', ';', '\n', 'i', 'm', 'p', 'l', ' ', 'f', 'n',
  ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ',
  '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ' ', '}', ' ', '{', ' ', 'r', 'e', 't',
  'u', 'r', 'n', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ';', ' ', '}', '\n', '}', '\n']

def countText : String := String.ofList countCharacters

theorem count_lexed : (lexL countCharacters).toOption.isSome = true := by decide +kernel
def countTokens := (lexL countCharacters).toOption.get count_lexed

theorem count_parsed : (parseTopTief countTokens).toOption.isSome = true := by decide +kernel
def countItems := (parseTopTief countTokens).toOption.get count_parsed

theorem count_elaborated : (elabU (pre108 countItems)).toOption.isSome = true := by decide +kernel
def countUnit := (elabU (pre108 countItems)).toOption.get count_elaborated

theorem count_lowered : (UebersetzeAllg2.lowerAllg countUnit).toOption.isSome = true := by decide +kernel

theorem count_source_zeuge : (uebersetzeAllg countText).toOption.isSome = true := by
  have lexed := except_ok_get count_lexed
  have parsed := except_ok_get count_parsed
  have elaborated := except_ok_get count_elaborated
  have lowered := except_ok_get count_lowered
  have pipeline := uebersetzeAllg_von_zeichen lexed parsed elaborated lowered
  rw [show countText = String.ofList countCharacters from rfl, pipeline]
  rfl

def relationsCharacters : List Char := [
  'm', 'o', 'd', 'u', 'l', 'e', ' ', 'i', 'r', '_', 'm', 'e', 'm', 'b', 'e', 'r', '_', 'r', 'e', 'a', 'c', 'h',
  ' ', '{', '\n', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't', ' ', '3', ' ', '{', ' ', 's',
  'l', 'o', 't', ' ', '{', ' ', 'n', 'e', 'x', 't', ' ', ':', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n',
  'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'e', 'l', 'f', ',', ' ', '}', ' ', '}', '\n', 'i', 'm', 'p',
  'l', ' ', 'f', 'n', ' ', 'q', 'u', 'e', 'r', 'y', '(', 'a', ' ', ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i',
  'n', 't', 'o', ' ', 'T', ',', ' ', 'b', ' ', ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ',
  'T', ')', ' ', '-', '>', ' ', 'u', '8', '\n', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e',
  'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '}', '\n', ' ', 'r', 'e', 'q', 'u', 'i', 'r', 'e',
  's', ' ', 'a', ' ', 'i', 'n', ' ', 's', 'l', 'o', 't', 's', ' ', 'o', 'f', ' ', 'T', '\n', ' ', 'r', 'e', 'q',
  'u', 'i', 'r', 'e', 's', ' ', 'a', ' ', 'r', 'e', 'a', 'c', 'h', 'e', 's', ' ', 'b', ' ', 'v', 'i', 'a', ' ',
  'n', 'e', 'x', 't', '\n', ' ', 'r', 'e', 'q', 'u', 'i', 'r', 'e', 's', ' ', '!', '(', 'b', ' ', 'r', 'e', 'a',
  'c', 'h', 'e', 's', ' ', 'a', ' ', 'v', 'i', 'a', ' ', 'n', 'e', 'x', 't', ')', '\n', ' ', 'e', 'n', 's', 'u',
  'r', 'e', 's', ' ', 'r', 'e', 's', 'u', 'l', 't', ' ', '=', '=', ' ', '4', '2', '\n', ' ', '{', ' ', 'r', 'e',
  't', 'u', 'r', 'n', ' ', '4', '2', ';', ' ', '}', '\n', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i',
  'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e',
  'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'w', 'r', 'i', 't', 'e', 's', ' ', 'T', '.',
  's', 'l', 'o', 't', 's', ' ', '}', ' ', '{', '\n', ' ', 'T', '.', 's', 'l', 'o', 't', 's', '[', '0', ']', '.',
  'n', 'e', 'x', 't', ' ', '=', ' ', 'S', 'o', 'm', 'e', '(', '1', ')', ';', '\n', ' ', 'T', '.', 's', 'l', 'o',
  't', 's', '[', '1', ']', '.', 'n', 'e', 'x', 't', ' ', '=', ' ', 'S', 'o', 'm', 'e', '(', '2', ')', ';', '\n',
  ' ', 'l', 'e', 't', ' ', 'a', 'n', 's', 'w', 'e', 'r', ' ', '=', ' ', 'q', 'u', 'e', 'r', 'y', '(', '0', ',',
  ' ', '2', ')', ';', '\n', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'a', 'n', 's', 'w', 'e', 'r', ';', '\n', '}',
  '\n', '}', '\n']

def relationsText : String := String.ofList relationsCharacters

theorem relations_lexed : (lexL relationsCharacters).toOption.isSome = true := by decide +kernel
def relationsTokens := (lexL relationsCharacters).toOption.get relations_lexed

theorem relations_parsed : (parseTopTief relationsTokens).toOption.isSome = true := by decide +kernel
def relationsItems := (parseTopTief relationsTokens).toOption.get relations_parsed

theorem relations_elaborated : (elabU (pre108 relationsItems)).toOption.isSome = true := by decide +kernel
def relationsUnit := (elabU (pre108 relationsItems)).toOption.get relations_elaborated

theorem relations_lowered : (UebersetzeAllg2.lowerAllg relationsUnit).toOption.isSome = true := by decide +kernel

theorem relations_source_zeuge : (uebersetzeAllg relationsText).toOption.isSome = true := by
  have lexed := except_ok_get relations_lexed
  have parsed := except_ok_get relations_parsed
  have elaborated := except_ok_get relations_elaborated
  have lowered := except_ok_get relations_lowered
  have pipeline := uebersetzeAllg_von_zeichen lexed parsed elaborated lowered
  rw [show relationsText = String.ofList relationsCharacters from rfl, pipeline]
  rfl

def treeCharacters : List Char := [
  'm', 'o', 'd', 'u', 'l', 'e', ' ', 'i', 'r', '_', 't', 'r', 'e', 'e', '_', 'b', 'i', 'n', 'd', 'e', 'r', '_',
  's', 'h', 'a', 'd', 'o', 'w', ' ', '{', '\n', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u', 'n', 't',
  ' ', '3', ' ', '{', ' ', 't', 'r', 'e', 'e', ' ', '{', ' ', 'c', 'h', 'i', 'l', 'd', ' ', 'n', 'e', 'x', 't',
  ' ', '}', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'n', 'e', 'x', 't', ' ', ':', ' ', 'o', 'p', 't', 'i', 'o',
  'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'e', 'l', 'f', ',', ' ', '}', ' ', '}',
  '\n', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'q', 'u', 'e', 'r', 'y', '(', 'r', 'o', 'o', 't', ' ', ':', ' ',
  'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'e', 'f',
  'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ',
  '}', '\n', ' ', 'r', 'e', 'q', 'u', 'i', 'r', 'e', 's', ' ', 'f', 'o', 'r', 'a', 'l', 'l', ' ', 'r', 'o', 'o',
  't', ' ', 'i', 'n', ' ', 'd', 'e', 's', 'c', 'e', 'n', 'd', 'a', 'n', 't', 's', ' ', 'o', 'f', ' ', 'r', 'o',
  'o', 't', ' ', ':', ' ', 'r', 'o', 'o', 't', ' ', '<', '=', ' ', '1', '\n', ' ', 'r', 'e', 'q', 'u', 'i', 'r',
  'e', 's', ' ', 'e', 'x', 'i', 's', 't', 's', ' ', 'n', 'o', 'd', 'e', ' ', 'i', 'n', ' ', 'a', 'n', 'c', 'e',
  's', 't', 'o', 'r', 's', ' ', 'o', 'f', ' ', 'r', 'o', 'o', 't', ' ', ':', ' ', 'n', 'o', 'd', 'e', ' ', '=',
  '=', ' ', '0', '\n', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'r', 'e', 's', 'u', 'l', 't', ' ', '=', '=',
  ' ', '4', '2', '\n', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '4', '2', ';', ' ', '}', '\n', 'i', 'm',
  'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'e', 'f', 'f',
  'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ',', ' ',
  'w', 'r', 'i', 't', 'e', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' ', '{', '\n', ' ', 'T', '.',
  's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'n', 'e', 'x', 't', ' ', '=', ' ', 'S', 'o', 'm', 'e', '(', '1',
  ')', ';', '\n', ' ', 'l', 'e', 't', ' ', 'a', 'n', 's', 'w', 'e', 'r', ' ', '=', ' ', 'q', 'u', 'e', 'r', 'y',
  '(', '1', ')', ';', '\n', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'a', 'n', 's', 'w', 'e', 'r', ';', '\n', '}',
  '\n', '}', '\n']

def treeText : String := String.ofList treeCharacters

theorem tree_lexed : (lexL treeCharacters).toOption.isSome = true := by decide +kernel
def treeTokens := (lexL treeCharacters).toOption.get tree_lexed

theorem tree_parsed : (parseTopTief treeTokens).toOption.isSome = true := by decide +kernel
def treeItems := (parseTopTief treeTokens).toOption.get tree_parsed

theorem tree_elaborated : (elabU (pre108 treeItems)).toOption.isSome = true := by decide +kernel
def treeUnit := (elabU (pre108 treeItems)).toOption.get tree_elaborated

theorem tree_lowered : (UebersetzeAllg2.lowerAllg treeUnit).toOption.isSome = true := by decide +kernel

theorem tree_source_zeuge : (uebersetzeAllg treeText).toOption.isSome = true := by
  have lexed := except_ok_get tree_lexed
  have parsed := except_ok_get tree_parsed
  have elaborated := except_ok_get tree_elaborated
  have lowered := except_ok_get tree_lowered
  have pipeline := uebersetzeAllg_von_zeichen lexed parsed elaborated lowered
  rw [show treeText = String.ofList treeCharacters from rfl, pipeline]
  rfl

def stringsCharacters : List Char := [
  'm', 'o', 'd', 'u', 'l', 'e', ' ', 'i', 'r', '_', 's', 'h', 'o', 'r', 't', '_', 's', 't', 'r', 'i', 'n', 'g',
  '_', 'c', 'o', 'm', 'p', 'a', 'r', 'i', 's', 'o', 'n', 's', ' ', '{', '\n', 'i', 'm', 'p', 'l', ' ', 'f', 'n',
  ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'e', 'f', 'f', 'e', 'c', 't', 's', ' ',
  '{', ' ', 'p', 'u', 'r', 'e', ' ', '}', ' ', '{', '\n', ' ', ' ', ' ', ' ', 'l', 'e', 't', ' ', 'e', 'm', 'p',
  't', 'y', ' ', ':', ' ', 's', 't', 'r', 'i', 'n', 'g', ' ', 'm', 'a', 'x', ' ', '1', ' ', '=', ' ', '"', '"',
  ';', '\n', ' ', ' ', ' ', ' ', 'l', 'e', 't', ' ', 'f', 'i', 'r', 's', 't', ' ', ':', ' ', 's', 't', 'r', 'i',
  'n', 'g', ' ', 'm', 'a', 'x', ' ', '1', ' ', '=', ' ', '"', 'A', '"', ';', '\n', ' ', ' ', ' ', ' ', 'l', 'e',
  't', ' ', 's', 'e', 'c', 'o', 'n', 'd', ' ', ':', ' ', 's', 't', 'r', 'i', 'n', 'g', ' ', 'm', 'a', 'x', ' ',
  '1', ' ', '=', ' ', '"', 'B', '"', ';', '\n', ' ', ' ', ' ', ' ', 'i', 'f', ' ', 'e', 'm', 'p', 't', 'y', ' ',
  '<', ' ', 'f', 'i', 'r', 's', 't', ' ', '{', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', 'i', 'f', ' ', 'f',
  'i', 'r', 's', 't', ' ', '!', '=', ' ', 's', 'e', 'c', 'o', 'n', 'd', ' ', '{', '\n', ' ', ' ', ' ', ' ', ' ',
  ' ', ' ', ' ', ' ', ' ', ' ', ' ', 'i', 'f', ' ', 'f', 'i', 'r', 's', 't', ' ', '<', '=', ' ', 's', 'e', 'c',
  'o', 'n', 'd', ' ', '{', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ',
  'i', 'f', ' ', 's', 'e', 'c', 'o', 'n', 'd', ' ', '>', ' ', 'f', 'i', 'r', 's', 't', ' ', '{', '\n', ' ', ' ',
  ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', 'i', 'f', ' ', 's',
  'e', 'c', 'o', 'n', 'd', ' ', '>', '=', ' ', 'f', 'i', 'r', 's', 't', ' ', '{', '\n', ' ', ' ', ' ', ' ', ' ',
  ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', 'i', 'f', ' ',
  'f', 'i', 'r', 's', 't', ' ', '=', '=', ' ', 'f', 'i', 'r', 's', 't', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r',
  'n', ' ', '4', '2', ';', ' ', '}', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ',
  ' ', ' ', ' ', ' ', ' ', ' ', '}', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ',
  ' ', ' ', '}', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '}', '\n', ' ', ' ', ' ', ' ',
  ' ', ' ', ' ', ' ', '}', '\n', ' ', ' ', ' ', ' ', '}', '\n', ' ', ' ', ' ', ' ', 'r', 'e', 't', 'u', 'r', 'n',
  ' ', '1', ';', '\n', '}', '\n', '}', '\n']

def stringsText : String := String.ofList stringsCharacters

theorem strings_lexed : (lexL stringsCharacters).toOption.isSome = true := by decide +kernel
def stringsTokens := (lexL stringsCharacters).toOption.get strings_lexed

theorem strings_parsed : (parseTopTief stringsTokens).toOption.isSome = true := by decide +kernel
def stringsItems := (parseTopTief stringsTokens).toOption.get strings_parsed

theorem strings_elaborated : (elabU (pre108 stringsItems)).toOption.isSome = true := by decide +kernel
def stringsUnit := (elabU (pre108 stringsItems)).toOption.get strings_elaborated

theorem strings_lowered : (UebersetzeAllg2.lowerAllg stringsUnit).toOption.isSome = true := by decide +kernel

theorem strings_source_zeuge : (uebersetzeAllg stringsText).toOption.isSome = true := by
  have lexed := except_ok_get strings_lexed
  have parsed := except_ok_get strings_parsed
  have elaborated := except_ok_get strings_elaborated
  have lowered := except_ok_get strings_lowered
  have pipeline := uebersetzeAllg_von_zeichen lexed parsed elaborated lowered
  rw [show stringsText = String.ofList stringsCharacters from rfl, pipeline]
  rfl

def arraysCharacters : List Char := [
  'c', 'o', 'n', 's', 't', ' ', 'D', 'A', 'T', 'A', ' ', ':', ' ', '[', 'u', '8', ';', ' ', '2', ']', ' ', '=',
  ' ', '[', '4', '0', ',', ' ', '4', '2', ']', ';', '\n', 'c', 'o', 'n', 's', 't', ' ', 'j', ' ', ':', ' ', 'u',
  '8', ' ', '=', ' ', '9', '9', ';', '\n', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')',
  ' ', '-', '>', ' ', 'u', '8', '\n', ' ', 'r', 'e', 'q', 'u', 'i', 'r', 'e', 's', ' ', 'f', 'o', 'r', 'a', 'l',
  'l', ' ', 'j', ' ', 'i', 'n', ' ', 'e', 'l', 'e', 'm', 's', ' ', 'o', 'f', ' ', 'D', 'A', 'T', 'A', ' ', ':',
  ' ', 'j', ' ', '<', ' ', '2', '\n', ' ', 'r', 'e', 'q', 'u', 'i', 'r', 'e', 's', ' ', 'e', 'x', 'i', 's', 't',
  's', ' ', 'k', ' ', 'i', 'n', ' ', 'e', 'l', 'e', 'm', 's', ' ', 'o', 'f', ' ', 'D', 'A', 'T', 'A', ' ', ':',
  ' ', 'D', 'A', 'T', 'A', '[', 'k', ']', ' ', '=', '=', ' ', '4', '2', '\n', ' ', 'r', 'e', 'q', 'u', 'i', 'r',
  'e', 's', ' ', 'j', ' ', '=', '=', ' ', '9', '9', '\n', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'f', 'o',
  'r', 'a', 'l', 'l', ' ', 'j', ' ', 'i', 'n', ' ', 'e', 'l', 'e', 'm', 's', ' ', 'o', 'f', ' ', 'D', 'A', 'T',
  'A', ' ', ':', ' ', 'D', 'A', 'T', 'A', '[', 'j', ']', ' ', '<', '=', ' ', 'r', 'e', 's', 'u', 'l', 't', '\n',
  ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '4', '2', ';', ' ', '}', '\n']

def arraysText : String := String.ofList arraysCharacters

theorem arrays_lexed : (lexL arraysCharacters).toOption.isSome = true := by decide +kernel
def arraysTokens := (lexL arraysCharacters).toOption.get arrays_lexed

theorem arrays_parsed : (parseTopTief arraysTokens).toOption.isSome = true := by decide +kernel
def arraysItems := (parseTopTief arraysTokens).toOption.get arrays_parsed

theorem arrays_elaborated : (elabU (pre108 arraysItems)).toOption.isSome = true := by decide +kernel
def arraysUnit := (elabU (pre108 arraysItems)).toOption.get arrays_elaborated

theorem arrays_lowered : (UebersetzeAllg2.lowerAllg arraysUnit).toOption.isSome = true := by decide +kernel

theorem arrays_source_zeuge : (uebersetzeAllg arraysText).toOption.isSome = true := by
  have lexed := except_ok_get arrays_lexed
  have parsed := except_ok_get arrays_parsed
  have elaborated := except_ok_get arrays_elaborated
  have lowered := except_ok_get arrays_lowered
  have pipeline := uebersetzeAllg_von_zeichen lexed parsed elaborated lowered
  rw [show arraysText = String.ofList arraysCharacters from rfl, pipeline]
  rfl

def treeTraversalCharacters : List Char := [
  'm', 'o', 'd', 'u', 'l', 'e', ' ', 'i', 'r', '_', 't', 'r', 'e', 'e', '_', 't', 'r', 'a', 'v', 'e', 'r', 's',
  'a', 'l', '_', 'e', 'x', 'i', 't', 's', ' ', '{', '\n', 't', 'a', 'b', 'l', 'e', ' ', 'T', ' ', 'c', 'o', 'u',
  'n', 't', ' ', '3', ' ', '{', ' ', 't', 'r', 'e', 'e', ' ', '{', ' ', 'c', 'h', 'i', 'l', 'd', ' ', 'n', 'e',
  'x', 't', ' ', '}', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'n', 'e', 'x', 't', ' ', ':', ' ', 'o', 'p', 't',
  'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'e', 'l', 'f', ',', ' ', '}',
  ' ', '}', '\n', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'q', 'u', 'e', 'r', 'y', '(', 'r', 'o', 'o', 't', ' ',
  ':', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'T', ')', ' ', '-', '>', ' ', 'u', '8', ' ',
  'e', 'f', 'f', 'e', 'c', 't', 's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't',
  's', ' ', '}', ' ', '{', '\n', ' ', ' ', ' ', ' ', 'l', 'e', 't', ' ', 'm', 'u', 't', ' ', 'a', 'n', 's', 'w',
  'e', 'r', ' ', ':', ' ', 'u', '8', ' ', '=', ' ', '0', ';', '\n', ' ', ' ', ' ', ' ', 't', 'r', 'a', 'v', 'e',
  'r', 's', 'e', ' ', 'n', 'o', 'd', 'e', ' ', 'o', 'f', ' ', 'r', 'o', 'o', 't', ' ', 'o', 'v', 'e', 'r', ' ',
  'd', 'e', 's', 'c', 'e', 'n', 'd', 'a', 'n', 't', 's', ' ', 'o', 'f', ' ', 'r', 'o', 'o', 't', ' ', 'b', 'y',
  ' ', 'u', 'n', 'v', 'i', 's', 'i', 't', 'e', 'd', ' ', 'i', 'n', 'v', 'a', 'r', 'i', 'a', 'n', 't', ' ', 'a',
  'n', 's', 'w', 'e', 'r', ' ', '<', '=', ' ', '4', '2', ' ', '{', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ',
  'i', 'f', ' ', 'n', 'o', 'd', 'e', ' ', '=', '=', ' ', '0', ' ', '{', ' ', 'n', 'e', 'x', 't', ' ', 'n', 'o',
  'd', 'e', ';', ' ', '}', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', 'i', 'f', ' ', 'n', 'o', 'd', 'e', ' ',
  '=', '=', ' ', '1', ' ', '{', ' ', 'a', 'n', 's', 'w', 'e', 'r', ' ', '=', ' ', '4', '2', ';', ' ', 'l', 'e',
  'a', 'v', 'e', ' ', 'n', 'o', 'd', 'e', ';', ' ', '}', '\n', ' ', ' ', ' ', ' ', '}', '\n', ' ', ' ', ' ', ' ',
  'r', 'e', 't', 'u', 'r', 'n', ' ', 'a', 'n', 's', 'w', 'e', 'r', ';', '\n', '}', '\n', 'i', 'm', 'p', 'l', ' ',
  'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'e', 'f', 'f', 'e', 'c', 't',
  's', ' ', '{', ' ', 'r', 'e', 'a', 'd', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ',', ' ', 'w', 'r', 'i',
  't', 'e', 's', ' ', 'T', '.', 's', 'l', 'o', 't', 's', ' ', '}', ' ', '{', '\n', ' ', ' ', ' ', ' ', 'T', '.',
  's', 'l', 'o', 't', 's', '[', '0', ']', '.', 'n', 'e', 'x', 't', ' ', '=', ' ', 'S', 'o', 'm', 'e', '(', '1',
  ')', ';', '\n', ' ', ' ', ' ', ' ', 'l', 'e', 't', ' ', 'a', 'n', 's', 'w', 'e', 'r', 'F', 'r', 'o', 'm', 'C',
  'a', 'l', 'l', ' ', '=', ' ', 'q', 'u', 'e', 'r', 'y', '(', '0', ')', ';', '\n', ' ', ' ', ' ', ' ', 'r', 'e',
  't', 'u', 'r', 'n', ' ', 'a', 'n', 's', 'w', 'e', 'r', 'F', 'r', 'o', 'm', 'C', 'a', 'l', 'l', ';', '\n', '}',
  '\n', '}', '\n']

def treeTraversalText : String := String.ofList treeTraversalCharacters

theorem treeTraversal_lexed : (lexL treeTraversalCharacters).toOption.isSome = true := by decide +kernel
def treeTraversalTokens := (lexL treeTraversalCharacters).toOption.get treeTraversal_lexed

theorem treeTraversal_parsed : (parseTopTief treeTraversalTokens).toOption.isSome = true := by decide +kernel
def treeTraversalItems := (parseTopTief treeTraversalTokens).toOption.get treeTraversal_parsed

theorem treeTraversal_elaborated : (elabU (pre108 treeTraversalItems)).toOption.isSome = true := by decide +kernel
def treeTraversalUnit := (elabU (pre108 treeTraversalItems)).toOption.get treeTraversal_elaborated

theorem treeTraversal_lowered : (UebersetzeAllg2.lowerAllg treeTraversalUnit).toOption.isSome = true := by decide +kernel

theorem treeTraversal_source_zeuge : (uebersetzeAllg treeTraversalText).toOption.isSome = true := by
  have lexed := except_ok_get treeTraversal_lexed
  have parsed := except_ok_get treeTraversal_parsed
  have elaborated := except_ok_get treeTraversal_elaborated
  have lowered := except_ok_get treeTraversal_lowered
  have pipeline := uebersetzeAllg_von_zeichen lexed parsed elaborated lowered
  rw [show treeTraversalText = String.ofList treeTraversalCharacters from rfl, pipeline]
  rfl

def arrayTraversalCharacters : List Char := [
  'c', 'o', 'n', 's', 't', ' ', 'D', 'A', 'T', 'A', ' ', ':', ' ', '[', 'u', '8', ';', ' ', '3', ']', ' ', '=',
  ' ', '[', '9', ',', ' ', '4', '2', ',', ' ', '8', ']', ';', '\n', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm',
  'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', '{', '\n', ' ', 'l', 'e', 't', ' ', 'd', 'a', 't',
  'a', ' ', ':', ' ', '[', 'u', '8', ';', ' ', '3', ']', ' ', '=', ' ', 'D', 'A', 'T', 'A', ';', '\n', ' ', 'l',
  'e', 't', ' ', 'm', 'u', 't', ' ', 'a', 'n', 's', 'w', 'e', 'r', ' ', ':', ' ', 'u', '8', ' ', '=', ' ', '0',
  ';', '\n', ' ', 't', 'r', 'a', 'v', 'e', 'r', 's', 'e', ' ', 'j', ' ', 'o', 'v', 'e', 'r', ' ', 'e', 'l', 'e',
  'm', 's', ' ', 'o', 'f', ' ', 'd', 'a', 't', 'a', ' ', 'b', 'y', ' ', 'u', 'n', 'v', 'i', 's', 'i', 't', 'e',
  'd', ' ', 'i', 'n', 'v', 'a', 'r', 'i', 'a', 'n', 't', ' ', 'a', 'n', 's', 'w', 'e', 'r', ' ', '<', '=', ' ',
  '4', '2', ' ', '{', '\n', ' ', ' ', ' ', 'i', 'f', ' ', 'j', ' ', '=', '=', ' ', '0', ' ', '{', ' ', 'n', 'e',
  'x', 't', ' ', 'j', ';', ' ', '}', '\n', ' ', ' ', ' ', 'i', 'f', ' ', 'd', 'a', 't', 'a', '[', 'j', ']', ' ',
  '=', '=', ' ', '4', '2', ' ', '{', ' ', 'a', 'n', 's', 'w', 'e', 'r', ' ', '=', ' ', '4', '2', ';', ' ', 'l',
  'e', 'a', 'v', 'e', ' ', 'j', ';', ' ', '}', '\n', ' ', '}', '\n', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'a',
  'n', 's', 'w', 'e', 'r', ';', '\n', '}', '\n']

def arrayTraversalText : String := String.ofList arrayTraversalCharacters

theorem arrayTraversal_lexed : (lexL arrayTraversalCharacters).toOption.isSome = true := by decide +kernel
def arrayTraversalTokens := (lexL arrayTraversalCharacters).toOption.get arrayTraversal_lexed

theorem arrayTraversal_parsed : (parseTopTief arrayTraversalTokens).toOption.isSome = true := by decide +kernel
def arrayTraversalItems := (parseTopTief arrayTraversalTokens).toOption.get arrayTraversal_parsed

theorem arrayTraversal_elaborated : (elabU (pre108 arrayTraversalItems)).toOption.isSome = true := by decide +kernel
def arrayTraversalUnit := (elabU (pre108 arrayTraversalItems)).toOption.get arrayTraversal_elaborated

theorem arrayTraversal_lowered : (UebersetzeAllg2.lowerAllg arrayTraversalUnit).toOption.isSome = true := by decide +kernel

theorem arrayTraversal_source_zeuge : (uebersetzeAllg arrayTraversalText).toOption.isSome = true := by
  have lexed := except_ok_get arrayTraversal_lexed
  have parsed := except_ok_get arrayTraversal_parsed
  have elaborated := except_ok_get arrayTraversal_elaborated
  have lowered := except_ok_get arrayTraversal_lowered
  have pipeline := uebersetzeAllg_von_zeichen lexed parsed elaborated lowered
  rw [show arrayTraversalText = String.ofList arrayTraversalCharacters from rfl, pipeline]
  rfl

end Gabbro.Grammatik.Parser.ExportWitnesses2
