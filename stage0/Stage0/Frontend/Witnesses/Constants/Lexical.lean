module
public import Stage0.Frontend.Witnesses.Constants.Fragments1
public import Stage0.Frontend.Witnesses.Constants.Fragments2
public import Stage0.Frontend.Witnesses.Constants.Fragments3

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik.Parser
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def incrementScan := (((((fragment0).append fragment1).append fragment2).append fragment3).append fragment4).append fragment5

theorem increment_lexed :
    lex Gabbro.Stage0.Frontend.ConstWitness.text = .ok (incrementScan.tokens ++ [.ende]) := by
  have characters : Gabbro.Stage0.Frontend.ConstWitness.text = String.ofList ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '1', ' ', 'r', 'e', 'q', 'u', 'i', 'r', 'e', 's', ' ', 'x', ' ', '>', ' ', '0', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'r', 'e', 's', 'u', 'l', 't', ' ', '=', '=', ' ', 'x', ' ', '+', ' ', '1', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ' ', '+', ' ', '1', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '6', '4', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', '3', ')', ' ', '+', ' ', 'i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', '5', ')', ';', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact incrementScan.lexed (by cbv)

def initializerScan := (((((fragment0).append fragment1).append fragment2).append fragment6).append fragment7).append fragment8

theorem initializer_lexed :
    lex Gabbro.Stage0.Frontend.ConstWitness.initializerText = .ok (initializerScan.tokens ++ [.ende]) := by
  have characters : Gabbro.Stage0.Frontend.ConstWitness.initializerText = String.ofList ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '1', ' ', 'r', 'e', 'q', 'u', 'i', 'r', 'e', 's', ' ', 'x', ' ', '>', ' ', '0', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'r', 'e', 's', 'u', 'l', 't', ' ', '=', '=', ' ', 'x', ' ', '+', ' ', '1', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ' ', '+', ' ', '1', ';', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ' ', ':', ' ', 'u', '8', ' ', '=', ' ', 'i', 'n', 'c', 'r', 'e', 'm', 'e', 'n', 't', '(', '3', ')', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ';', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact initializerScan.lexed (by cbv)

def boolTextScan := ((((fragment9).append fragment10).append fragment11).append fragment12).append fragment13

theorem boolText_lexed :
    lex Gabbro.Stage0.Frontend.ConstValuesWitness.boolText = .ok (boolTextScan.tokens ++ [.ende]) := by
  have characters : Gabbro.Stage0.Frontend.ConstValuesWitness.boolText = String.ofList ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'p', 'o', 's', 'i', 't', 'i', 'v', 'e', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', 'e', 'n', 's', 'u', 'r', 'e', 's', ' ', 'r', 'e', 's', 'u', 'l', 't', ' ', '=', '=', ' ', '(', 'x', ' ', '>', ' ', '0', ')', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ' ', '>', ' ', '0', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'p', 'o', 's', 'i', 't', 'i', 'v', 'e', '(', '3', ')', ' ', '&', '&', ' ', '!', 'p', 'o', 's', 'i', 't', 'i', 'v', 'e', '(', '0', ')', ';', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact boolTextScan.lexed (by cbv)

def optionTextScan := (((((fragment14).append fragment15).append fragment16).append fragment17).append fragment18).append fragment19

theorem optionText_lexed :
    lex Gabbro.Stage0.Frontend.ConstValuesWitness.optionText = .ok (optionTextScan.tokens ++ [.ende]) := by
  have characters : Gabbro.Stage0.Frontend.ConstValuesWitness.optionText = String.ofList ['t', 'a', 'b', 'l', 'e', ' ', 'S', 'l', 'o', 't', 's', ' ', 'c', 'o', 'u', 'n', 't', ' ', '4', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', 'a', 'l', 'u', 'e', ' ', ':', ' ', 'u', '8', ',', ' ', '}', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '3', ')', ' ', '-', '>', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'l', 'o', 't', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'S', 'o', 'm', 'e', '(', 'x', ')', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'l', 'o', 't', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', '2', ')', ';', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact optionTextScan.lexed (by cbv)

def noneTextScan := (((((fragment14).append fragment20).append fragment21).append fragment22).append fragment23).append fragment24

theorem noneText_lexed :
    lex Gabbro.Stage0.Frontend.ConstValuesWitness.noneText = .ok (noneTextScan.tokens ++ [.ende]) := by
  have characters : Gabbro.Stage0.Frontend.ConstValuesWitness.noneText = String.ofList ['t', 'a', 'b', 'l', 'e', ' ', 'S', 'l', 'o', 't', 's', ' ', 'c', 'o', 'u', 'n', 't', ' ', '4', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', ' ', 'v', 'a', 'l', 'u', 'e', ' ', ':', ' ', 'u', '8', ',', ' ', '}', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ' ', '-', '>', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'l', 'o', 't', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'N', 'o', 'n', 'e', '(', ')', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', 'i', 'n', 'd', 'e', 'x', ' ', 'i', 'n', 't', 'o', ' ', 'S', 'l', 'o', 't', 's', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ';', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact noneTextScan.lexed (by cbv)

def tagTextScan := ((((fragment25).append fragment26).append fragment27).append fragment28).append fragment29

theorem tagText_lexed :
    lex Gabbro.Stage0.Frontend.ConstValuesWitness.tagText = .ok (tagTextScan.tokens ++ [.ende]) := by
  have characters : Gabbro.Stage0.Frontend.ConstValuesWitness.tagText = String.ofList ['t', 'a', 'g', 'g', 'e', 'd', ' ', 't', 'y', 'p', 'e', ' ', 'C', 'h', 'o', 'i', 'c', 'e', ' ', '=', ' ', '{', ' ', 'E', 'm', 'p', 't', 'y', ',', ' ', 'D', 'a', 't', 'a', '(', 'u', '8', ')', ' ', '}', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'C', 'h', 'o', 'i', 'c', 'e', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'D', 'a', 't', 'a', '(', 'x', ' ', '+', ' ', '1', ')', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'C', 'h', 'o', 'i', 'c', 'e', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', '4', ')', ';', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact tagTextScan.lexed (by cbv)

def stringTextScan := (((fragment30).append fragment31).append fragment32).append fragment24

theorem stringText_lexed :
    lex Gabbro.Stage0.Frontend.ConstValuesWitness.stringText = .ok (stringTextScan.tokens ++ [.ende]) := by
  have characters : Gabbro.Stage0.Frontend.ConstValuesWitness.stringText = String.ofList ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ' ', '-', '>', ' ', 's', 't', 'r', 'i', 'n', 'g', ' ', 'm', 'a', 'x', ' ', '1', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '"', 'A', '"', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 's', 't', 'r', 'i', 'n', 'g', ' ', 'm', 'a', 'x', ' ', '1', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ';', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact stringTextScan.lexed (by cbv)

def globalTextScan := (((fragment33).append fragment34).append fragment35).append fragment36

theorem globalText_lexed :
    lex Gabbro.Stage0.Frontend.ConstValuesWitness.globalText = .ok (globalTextScan.tokens ++ [.ende]) := by
  have characters : Gabbro.Stage0.Frontend.ConstValuesWitness.globalText = String.ofList ['c', 'o', 'n', 's', 't', ' ', 'K', ' ', ':', ' ', 'u', '8', ' ', '=', ' ', '5', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '2', '0', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ' ', '+', ' ', 'K', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'K', ' ', '+', ' ', '1', ')', ';', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact globalTextScan.lexed (by cbv)

def qualifiedTextScan := (((((fragment37).append fragment38).append fragment39).append fragment40).append fragment41).append fragment42

theorem qualifiedText_lexed :
    lex Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText = .ok (qualifiedTextScan.tokens ++ [.ende]) := by
  have characters : Gabbro.Stage0.Frontend.ConstValuesWitness.qualifiedText = String.ofList ['m', 'o', 'd', 'u', 'l', 'e', ' ', 'C', 'o', 'n', 's', 't', 'a', 'n', 't', 's', ' ', '{', ' ', 'p', 'u', 'b', ' ', 'c', 'o', 'n', 's', 't', ' ', 'K', ' ', ':', ' ', 'u', '8', ' ', '=', ' ', '5', ';', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'x', ' ', ':', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '1', '0', ')', ' ', '-', '>', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', '2', '0', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ' ', '+', ' ', 'C', 'o', 'n', 's', 't', 'a', 'n', 't', 's', ':', ':', 'K', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'a', 'd', 'd', 'K', '(', 'C', 'o', 'n', 's', 't', 'a', 'n', 't', 's', ':', ':', 'K', ' ', '+', ' ', '1', ')', ';', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact qualifiedTextScan.lexed (by cbv)

def blockTextScan := (((fragment43).append fragment44).append fragment12).append fragment24

theorem blockText_lexed :
    lex Gabbro.Stage0.Frontend.ConstValuesWitness.blockText = .ok (blockTextScan.tokens ++ [.ende]) := by
  have characters : Gabbro.Stage0.Frontend.ConstValuesWitness.blockText = String.ofList ['c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', '{', ' ', 'l', 'e', 't', ' ', 'x', ' ', '=', ' ', 't', 'r', 'u', 'e', ';', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'x', ';', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'b', 'o', 'o', 'l', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 's', 'e', 'l', 'e', 'c', 't', 'e', 'd', '(', ')', ';', ' ', '}'] := by cbv
  rw [characters, lex_ofList]
  exact blockTextScan.lexed (by cbv)

end Gabbro.Stage0.Frontend.ConstPhases
