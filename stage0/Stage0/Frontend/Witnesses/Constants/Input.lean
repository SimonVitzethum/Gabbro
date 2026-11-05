module
public import Stage0.Frontend.ExportCorrectness
public import Grammatik.Parser.Elab.Konst.Scalar.Export
public import Grammatik.Parser.Elab.Generic.Body

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.Konst

/-- The unchanged predicate clauses shared by both original scalar calls. -/
def signature : FnSig where
  art := "const"
  name := "increment"
  params := [("x", .range (.atom "u8") (.lit 0) (.lit 10) false)]
  res := some (.range (.atom "u8") (.lit 0) (.lit 11) false)
  fehler := none
  klauseln := [.needs (.bin ">" (.variable "x") (.lit 0)),
    .gives (.bin "==" .res (.bin "+" (.variable "x") (.lit 1)))]

def function : UKonstFn where
  name := "increment"
  params := [("x", .int 0 10)]
  erg := .int 0 11
  rumpf := .block [] (some (.ret (some (.bin "+" (.variable "x") (.lit 1)))))
  signature := signature

def wrongPost : UKonstFn :=
  { function with signature := { signature with klauseln :=
    [.needs (.bin ">" (.variable "x") (.lit 0)),
      .gives (.bin "==" .res (.variable "x"))] } }

def overflows : UKonstFn :=
  { function with
    rumpf := .block [] (some (.ret (some
      (.bin "-" (.bin "+" (.variable "x") (.lit 11)) (.lit 11)))))
    signature := { signature with klauseln := [] } }

/-- Exact original source characters; phase certificates do not replace the input. -/
def characters : List Char :=
  ("const fn increment(x : u8 in 0 .. 10) -> u8 in 0 .. 11 ".toList ++
   "requires x > 0 ensures result == x + 1 { return x + 1; } ".toList ++
   "impl fn main() -> u64 { return increment(3) + increment(5); }".toList)

def text : String := String.ofList characters

def initializerText : String := String.ofList
  ("const fn increment(x : u8 in 0 .. 10) -> u8 in 0 .. 11 ".toList ++
   "requires x > 0 ensures result == x + 1 { return x + 1; } ".toList ++
   "const ANSWER : u8 = increment(3); impl fn main() -> u8 { return ANSWER; }".toList)

end Gabbro.Stage0.Frontend.ConstWitness

namespace Gabbro.Stage0.Frontend.ConstValuesWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.Konst

def boolText : String := String.ofList
  ("const fn positive(x : u8 in 0 .. 10) -> bool ".toList ++
   "ensures result == (x > 0) { return x > 0; } ".toList ++
   "impl fn main() -> bool { return positive(3) && !positive(0); }".toList)

def optionText : String := String.ofList
  ("table Slots count 4 { slot { value : u8, } } ".toList ++
   "const fn selected(x : u8 in 0 .. 3) -> option index into Slots { return Some(x); } ".toList ++
   "impl fn main() -> option index into Slots { return selected(2); }".toList)

def noneText : String := String.ofList
  ("table Slots count 4 { slot { value : u8, } } ".toList ++
   "const fn selected() -> option index into Slots { return None; } ".toList ++
   "impl fn main() -> option index into Slots { return selected(); }".toList)

def tagText : String := String.ofList
  ("tagged type Choice = { Empty, Data(u8) }; ".toList ++
   "const fn selected(x : u8 in 0 .. 10) -> Choice { return Data(x + 1); } ".toList ++
   "impl fn main() -> Choice { return selected(4); }".toList)

def stringText : String := String.ofList
  ("const fn selected() -> string max 1 { return \"A\"; } ".toList ++
   "impl fn main() -> string max 1 { return selected(); }".toList)

def globalText : String := String.ofList
  ("const K : u8 = 5; ".toList ++
   "const fn addK(x : u8 in 0 .. 10) -> u8 in 0 .. 20 { return x + K; } ".toList ++
   "impl fn main() -> u8 { return addK(K + 1); }".toList)

def qualifiedText : String := String.ofList
  ("module Constants { pub const K : u8 = 5; } ".toList ++
   "const fn addK(x : u8 in 0 .. 10) -> u8 in 0 .. 20 { return x + Constants::K; } ".toList ++
   "impl fn main() -> u8 { return addK(Constants::K + 1); }".toList)

def blockText : String := String.ofList
  ("const fn selected() -> bool { let x = true; return x; } ".toList ++
   "impl fn main() -> bool { return selected(); }".toList)

end Gabbro.Stage0.Frontend.ConstValuesWitness
