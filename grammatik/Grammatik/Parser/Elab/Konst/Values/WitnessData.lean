module
public import Grammatik.Parser.Elab.Konst.ErsetzungTor

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Values.Witness
open Uebersetze Scalar

def positive : UKonstFn where
  name := "positive"
  params := [("x", .int 0 10)]
  erg := .bool
  rumpf := .block [] (some (.ret (some (.bin ">" (.variable "x") (.lit 0)))))
  signature :=
    { art := "const"
      name := "positive"
      params := [("x", .range (.atom "u8") (.lit 0) (.lit 10) false)]
      res := some (.atom "bool")
      fehler := none
      klauseln := [.gives (.bin "==" .res (.bin ">" (.variable "x") (.lit 0)))]
      generics := [] }

def optional : UKonstFn where
  name := "optional"
  params := [("x", .int 0 3)]
  erg := .opt 4
  rumpf := .block [] (some (.ret (some (.call "Some" [.variable "x"]))))
  signature :=
    { art := "const"
      name := "optional"
      params := [("x", .range (.atom "u8") (.lit 0) (.lit 3) false)]
      res := some (.index true "Slots")
      fehler := none
      klauseln := []
      generics := [] }

def absent : UKonstFn :=
  { optional with
    name := "absent"
    params := []
    rumpf := .block [] (some (.ret (some (.call "None" [])))),
    signature := { optional.signature with name := "absent", params := [] } }

def schema : USum :=
  { name := "Choice"
    cases := [("Empty", none), ("Data", some (.int 0 255)),
      ("Flag", some .bool), ("Text", some (.str 1))] }

def tagged : UKonstFn where
  name := "tagged"
  params := [("x", .int 0 10)]
  erg := .sum schema.spec
  rumpf := .block [] (some (.ret (some (.call "Data" [.bin "+" (.variable "x") (.lit 1)]))))
  signature :=
    { art := "const"
      name := "tagged"
      params := [("x", .range (.atom "u8") (.lit 0) (.lit 10) false)]
      res := some (.atom "Choice")
      fehler := none
      klauseln := []
      generics := [] }
  sums := [schema]

def emptyTag : UKonstFn :=
  { tagged with
    params := []
    rumpf := .block [] (some (.ret (some (.variable "Empty"))))
    signature := { tagged.signature with params := [] } }

def flagTag : UKonstFn :=
  { emptyTag with rumpf := .block [] (some (.ret (some (.call "Flag" [.tru])))) }

def textTag : UKonstFn :=
  { emptyTag with rumpf := .block [] (some (.ret (some (.call "Text" [.ext .text ["Z"] []])))) }

def shortText (text : String) (maximum : Nat := 1) : UKonstFn where
  name := "shortText"
  params := []
  erg := .str maximum
  rumpf := .block [] (some (.ret (some (.ext .text [text] []))))
  signature :=
    { art := "const"
      name := "shortText"
      params := []
      res := some (.str (.lit maximum))
      fehler := none
      klauseln := []
      generics := [] }

def reasonTag : UKonstFn where
  name := "reasonTag"
  params := []
  erg := .why 2
  rumpf := .block [] (some (.ret (some (.why "Reason" "Second"))))
  signature :=
    { art := "const"
      name := "reasonTag"
      params := []
      res := some (.atom "Reason")
      fehler := none
      klauseln := []
      generics := [] }
  sums := [{ name := "Foreign", cases := [("Other", none), ("Second", none)] },
    { name := "Reason", cases := [("First", none), ("Second", none)] }]

def captured : UKonstFn where
  name := "captured"
  params := [("x", .int 0 10)]
  erg := .int 0 20
  rumpf := .block [] (some (.ret (some (.bin "+" (.variable "x") (.variable "math::K")))))
  signature :=
    { art := "const"
      name := "captured"
      params := [("x", .range (.atom "u8") (.lit 0) (.lit 10) false)]
      res := some (.range (.atom "u8") (.lit 0) (.lit 20) false)
      fehler := none
      klauseln := []
      generics := [] }
  constants := [("math::K", 5), ("x", 99)]

end Gabbro.Grammatik.Parser.Konst.Values.Witness

