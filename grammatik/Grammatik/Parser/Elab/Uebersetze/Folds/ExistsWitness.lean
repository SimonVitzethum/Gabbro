module

public import Grammatik.Parser.Expr.Ausdruck.Teil3
public import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Expr.Ausdruck.Teil1
import all Grammatik.Parser.Expr.Ausdruck.Teil2
import all Grammatik.Parser.Expr.Ausdruck.Teil2a
import all Grammatik.Parser.Expr.Ausdruck.Teil3
import all Grammatik.Parser.Expr.Typ
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expansion
import all Grammatik.Parser.Elab.Uebersetze.Branches
import all Grammatik.Parser.Elab.Uebersetze.Records.Records
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil4
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil7
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil8
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil9
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil10
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil1
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil3Values
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil4
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
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
namespace Gabbro.Grammatik.Parser.Uebersetze.ExistsWitness
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

attribute [local cbv_opaque] parseTyp parseTypNach parseOr parseOrL parseAnd parseAndL
  parseCmp parseBit parseBitL parseAdd parseAddL parseMul parseMulL parseUnary
  parsePrimary parseKopf parseSuffixe parseQuant parseDomain domPlace parseOrt
  parsePred parsePredOrL parsePredAnd parsePredAndL parsePredNot parsePredAtom uFloatLimit
attribute [local cbv_eval] parseTyp.eq_def parseTypNach.eq_def parseOr.eq_def parseOrL.eq_def
  parseAnd.eq_def parseAndL.eq_def parseCmp.eq_def parseBit.eq_def parseBitL.eq_def
  parseAdd.eq_def parseAddL.eq_def parseMul.eq_def parseMulL.eq_def parseUnary.eq_def
  parsePrimary.eq_def parseKopf.eq_def parseSuffixe.eq_def parseQuant.eq_def parseDomain.eq_def
  domPlace.eq_def parseOrt.eq_def parsePred.eq_def parsePredOrL.eq_def parsePredAnd.eq_def
  parsePredAndL.eq_def parsePredNot.eq_def parsePredAtom.eq_def lowEns.eq_def

def unit : UProg :=
  {tabs := [{name := "T", count := 2, cols := []}], locks := [], fns := []}

def function : UFn :=
  {name := "sample", params := [], kinds := [], res := none,
   held := [], puts := [], gives := [], body := [], ret := .empty}

def context : UCtx :=
  {names := [], kinds := [], types := [], tabs := unit.tabs, locks := [], held := [],
   res := none, fname := "sample", alias := [], lits := []}

/-- An ordinary expression parsed through `parseOr`, not the predicate-only reader:
    `true && exists k in slots of T : false`. -/
def tokens : List Token :=
  [.wort "true", .zeichen "&&", .wort "exists", .ident "k", .wort "in",
   .wort "slots", .wort "of", .ident "T", .zeichen ":", .wort "false", .ende]

def elaborated : Except String UEns := do
  uBool context (← parseTop tokens)

-- Retain the actual parsed constructor before either Boolean consumer runs.
private def parsed : { actual : SExpr // parseTop tokens = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

public theorem exists_boolean_elaboration_zeuge :
    elaborated = .ok (.and .tru (.einige "T" "k" .fls)) := by
  simp only [elaborated, parsed.property, bind, Except.bind]
  cbv

/-- The endpoint is the concrete canonical G constructor, including its table,
    body and access guard; success or an untyped intermediate shape would be weaker. -/
public theorem exists_boolean_concrete_term_zeuge :
    (do
      let predicate ← elaborated
      lowEns unit [] [] function none predicate) =
      .ok (Expr.and (D := declOf unit) Expr.tru
        (Expr.existsSlots (D := declOf unit) (0 : Fin unit.tabs.length) Expr.fls
          (by intro resource member; cases member))) := by
  simp only [exists_boolean_elaboration_zeuge, bind, Except.bind]
  cbv

private def bindingResult : { actual : List UStmt × UCtx //
    uAnwReihe unit.tabs [] 1000 context
      [.bind false "found" (some (.atom "bool")) parsed.val] = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

public theorem exists_boolean_binding_zeuge :
    (do
      let expression ← parseTop tokens
      let (statements, _) ← uAnwReihe unit.tabs [] 1000 context
        [.bind false "found" (some (.atom "bool")) expression]
      pure statements) = .ok [UStmt.bindB "found" (.and .tru (.einige "T" "k" .fls))] := by
  simp only [parsed.property, bind, Except.bind]
  rw [bindingResult.property] <;> cbv

end Gabbro.Grammatik.Parser.Uebersetze.ExistsWitness
