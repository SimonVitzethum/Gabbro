module
public import Grammatik.Parser.Elab.Modules.PipelineWitness.Data
import all Grammatik.Parser.Elab.Modules.Witness.Phases
import all Grammatik.Parser.Elab.Modules.PipelineWitness.Scanning
import all Grammatik.Parser.Elab.Modules.Expansion
import all Grammatik.Parser.Elab.Modules.Shape
import all Grammatik.Parser.Elab.Modules.Substitution
import all Grammatik.Parser.Elab.Generic.Arguments
import all Grammatik.Parser.Elab.Generic.Substitution
import all Grammatik.Parser.Elab.Generic.Rewrite
import all Grammatik.Parser.Elab.Generic.Body
import all Grammatik.Parser.Elab.Generic.Expansion
import all Grammatik.Parser.Elab.Generic.Bounds
import all Grammatik.Parser.Elab.Generic.Literals
import all Grammatik.Parser.Namen.Aufloesung.Teil1a
import all Grammatik.Parser.Namen.Aufloesung.Teil1
import all Grammatik.Parser.Namen.Aufloesung.Teil2
import all Grammatik.Parser.Item.ElementTief.Defs1
import all Grammatik.Parser.Item.ElementTief.Defs2
import all Grammatik.Parser.Item.ElementTief.Defs6a
import all Grammatik.Parser.Item.ElementTief.Defs7
import all Grammatik.Parser.Item.ElementTief.GenericParams
import all Grammatik.Parser.Item.ElementTief.Kopf.Teil1a
import all Grammatik.Parser.Item.ElementTief.Kopf.Teil2
import all Grammatik.Parser.Stmt.Anweisung.Defs1
import all Grammatik.Parser.Stmt.Anweisung.Defs2a
import all Grammatik.Parser.Expr.Ausdruck.Teil1
import all Grammatik.Parser.Expr.Ausdruck.Teil2a
import all Grammatik.Parser.Expr.Ausdruck.Teil3
import all Grammatik.Parser.Expr.Typ
import all Grammatik.Parser.Print.Item.Teil1
import all Grammatik.Parser.Print.Item.Teil2
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil2
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
import all Grammatik.Parser.Elab.Uebersetze.Folds.ConstEvaluation
import Init.Data.String.Lemmas.Intercalate
import all Init.Data.Int.Repr
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

namespace Gabbro.Grammatik.Parser.Modules.PipelinePhases
open Gabbro.Grammatik.Parser.UebersetzeProben11.Phases (Input)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- Select canonical recursion equations at actual nodes, retaining the original fuels.
attribute [local cbv_opaque] parseTyp parseTypNach parseOr parseOrL parseAnd parseAndL
  parseCmp parseBit parseBitL parseAdd parseAddL parseMul parseMulL parseUnary
  parsePrimary parseKopf parseSuffixe parseModulTief parseItemsTief parseItemTief parseItemKopfTief
  visitItem visitList locateItem locateList templatesItem templatesList ordinaryItem ordinaryList
  occupiedItem occupiedList syntaxItem syntaxList Generic.rewriteExpression
  Generic.rewriteQuantifierOperands Generic.rewriteType Generic.rewriteBody Generic.rewriteStatements
  Uebersetze.uFloatLimit
attribute [local cbv_eval] parseTyp.eq_def parseTypNach.eq_def parseOr.eq_def parseOrL.eq_def
  parseAnd.eq_def parseAndL.eq_def parseCmp.eq_def parseBit.eq_def parseBitL.eq_def
  parseAdd.eq_def parseAddL.eq_def parseMul.eq_def parseMulL.eq_def parseUnary.eq_def
  parsePrimary.eq_def parseKopf.eq_def parseSuffixe.eq_def parseModulTief.eq_def
  parseItemsTief.eq_def parseItemTief.eq_def parseItemKopfTief.eq_def visitItem.eq_def visitList.eq_def
  locateItem.eq_def locateList.eq_def templatesItem.eq_def templatesList.eq_def
  ordinaryItem.eq_def ordinaryList.eq_def occupiedItem.eq_def occupiedList.eq_def
  syntaxItem.eq_def syntaxList.eq_def Generic.rewriteExpression.eq_def
  Generic.rewriteQuantifierOperands.eq_def Generic.rewriteType.eq_def Generic.rewriteBody.eq_def
  Generic.rewriteStatements.eq_def Generic.sourceSize_eq String.intercalate_singleton

-- Infer constructor-valued parser results before transporting the full
-- certified lexer equation to each unchanged public source.

private def genericTokensParsed : { actual : List SItemTief //
    parseTopTief genericInput.tokens = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def genericParsed : { actual : List SItemTief //
    parsedSource genericModuleSource = .ok actual } :=
  ⟨genericTokensParsed.val, WitnessPhases.parsed_from_input genericInput genericTokensParsed⟩

private def callerTokensParsed : { actual : List SItemTief //
    parseTopTief callerInput.tokens = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def callerParsed : { actual : List SItemTief //
    parsedSource callerSource = .ok actual } :=
  ⟨callerTokensParsed.val, WitnessPhases.parsed_from_input callerInput callerTokensParsed⟩

private def lexicalTokensParsed : { actual : List SItemTief //
    parseTopTief lexicalInput.tokens = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def lexicalParsed : { actual : List SItemTief //
    parsedSource lexicalSource = .ok actual } :=
  ⟨lexicalTokensParsed.val, WitnessPhases.parsed_from_input lexicalInput lexicalTokensParsed⟩

private def callbackTokensParsed : { actual : List SItemTief //
    parseTopTief callbackInput.tokens = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def callbackParsed : { actual : List SItemTief //
    parsedSource callbackSource = .ok actual } :=
  ⟨callbackTokensParsed.val, WitnessPhases.parsed_from_input callbackInput callbackTokensParsed⟩

private def forwardTokensParsed : { actual : List SItemTief //
    parseTopTief forwardInput.tokens = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def forwardParsed : { actual : List SItemTief //
    parsedSource callbackForwardSource = .ok actual } :=
  ⟨forwardTokensParsed.val, WitnessPhases.parsed_from_input forwardInput forwardTokensParsed⟩

private def completeTokensParsed : { actual : List SItemTief //
    parseTopTief completeInput.tokens = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def completeParsed : { actual : List SItemTief //
    parsedSource completeOrderSource = .ok actual } :=
  ⟨completeTokensParsed.val, WitnessPhases.parsed_from_input completeInput completeTokensParsed⟩

private def reasonTokensParsed : { actual : List SItemTief //
    parseTopTief reasonInput.tokens = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def reasonParsed : { actual : List SItemTief //
    parsedSource reasonOrderSource = .ok actual } :=
  ⟨reasonTokensParsed.val, WitnessPhases.parsed_from_input reasonInput reasonTokensParsed⟩

end Gabbro.Grammatik.Parser.Modules.PipelinePhases
