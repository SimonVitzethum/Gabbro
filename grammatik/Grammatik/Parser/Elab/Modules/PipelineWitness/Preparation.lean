module
public import Grammatik.Parser.Elab.Modules.PipelineWitness.Data
import all Grammatik.Parser.Elab.Modules.PipelineWitness.Parsing
import all Grammatik.Parser.Elab.Modules.Witness.Phases
import all Grammatik.Parser.Elab.Modules.Frontend
import all Grammatik.Parser.Elab.Generic.Expansion
import all Grammatik.Parser.Elab.Generic.Closure
import all Grammatik.Parser.Elab.Generic.Body
import all Grammatik.Parser.Elab.Generic.Rewrite
import all Grammatik.Parser.Elab.Modules.Expansion
import all Grammatik.Parser.Elab.Modules.Shape
import all Grammatik.Parser.Elab.Modules.Substitution
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil18
import all Grammatik.Parser.Spec.Walk
import all Grammatik.Parser.Spec.Items
import all Grammatik.Parser.Spec.Expand
import all Grammatik.Parser.Dyn.Collect
import all Grammatik.Parser.Dyn.Rewrite
import all Grammatik.Parser.TaggedDispatch.Frontend
import all Grammatik.Parser.Elab.Uebersetze.Folds.Substitution
import all Grammatik.Parser.Elab.Uebersetze.Folds.ConstEvaluation
import Init.Data.String.Lemmas.Intercalate
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Legacy
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.String
import all Init.Data.String.TakeDrop
import all Init.Data.String.ToSlice

namespace Gabbro.Grammatik.Parser.Modules.PipelinePhases
open Uebersetze UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- Select only the real recursion equations, with every production fuel retained.
attribute [local cbv_opaque] visitItem visitList locateItem locateList templatesItem templatesList
  ordinaryItem ordinaryList occupiedItem occupiedList syntaxItem syntaxList
  Generic.rewriteExpression Generic.rewriteQuantifierOperands Generic.rewriteType
  Generic.rewriteBody Generic.rewriteStatements Generic.instanceClosure Generic.checkRecursion
  Spec.Walk.expr Spec.Walk.type Spec.Walk.statement Spec.Walk.statements
  Spec.Walk.item Spec.Walk.constant Spec.resolveKnownBodies Spec.inferType
  Spec.canonicalType Spec.expandEffects sErsetze uKonstEval entfalteFrage entfalteFrageL uFloatLimit
attribute [local cbv_eval] visitItem.eq_def visitList.eq_def locateItem.eq_def locateList.eq_def
  templatesItem.eq_def templatesList.eq_def ordinaryItem.eq_def ordinaryList.eq_def
  occupiedItem.eq_def occupiedList.eq_def syntaxItem.eq_def syntaxList.eq_def
  Generic.rewriteExpression.eq_def Generic.rewriteQuantifierOperands.eq_def
  Generic.rewriteType.eq_def Generic.rewriteBody.eq_def Generic.rewriteStatements.eq_def
  Generic.instanceClosure.eq_def Generic.checkRecursion.eq_def Generic.sourceSize_eq
  Spec.Walk.expr.eq_def Spec.Walk.type.eq_def Spec.Walk.statement.eq_def
  Spec.Walk.statements.eq_def Spec.Walk.item.eq_def Spec.Walk.constant.eq_def
  Spec.resolveKnownBodies.eq_def Spec.inferType.eq_def Spec.canonicalType.eq_def
  Spec.expandEffects.eq_def sErsetze.eq_def uKonstEval.eq_def entfalteFrage.eq_def
  entfalteFrageL.eq_def Spec.Walk.expr_literal Spec.Walk.type_atom String.intercalate_singleton
attribute [local cbv_opaque] parseTyp parseTypNach parseOr parseOrL parseAnd parseAndL
  parseCmp parseBit parseBitL parseAdd parseAddL parseMul parseMulL parseUnary
  parsePrimary parseKopf parseSuffixe
attribute [local cbv_eval] parseTyp.eq_def parseTypNach.eq_def parseOr.eq_def parseOrL.eq_def
  parseAnd.eq_def parseAndL.eq_def parseCmp.eq_def parseBit.eq_def parseBitL.eq_def
  parseAdd.eq_def parseAddL.eq_def parseMul.eq_def parseMulL.eq_def parseUnary.eq_def
  parsePrimary.eq_def parseKopf.eq_def parseSuffixe.eq_def

-- The commands below only name separate equality certificates for the existing
-- producers. Their constructor-valued results are inferred from actual success;
-- no source item, instantiated output, name allocation or callback is supplied.
scoped macro "pipeline_items " name:ident " from " parsed:term : command => do
  let items := Lean.mkIdentFrom name (name.getId.appendAfter "Items")
  `(command| private def $items : { actual : List SItemTief //
      pre108 ($parsed).val = actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)

scoped macro "pipeline_modules " name:ident : command => do
  let items := Lean.mkIdentFrom name (name.getId.appendAfter "Items")
  let visited := Lean.mkIdentFrom name (name.getId.appendAfter "Visits")
  let environment := Lean.mkIdentFrom name (name.getId.appendAfter "Environment")
  let resolved := Lean.mkIdentFrom name (name.getId.appendAfter "Resolved")
  let raw := Lean.mkIdentFrom name (name.getId.appendAfter "ModulesRaw")
  let visitCommand ← `(command| private def $visited : { actual : Unit × Work //
      WitnessPhases.VisitResult ($items).val (.ok actual) } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let envCommand ← `(command| private def $environment : { actual : Generic.Environment //
      argumentEnvironment (Aufloesung.quelle (ordinaryList ($items).val))
        ($visited).val.2 = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let resolvedCommand ← `(command| private def $resolved : { actual : List SItemTief //
      ($visited).val.2.locations.mapM (resolve ($environment).val
        (Aufloesung.quelle (ordinaryList ($items).val)) ($visited).val.2.locations) =
          .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let rawCommand ← `(command| private def $raw : { actual : Expansion //
      expandRaw ($items).val = .ok actual } := by
    refine ⟨?_, ?origin⟩
    case origin =>
      unfold expandRaw
      simp only [($visited).property, ($environment).property, ($resolved).property,
        bind, Except.bind, pure, Except.pure]
      cbv <;> exact Eq.refl _)
  return ⟨Lean.mkNullNode #[visitCommand, envCommand, resolvedCommand, rawCommand]⟩

scoped macro "pipeline_prepare " name:ident : command => do
  let items := Lean.mkIdentFrom name (name.getId.appendAfter "Items")
  let modulesRaw := Lean.mkIdentFrom name (name.getId.appendAfter "ModulesRaw")
  let modules := Lean.mkIdentFrom name (name.getId.appendAfter "Modules")
  let members := Lean.mkIdentFrom name (name.getId.appendAfter "Members")
  let functions := Lean.mkIdentFrom name (name.getId.appendAfter "Functions")
  let desugared := Lean.mkIdentFrom name (name.getId.appendAfter "Desugared")
  let declarations := Lean.mkIdentFrom name (name.getId.appendAfter "Declarations")
  let raw := Lean.mkIdentFrom name (name.getId.appendAfter "Raw")
  let prepared := Lean.mkIdentFrom name (name.getId.appendAfter "Prepared")
  let modulesCommand ← `(command| private def $modules : { actual : Expansion //
      expandWithRequirements ($items).val = .ok actual } := by
    refine ⟨?_, ?origin⟩
    case origin =>
      simp only [expandWithRequirements, ($modulesRaw).property, bind, Except.bind]
      cbv <;> exact Eq.refl _)
  let membersCommand ← `(command| private def $members : { actual : List SItemTief //
      (if syntaxList ($items).val then normTopU32 (uMembers ($modules).val.items)
        else uMembers ($modules).val.items) = actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let functionsCommand ← `(command| private def $functions : { actual : Generic.Expansion //
      Generic.expandDetailed ($members).val ($modules).val.literals = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let desugaredCommand ← `(command| private def $desugared : { actual : List SItemTief //
      entzuckere ($functions).val.items = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let declarationsCommand ← `(command| private def $declarations : {
      actual : List SItemTief × List String //
      exportDeclarationUnitDetailed ($desugared).val = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let rawCommand ← `(command| private def $raw : { actual : Prepared //
      prepareDetailedRaw ($items).val = .ok actual } := by
    refine ⟨?_, ?origin⟩
    case origin =>
      simp only [prepareDetailedRaw, ($modules).property, ($members).property,
        ($functions).property, ($desugared).property, ($declarations).property,
        bind, Except.bind, pure, Except.pure]
      cbv <;> exact Eq.refl _)
  let preparedCommand ← `(command| private def $prepared : {
      actual : List SItemTief × List (STyp × String) //
      prepare ($items).val = .ok actual } := by
    refine ⟨?_, ?origin⟩
    case origin =>
      simp only [prepare, ($raw).property, bind, Except.bind]
      cbv <;> exact Eq.refl _)
  return ⟨Lean.mkNullNode #[modulesCommand, membersCommand, functionsCommand,
    desugaredCommand, declarationsCommand, rawCommand, preparedCommand]⟩

open scoped Gabbro.Grammatik.Parser.Modules.PipelinePhases

pipeline_items generic from genericParsed
pipeline_modules generic
pipeline_prepare generic
pipeline_items caller from callerParsed
pipeline_modules caller
pipeline_prepare caller
pipeline_items lexical from lexicalParsed
pipeline_modules lexical
pipeline_prepare lexical
pipeline_items callback from callbackParsed
pipeline_modules callback
pipeline_prepare callback
pipeline_items forward from forwardParsed
pipeline_modules forward
pipeline_prepare forward
pipeline_items complete from completeParsed
pipeline_modules complete
pipeline_prepare complete
pipeline_items reason from reasonParsed
-- With no module syntax, the real expandRaw immediately returns these items;
-- no visitor or argument-environment phase is executed for this source.
private def reasonModulesRaw : { actual : Expansion //
    expandRaw reasonItems.val = .ok actual } := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
pipeline_prepare reason

-- Reuse the measured stack module expansion instead of evaluating it again.
pipeline_items stack from WitnessPhases.stackParsed
private def stackModulesRaw : { actual : Expansion // expandRaw stackItems.val = .ok actual } := by
  have kept : pre108 WitnessPhases.stackParsed.val = WitnessPhases.stackParsed.val := by
    unfold pre108
    have syntax : syntaxList WitnessPhases.stackParsed.val = true := by cbv
    simp only [syntax, ite_true]
  exact ⟨WitnessPhases.stackRaw.val,
    (congrArg expandRaw (stackItems.property.symm.trans kept)).trans WitnessPhases.stackRaw.property⟩
pipeline_prepare stack

-- Compose the whole prepared result before applying any list or signature projection.
private theorem prepared_from_phases {source : String}
    (parsed : { actual : List SItemTief // parsedSource source = .ok actual })
    (items : { actual : List SItemTief // pre108 parsed.val = actual })
    (prepared : { actual : List SItemTief × List (STyp × String) //
      prepare items.val = .ok actual }) : preparedSource source = .ok prepared.val.1 := by
  have selected := (congrArg prepare items.property).trans prepared.property
  simp only [preparedSource, parsed.property, selected, bind, Except.bind, pure, Except.pure]

private theorem generic_prepared : preparedSource genericModuleSource = .ok genericPrepared.val.1 :=
  prepared_from_phases genericParsed genericItems genericPrepared
private theorem caller_prepared : preparedSource callerSource = .ok callerPrepared.val.1 :=
  prepared_from_phases callerParsed callerItems callerPrepared
private theorem lexical_prepared : preparedSource lexicalSource = .ok lexicalPrepared.val.1 :=
  prepared_from_phases lexicalParsed lexicalItems lexicalPrepared
private theorem callback_prepared : preparedSource callbackSource = .ok callbackPrepared.val.1 :=
  prepared_from_phases callbackParsed callbackItems callbackPrepared
private theorem complete_prepared : preparedSource completeOrderSource = .ok completePrepared.val.1 :=
  prepared_from_phases completeParsed completeItems completePrepared
private theorem stack_prepared : preparedSource stackSource = .ok stackPrepared.val.1 :=
  prepared_from_phases WitnessPhases.stackParsed stackItems stackPrepared

-- The two original callback claims enter prepare without pre108. Module syntax
-- is exactly the canonical branch where pre108 preserves its whole input.
private theorem direct_from_modules {source : String}
    (parsed : { actual : List SItemTief // parsedSource source = .ok actual })
    (items : { actual : List SItemTief // pre108 parsed.val = actual })
    (prepared : { actual : List SItemTief × List (STyp × String) //
      prepare items.val = .ok actual }) (syntax : syntaxList parsed.val = true) :
    (parsedSource source).bind prepare = .ok prepared.val := by
  have kept : pre108 parsed.val = parsed.val := by simp only [pre108, syntax, ite_true]
  have same := (congrArg prepare (kept.symm.trans items.property)).trans prepared.property
  simp only [parsed.property, bind, Except.bind, same]
private theorem callback_direct :
    (parsedSource callbackSource).bind prepare = .ok callbackPrepared.val :=
  direct_from_modules callbackParsed callbackItems callbackPrepared (by cbv)
private theorem forward_direct :
    (parsedSource callbackForwardSource).bind prepare = .ok forwardPrepared.val :=
  direct_from_modules forwardParsed forwardItems forwardPrepared (by cbv)

end Gabbro.Grammatik.Parser.Modules.PipelinePhases
