module
public import Grammatik.Parser.Elab.Modules.PipelineWitness.Data
import all Grammatik.Parser.Elab.Modules.PipelineWitness.Preparation
import all Grammatik.Parser.Elab.Modules.PipelineWitness.Parsing
import all Grammatik.Parser.Elab.Modules.Witness.Phases
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Elaboration
import all Grammatik.Parser.Elab.Uebersetze.Einheit.ReturnCalls
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.SondeCode
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.Konst.ErsetzungTor
import all Grammatik.Parser.Elab.Uebersetze.Guest.Source
-- Reuse the existing generic equations of the canonical mutual reader.
import all Grammatik.Parser.Elab.Uebersetze.Akku.ProbenPhases
import all Init.Data.Repr
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

-- Keep the production continuation symbolic until the actual fuel and source
-- statement are selected. The fallible call keeps uBindElse's complete callback.
private theorem reason_binding_select (tabs : List UTab) (heads : List UFnKopf)
    (fuel : Nat) (ctx : UCtx) (name : String) (ty : Option STyp)
    (value : SExpr) (reason : String) (body : SAnw) (rest : List SAnw) :
    uAnwReiheCore tabs heads fuel ctx (.bindElse name ty value reason body :: rest) =
      match fuel with
      | 0 => .error "nesting without G form"
      | next + 1 => uBindElse tabs heads (uAnwReihe tabs heads next)
          ctx name ty value reason body rest := by
  cases fuel with
  | zero => simp only [uAnwReiheCore]
  | succ fuel => exact uAnwReiheCore_bindElse tabs heads fuel ctx name ty value reason body rest

attribute [local cbv_opaque] uAnwReihe uAnwReiheCore uAkkuBinder uZeigerAnw uStartNamen
  uSondenFns uTorHuellen uFloatLimit
attribute [local cbv_eval] row_nil row_cons core_bind core_set core_call reason_binding_select
  bound_names_select pointer_source_select start_source_select sonden_nil wrappers_nil

-- Each packet is the actual output of its original collector or elaborator.
-- In particular, elabExpandedWithScopes retains canonical const admission,
-- source substitution, signature/body checks, all ownership gates and the
-- final static-conformance check. The command only gives those values cuts.
scoped macro "pipeline_unit " name:ident : command => do
  let prepared := Lean.mkIdentFrom name (name.getId.appendAfter "Prepared")
  let consts := Lean.mkIdentFrom name (name.getId.appendAfter "Constants")
  let aliases := Lean.mkIdentFrom name (name.getId.appendAfter "Aliases")
  let functions := Lean.mkIdentFrom name (name.getId.appendAfter "ScopeFunctions")
  let guests := Lean.mkIdentFrom name (name.getId.appendAfter "Guests")
  let substituted := Lean.mkIdentFrom name (name.getId.appendAfter "Substituted")
  let unit := Lean.mkIdentFrom name (name.getId.appendAfter "Unit")
  let constsCommand ← `(command| private def $consts : { actual : List (String × Int) //
      uConstsRech (uKonstFns ($prepared).val.1) ($prepared).val.1 [] = actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let aliasesCommand ← `(command| private def $aliases : {
      actual : List (String × (Int × Int)) //
      uAliase ($consts).val ($prepared).val.1 ++ uAliasBreiten ($prepared).val.1 ++
        ($consts).val.map (fun c => (c.1, (c.2, c.2))) = actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let functionsCommand ← `(command| private def $functions : { actual : List UKonstFn //
      uKonstFns (uOhneSenken ($prepared).val.1) = actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let guestsCommand ← `(command| private def $guests : {
      actual : List UGuest × List SItemTief // guestSources ($prepared).val.1 = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let substitutedCommand ← `(command| private def $substituted : { actual : List SItemTief //
      Konst.konstErsetzePipeline (uOhneSenken ($guests).val.2) = .ok actual } := by
    refine ⟨?_, by cbv <;> exact Eq.refl _⟩)
  let unitCommand ← `(command| private def $unit : { actual : Uebersetze.UProg //
      elabUExpanded ($prepared).val = .ok actual } := by
    refine ⟨?_, ?origin⟩
    case origin =>
      simp only [elabUExpanded, ($consts).property, ($aliases).property, ($functions).property]
      unfold elabExpandedWithScopes
      simp only [($guests).property, ($substituted).property, bind, Except.bind]
      cbv <;> exact Eq.refl _)
  return ⟨Lean.mkNullNode #[constsCommand, aliasesCommand, functionsCommand,
    guestsCommand, substitutedCommand, unitCommand]⟩

open scoped Gabbro.Grammatik.Parser.Modules.PipelinePhases
pipeline_unit generic
pipeline_unit stack
pipeline_unit lexical
pipeline_unit reason

-- Transport the whole canonical UProg before introducing any typed field
-- projection. Neither the parser getter nor the prepare graph is re-evaluated.
private theorem exported_from_phases {source : String}
    (parsed : { actual : List SItemTief // parsedSource source = .ok actual })
    (items : { actual : List SItemTief // pre108 parsed.val = actual })
    (prepared : { actual : List SItemTief × List (STyp × String) //
      prepare items.val = .ok actual })
    (unit : { actual : Uebersetze.UProg // elabUExpanded prepared.val = .ok actual }) :
    exportedSource source = .ok unit.val := by
  have selected := (congrArg prepare items.property).trans prepared.property
  simp only [exportedSource, parsed.property, elabU, expandU, selected, unit.property,
    bind, Except.bind]

private theorem generic_exported : exportedSource genericModuleSource = .ok genericUnit.val :=
  exported_from_phases genericParsed genericItems genericPrepared genericUnit
private theorem stack_exported : exportedSource stackSource = .ok stackUnit.val :=
  exported_from_phases WitnessPhases.stackParsed stackItems stackPrepared stackUnit
private theorem lexical_exported : exportedSource lexicalSource = .ok lexicalUnit.val :=
  exported_from_phases lexicalParsed lexicalItems lexicalPrepared lexicalUnit
private theorem reason_exported : exportedSource reasonOrderSource = .ok reasonUnit.val :=
  exported_from_phases reasonParsed reasonItems reasonPrepared reasonUnit

end Gabbro.Grammatik.Parser.Modules.PipelinePhases
