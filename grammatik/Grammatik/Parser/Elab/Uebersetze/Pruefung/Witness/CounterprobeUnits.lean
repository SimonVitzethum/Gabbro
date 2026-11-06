module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeText
import Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Phases
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Calls
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Units
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Heads
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.Assembly
import all Init.Data.List.MapIdx
import all Grammatik.Parser.Lex.Lexer.Teil1
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
import all Grammatik.Parser.Elab.Uebersetze.Folds.Expansion
import all Grammatik.Parser.Elab.Uebersetze.Folds.FloatLiterals
import all Grammatik.Parser.Elab.Uebersetze.Branches
import all Grammatik.Parser.Elab.Uebersetze.LoopHeaders
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
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Ende
import all Grammatik.Parser.Elab.UebersetzeAllg3.Kopf
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Grammatik.Parser.Elab.UebersetzeAllg3.Transition
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
import all Grammatik.Parser.Elab.Generic.Signatures
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Init.Data.Repr
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
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
import all Init.Data.String.ToSlice
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.String.Extra
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Legacy
import all Init.Data.String.Termination
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Export
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Ableitung
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Elaboration
import all Grammatik.Parser.Elab.Uebersetze.Einheit.ReturnCalls
import all Grammatik.Parser.Elab.Uebersetze.Einheit.Signatures
import all Grammatik.Parser.Elab.Uebersetze.Akku.ProbenPhases

import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Witness.CounterprobeText

public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

-- A literal Boolean return introduces neither folds nor a call adapter. Keep
-- the complete lexical context and head list symbolic; elabFn still runs its
-- actual uEnde type/channel check on the unchanged ending afterwards.
private theorem counterprobe_return_false (ctx : UCtx) (heads : List UFnKopf) :
    expandReturnCall ctx heads (some (.ret (some .fls))) =
      .ok ([], ctx, some (.ret (some .fls))) := by
  unfold expandReturnCall
  cases uEnde ctx (some (.ret (some .fls))) <;> rfl

private theorem counterprobe_fold_end_false (ctx : UCtx) :
    expandFoldEnd ctx (some (.ret (some .fls))) =
      .ok ([], ctx, some (.ret (some .fls))) := rfl

-- The emitted source stays unchanged; these proof equations select its real callbacks.
attribute [local cbv_opaque] uFloatLimit uAnwReihe uAnwReiheCore
  uAkkuBinder uZeigerAnw uStartNamen elabKlauseln expandReturnCall expandFoldEnd
  recordCheckCode recordCheckStatements checkSampleSubstitute lowStufe lowSeqL lowStructL lowEndL
  Measures.checkedProgram lowRufKopf lowCallArgOneL lowCallArgsAuxL withErg lowErg lowEnd
attribute [local cbv_eval] row_nil row_cons core_bind core_call core_set core_cond
  bound_names_select pointer_source_select start_source_select
  clauses_nil return_none return_empty return_variable counterprobe_return_false
  fold_end_none fold_end_empty fold_end_variable counterprobe_fold_end_false
  recording_block recording_bind recording_nil recording_cons
  sample_binary sample_variable sample_literal
  check_sequence_select check_structure_select lowEndL_succ
  lowStufe_seq lowStufe_struct lowStufe_ende
  check_argument_bool check_argument_integer check_arguments_nil check_arguments_cons
  check_result_select check_return_empty check_return_bool check_end_empty check_end_bool

attribute [local cbv_eval] admission_name_self admission_mark_self

-- Each output is inferred from its own complete canonical success equation.
-- No caller observes a getD fallback or replays the source pipeline.
private def sondeUnitMade : {unit : UProg // elabU sondeParsed.val = .ok unit} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem sonde_source_ok : elabText checkTextSonde = .ok sondeUnitMade.val :=
  sonde_text_phase.trans sondeUnitMade.property

private def sondeUnboundError : {error : String //
    elabU sondeUnboundParsed.val = .error error} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩
private def sondeDuplicateError : {error : String //
    elabU sondeDuplicateParsed.val = .error error} := by
  refine ⟨?_, by cbv <;> exact Eq.refl _⟩

private theorem sonde_unbound_refused :
    (elabText "impl fn g() { return; } check p { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"ext text\" expects ext }").toOption.isNone = true := by
  rw [sonde_unbound_phase, sondeUnboundError.property]
  rfl
private theorem sonde_duplicate_refused :
    (elabText "impl fn g() { return; } impl fn ext() -> bool { return false; } check p { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"one\" expects ext } check q { claim \"c\" measures x gates g can_fail { return false; } counterprobe \"two\" expects ext }").toOption.isNone = true := by
  rw [sonde_duplicate_phase, sondeDuplicateError.property]
  rfl

private theorem sonde_function_count : sondeUnitMade.val.fns.length = 6 := by cbv

end Gabbro.Grammatik.Parser.Uebersetze
