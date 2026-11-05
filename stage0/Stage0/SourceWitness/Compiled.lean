module
public import Stage0.SourceWitness.Input
public import Stage0.SourceWitness.Owners
public import Stage0.Frontend.Witnesses.Constants.ProgramPackets
import all Stage0.SourceWitness.Input
import all Stage0.SourceWitness.Owners

@[expose] public section
namespace Gabbro.Stage0.SourceWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
open Frontend.ConstPhases
set_option maxRecDepth 2000
set_option maxHeartbeats 100000

attribute [local cbv_opaque] uFloatLimit Frontend.normalize lowStufe lowSeqL lowStructL
attribute [local cbv_eval]
  Gabbro.Grammatik.Parser.UebersetzeProben2.seq_select
  Gabbro.Grammatik.Parser.UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct
  Konst.Values.expression.eq_def Konst.Values.payloadExpression.eq_def
  Konst.Values.reify.eq_def Konst.Values.reifyPayload.eq_def
  Konst.Values.WitnessReaders.reader_bool Konst.Values.WitnessReaders.reader_int
  Konst.Values.WitnessReaders.reader_text Konst.Values.WitnessReaders.reader_sum
  Konst.Values.WitnessReaders.reader_payload Konst.Values.WitnessReaders.reader_empty
  Konst.Values.WitnessReaders.reader_missing

private theorem source_function_count : sourceHeader.unit.fns.length = 1 := by cbv

private theorem source_functions : ∀ f : Fin sourceHeader.unit.fns.length,
    (lowerFnAt sourceHeader.unit f).toOption.isSome = true := by
  rintro ⟨index, bound⟩
  have small : index < 1 := by simpa only [source_function_count] using bound
  have zero : index = 0 := by omega
  subst index
  cbv

private def sourceFunctions : Functions sourceHeader.unit :=
  Functions.of_success source_functions (by cbv) (by
    rintro ⟨index, bound⟩
    have small : index < 1 := by simpa only [source_function_count] using bound
    have zero : index = 0 := by omega
    subst index
    cbv) (by cbv)

-- Every value is inferred from its actual producer equality; no G program or
-- source table is independently supplied in this witness.
private def sourceBody : Body sourceHeader := by
  refine {
    functions := sourceFunctions
    main := ⟨0, by rw [source_function_count]; decide⟩
    entry := by cbv
    initializers := by cbv
    arrays := ?arrays
    arrayEq := ?arrayEq
    program := ?program
    restored := ?restored
    accepted := ?accepted }
  case arrayEq => cbv <;> exact Eq.refl _
  case restored => cbv <;> exact Eq.refl _
  case accepted => cbv

private def sourceCompiled : {result : Compiled text // compile text = .ok result} :=
  Frontend.ConstPhases.compiledResult sourceHeader sourceBody

-- Fix the complete compiled constructor before any unit/entry/scopes projection.
-- All of these are properties of the canonical packet, without unfolding emit.
private theorem compiled_carriers :
    sourceCompiled.val.unit.tabs.length = 1 ∧ sourceCompiled.val.unit.globs.length = 0 ∧
    sourceCompiled.val.unit.axs.length = 0 ∧ sourceCompiled.val.unit.regs.length = 0 := by
  cbv

private theorem compiled_params : (declOf sourceCompiled.val.unit).params sourceCompiled.val.main = [] := by
  cbv

private theorem compiled_result :
    (declOf sourceCompiled.val.unit).erg sourceCompiled.val.main = some (.int 0 42) := by cbv

private theorem compiled_fieldless : ∀ t : Fin sourceCompiled.val.unit.tabs.length,
    fieldCount sourceCompiled.val.unit t = 0 := by
  intro t
  have count := compiled_carriers.1
  have small : t.val < 1 := by simpa only [count] using t.isLt
  have zero : t.val = 0 := by omega
  have index : t = ⟨0, by rw [count]; decide⟩ := Fin.ext zero
  subst t
  cbv

private theorem compiled_table_count : sourceCompiled.val.unit.tabs.map (·.count) = [2 ^ 32] := by cbv

private theorem compiled_scopes :
    sourceCompiled.val.source.scopes.values = [("NEGATIVE", -1), ("C", 42), ("ANSWER", 42)] ∧
    sourceCompiled.val.source.scopes.declared =
      [("A", (-128, 127)), ("B", (-128, 127)), ("Bound", (0, 42)), ("Final", (0, 42))] ∧
    sourceCompiled.val.unit.fns.length = 1 := by
  constructor
  · cbv
  · constructor <;> cbv

private theorem compiled_aliases :
    sourceCompiled.val.source.scopes.aliasConstants = sourceCompiled.val.source.scopes.values := by cbv

end Gabbro.Stage0.SourceWitness
