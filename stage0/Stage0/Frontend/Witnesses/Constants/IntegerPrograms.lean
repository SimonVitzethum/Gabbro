module
public import Stage0.Frontend.Witnesses.Constants.ProgramPackets
public import Stage0.Frontend.Witnesses.Constants.IntegerSources
import Grammatik.Parser.Elab.Konst.Values.WitnessReaders
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
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
import all Grammatik.Parser.Elab.Konst.Ersetzung
import all Grammatik.Parser.Elab.Konst.ErsetzungTor
import all Grammatik.Parser.Elab.Konst.Scope
import all Grammatik.Parser.Elab.Konst.Replacement
import all Grammatik.Parser.Elab.Konst.Scalar.Model
import all Grammatik.Parser.Elab.Konst.Scalar.Expression
import all Grammatik.Parser.Elab.Konst.Scalar.Names
import all Grammatik.Parser.Elab.Konst.Scalar.Arguments
import all Grammatik.Parser.Elab.Konst.Scalar.KExpr
import all Grammatik.Parser.Elab.Konst.Scalar.Export
import all Grammatik.Parser.Elab.Konst.Values.Expression
import all Grammatik.Parser.Elab.Konst.Values.Quotation
import all Grammatik.Parser.Elab.Konst.Values.Export

@[expose] public section
namespace Gabbro.Stage0.Frontend.ConstPhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- These are the existing generic typed reader equations used by the green const witnesses.
attribute [local cbv_eval] Konst.Values.expression.eq_def Konst.Values.payloadExpression.eq_def
attribute [local cbv_eval] Konst.Values.reify.eq_def Konst.Values.reifyPayload.eq_def
attribute [local cbv_eval]
  Konst.Values.WitnessReaders.reader_bool Konst.Values.WitnessReaders.reader_int
  Konst.Values.WitnessReaders.reader_text Konst.Values.WitnessReaders.reader_sum
  Konst.Values.WitnessReaders.reader_payload Konst.Values.WitnessReaders.reader_empty
  Konst.Values.WitnessReaders.reader_missing

-- Select a used field of the actual fuel record instead of expanding its unused operations.
attribute [local cbv_opaque] lowStufe lowSeqL lowStructL uFloatLimit Frontend.normalize
attribute [local cbv_eval]
  Gabbro.Grammatik.Parser.UebersetzeProben2.seq_select
  Gabbro.Grammatik.Parser.UebersetzeProben2.struct_select
  lowStufe_seq lowStufe_struct
  uKonstZeile.eq_def uKonstZeilen.eq_def lowLit.eq_def

/-- Retain the actual elaborated constructor and all body facts inside one opaque theorem. -/
private theorem increment_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstWitness.text,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) := by
  let header : Header Gabbro.Stage0.Frontend.ConstWitness.text := by
    refine {
      source := sourceFrom incrementInput incrementTail
      sourceEq := by exact sourceFrom_eq incrementInput incrementTail
      expanded := ?expanded
      requirements := ?requirements
      expansion := ?expansion
      constants := ?constants
      ordinary := by cbv
      metadata := by exact incrementTail.metadata
      candidate := ?candidate
      elaborated := ?elaborated }
    case expansion => cbv <;> exact Eq.refl _
    case constants =>
      change Konst.checkSourceConstants incrementInput.original = .ok ()
      unfold Konst.checkSourceConstants
      split
      · exact incrementTail.metadata
      · rfl
    case elaborated => cbv <;> exact Eq.refl _
  have count : header.unit.fns.length = 1 := by cbv
  have produced : ∀ f : Fin header.unit.fns.length,
      (lowerFnAt header.unit f).toOption.isSome = true := by
    rintro ⟨index, bound⟩
    have small : index < 1 := by simpa only [count] using bound
    have zero : index = 0 := by omega
    subst index
    cbv
  let functions : Functions header.unit := Functions.of_success produced (by cbv) (by
    rintro ⟨index, bound⟩
    have small : index < 1 := by simpa only [count] using bound
    have zero : index = 0 := by omega
    subst index
    cbv) (by cbv)
  refine ⟨header, count, ?body⟩
  case body =>
    refine ⟨{
      functions := functions
      main := ⟨0, by omega⟩
      entry := by cbv
      initializers := by cbv
      arrays := ?arrays
      arrayEq := ?arrayEq
      program := ?program
      restored := ?restored
      accepted := ?accepted }⟩
    case arrayEq => cbv <;> exact Eq.refl _
    case restored => cbv <;> exact Eq.refl _
    case accepted => cbv

theorem increment_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstWitness.text, compile Gabbro.Stage0.Frontend.ConstWitness.text = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := increment_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

/-- Transport all scalar scope projections together from the certified collector preparation. -/
private theorem initializer_scope_data
    (P : List (String × (Int × Int)) → List UKonstFn → List (String × Int) → Prop)
    (proved : P
      (initializerScopePreparation.val.env ++ initializerScalarFold.val.map
        (fun c => (c.1, (c.2, c.2))))
      initializerScopePreparation.val.fns initializerScalarFold.val) :
    P initializerConservative.scope.types initializerConservative.scope.functions
      initializerConservative.scope.values := by
  dsimp only [initializerConservative, Frontend.evaluatedScopes, Frontend.Scopes.types]
  exact Eq.mpr (congrArg (fun prepared : Frontend.Prepared =>
    P (prepared.env ++ initializerScalarFold.val.map (fun c => (c.1, (c.2, c.2))))
      prepared.fns initializerScalarFold.val) initializerScopePreparation.property) proved

/-- Infer the complete numeric result from the actual evaluator in the already certified scope. -/
private theorem initializer_numeric_value :
    ∃ value : Int,
      uKonstWert 0 255 initializerConservative.scope.functions
        initializerConservative.scope.values 64 (.call "increment" [.lit 3]) = some value ∧
      0 ≤ value ∧ value ≤ 255 := by
  have packet : ∃ value : Int,
      uKonstWert 0 255 initializerScopePreparation.val.fns initializerScalarFold.val
        64 (.call "increment" [.lit 3]) = some value ∧ 0 ≤ value ∧ value ≤ 255 := by
    refine ⟨?value, ?evaluated, ?lower, ?upper⟩
    case evaluated => cbv <;> exact Eq.refl _
    case lower => cbv <;> exact Int.NonNeg.mk _
    case upper => cbv <;> exact Int.NonNeg.mk _
  obtain ⟨value, evaluated, lower, upper⟩ := packet
  exact ⟨value, initializer_scope_data (fun _ fns values =>
    uKonstWert 0 255 fns values 64 (.call "increment" [.lit 3]) = some value) evaluated,
    lower, upper⟩

/-- Select the actual constant-item checker through all of its original typed gates. -/
private theorem checked_constant_item {original : List SItemTief}
    (u : UProg) (scope : Frontend.Scopes original)
    (name : String) (sourceType : STyp) (payload : SKonstWert)
    (ty : Ty) (raw : USide) (term : Expr (declOf u) [] [] ty)
    (meaning : Frontend.checkConstantMeaning scope.types scope.functions scope.values
      (.constT name sourceType payload) = true)
    (typed : uTypIn scope.types [] (uRecordConstantTypes u.records) [] [] sourceType = .ok ty)
    (evaluated : uKonstZeile scope.types scope.functions scope.values ty payload
      (uRecordConstant u.records scope.types scope.functions scope.values) = some raw)
    (lowered : lowLit (u := u) (Γ := []) (Λ := []) ty raw = .ok term) :
    (Frontend.checkArrayItem u scope (.constT name sourceType payload)).toOption.isSome = true := by
  unfold Frontend.checkArrayItem
  dsimp only [Frontend.arrayInput]
  split
  · split
    · rename_i error rejected
      cases rejected.symm.trans typed
    · rename_i actual selected
      have same : actual = ty := Except.ok.inj (selected.symm.trans typed)
      subst actual
      split
      · rename_i rejected
        cases rejected.symm.trans evaluated
      · rename_i actual selected
        have same : actual = raw := Option.some.inj (selected.symm.trans evaluated)
        subst actual
        split
        · rename_i error rejected
          cases rejected.symm.trans lowered
        · rfl
  · rename_i rejected
    exact False.elim (rejected meaning)

/-- Success of each actual item composes through the existing dependent array-check fold. -/
private theorem checked_array_items {original : List SItemTief}
    (u : UProg) (scope : Frontend.Scopes original) :
    ∀ items : List SItemTief,
      (∀ item ∈ items, (Frontend.checkArrayItem u scope item).toOption.isSome = true) →
      (Frontend.checkArrays u scope items).toOption.isSome = true := by
  intro items
  induction items with
  | nil => intro _; rfl
  | cons item rest ih =>
    intro each
    have head := Gabbro.Grammatik.except_ok_get (each item (List.mem_cons_self))
    have tail := Gabbro.Grammatik.except_ok_get
      (ih (fun entry member => each entry (List.mem_cons_of_mem item member)))
    rw [Frontend.checkArrays, head, tail]
    rfl

/-- The existing dependent collector retains a family whose readers already return that family. -/
private theorem collect_values (n : Nat) :
    ∀ (T : Fin n → Type) (values : (i : Fin n) → T i),
      OldSource.collect n T (fun i => .ok (values i)) = .ok values := by
  induction n with
  | zero =>
    intro T values
    apply congrArg (fun result : (i : Fin 0) → T i => Except.ok (ε := String) result)
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro T values
    rewrite [OldSource.collect, ih]
    apply congrArg (fun result : (i : Fin (n + 1)) → T i => Except.ok (ε := String) result)
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; rfl

/-- Replay restoration symbolically when the actual expanded posts contain no entry reads. -/
private theorem restore_entry_free (items expanded : List SItemTief)
    (requirements : List (STyp × String)) (unit : UProg) (program : Programm (declOf unit))
    (expansion : expandU items = .ok (expanded, requirements))
    (entryFree : ∀ f : Fin unit.fns.length,
      (OldSource.clauses expanded (fnAt unit f).name).any OldSource.hasEntry = false) :
    OldSource.restore items unit program = .ok program := by
  have readers : OldSource.atFunction expanded unit program =
      (fun f => .ok (program.ensures f)) := by
    funext f
    unfold OldSource.atFunction
    dsimp only
    erw [entryFree f]
    rfl
  unfold OldSource.restore
  rewrite [expansion]
  dsimp only [bind, Except.bind]
  erw [readers, collect_values]
  rfl

/-- Retain the actual elaborated constructor and all body facts inside one opaque theorem. -/
private theorem initializer_program_packet :
    ∃ header : Header Gabbro.Stage0.Frontend.ConstWitness.initializerText,
      header.unit.fns.length = 1 ∧ Nonempty (Body header) := by
  let header : Header Gabbro.Stage0.Frontend.ConstWitness.initializerText := by
    refine {
      source := sourceFrom initializerInput initializerTail
      sourceEq := by exact sourceFrom_eq initializerInput initializerTail
      expanded := ?expanded
      requirements := ?requirements
      expansion := ?expansion
      constants := ?constants
      ordinary := by cbv
      metadata := by exact initializerTail.metadata
      candidate := ?candidate
      elaborated := ?elaborated }
    case expansion => cbv <;> exact Eq.refl _
    case constants =>
      change Konst.checkSourceConstants initializerInput.original = .ok ()
      unfold Konst.checkSourceConstants
      split
      · exact initializerTail.metadata
      · rfl
    case elaborated => cbv <;> exact Eq.refl _
  have count : header.unit.fns.length = 1 := by cbv
  let main : Fin header.unit.fns.length := ⟨0, by omega⟩
  -- Infer the complete canonical triple once, rather than repeatedly executing its selected getter.
  let code : EnsTy header.unit main × RumpTy header.unit main × ReqTy header.unit main := ?code
  have codeEq : lowerFnAt header.unit main = .ok code := by cbv <;> exact Eq.refl _
  have onlyMain (f : Fin header.unit.fns.length) : f = main := by
    apply Fin.ext
    have small : f.val < 1 := by simpa only [count] using f.isLt
    change f.val = 0
    omega
  let functions : Functions header.unit := {
    values := by
      change (f : Fin 1) → EnsTy header.unit f × RumpTy header.unit f × ReqTy header.unit f
      exact Fin.cases (motive := fun f : Fin 1 =>
        EnsTy header.unit f × RumpTy header.unit f × ReqTy header.unit f)
        code (fun f : Fin 0 => Fin.elim0 f)
    equations := by
      intro f
      have same := onlyMain f
      subst f
      exact codeEq
    noInvariants := by cbv
    noMeasures := by
      intro f
      have same := onlyMain f
      subst f
      cbv
    contracts := by cbv }
  -- Resolve the active scalar collector/literal path once, before the dependent whole-list fold.
  obtain ⟨value, evaluated, lower, upper⟩ := initializer_numeric_value
  have typed : uTypIn header.source.scopes.types [] (uRecordConstantTypes header.unit.records)
      [] [] (.atom "u8") = .ok (.int 0 255) := by
    change uTypIn initializerConservative.scope.types []
      (uRecordConstantTypes header.unit.records) [] [] (.atom "u8") = .ok (.int 0 255)
    apply initializer_scope_data
      (fun types _ _ => uTypIn types [] (uRecordConstantTypes header.unit.records)
        [] [] (.atom "u8") = .ok (.int 0 255))
    cbv
  have actualEvaluation : uKonstWert 0 255 header.source.scopes.functions
      header.source.scopes.values 64 (.call "increment" [.lit 3]) = some value := by
    change uKonstWert 0 255 initializerConservative.scope.functions
      initializerConservative.scope.values 64 (.call "increment" [.lit 3]) = some value
    exact evaluated
  have literal : uKonstZeile header.source.scopes.types header.source.scopes.functions
      header.source.scopes.values (.int 0 255) (.one (.call "increment" [.lit 3]))
      (uRecordConstant header.unit.records header.source.scopes.types
        header.source.scopes.functions header.source.scopes.values) = some (.lit value) := by
    rw [uKonstZeile_int, actualEvaluation]
    rfl
  have lowered : lowLit (u := header.unit) (Γ := []) (Λ := [])
      (.int 0 255) (.lit value) =
      .ok (.widen lower upper (.lit value)) := by
    simp only [lowLit, dite_eq_left lower, dite_eq_left upper]
  have itemSpine : ∃ firstSig firstBody lastSig lastBody,
      initializerInput.original = [.fnT firstSig firstBody,
        .constT "ANSWER" (.atom "u8") (.one (.call "increment" [.lit 3])),
        .fnT lastSig lastBody] := by
    refine ⟨?firstSig, ?firstBody, ?lastSig, ?lastBody, ?origin⟩
    case origin => cbv <;> exact Eq.refl _
  obtain ⟨firstSig, firstBody, lastSig, lastBody, origin⟩ := itemSpine
  have checked : ∀ item ∈ initializerInput.original,
      (Frontend.checkArrayItem header.unit header.source.scopes item).toOption.isSome = true := by
    have meanings : initializerInput.original.all
        (Frontend.checkConstantMeaning header.source.scopes.types
          header.source.scopes.functions header.source.scopes.values) = true := by
      change initializerInput.original.all
        (Frontend.checkConstantMeaning initializerConservative.scope.types
          initializerConservative.scope.functions initializerConservative.scope.values) = true
      exact initializerTail.constants
    intro item member
    have meaning : Frontend.checkConstantMeaning header.source.scopes.types
        header.source.scopes.functions header.source.scopes.values item = true :=
      List.all_eq_true.mp meanings item member
    rw [origin] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rfl
    · exact checked_constant_item header.unit header.source.scopes "ANSWER" (.atom "u8")
        (.one (.call "increment" [.lit 3])) (.int 0 255) (.lit value)
        (.widen lower upper (.lit value)) meaning typed literal lowered
    · rfl
  have arraysReady : (Frontend.checkArrays header.unit header.source.scopes
      initializerInput.original).toOption.isSome = true :=
    checked_array_items header.unit header.source.scopes initializerInput.original checked
  have entryFree : ∀ f : Fin header.unit.fns.length,
      (OldSource.clauses header.expanded (fnAt header.unit f).name).any
        OldSource.hasEntry = false := by
    intro f
    have same := onlyMain f
    subst f
    cbv
  have restored : OldSource.restore (pre108 header.source.prepared.elaborierbar)
      header.unit functions.program = .ok functions.program :=
    restore_entry_free _ header.expanded header.requirements header.unit functions.program
      header.expansion entryFree
  have accepted : OldSource.accepts header.unit functions.program = .ok true := by cbv
  refine ⟨header, count, ?body⟩
  case body =>
    refine ⟨{
      functions := functions
      main := main
      entry := by cbv
      initializers := by cbv
      arrays := (Frontend.checkArrays header.unit header.source.scopes
        initializerInput.original).toOption.get arraysReady
      arrayEq := by exact Gabbro.Grammatik.except_ok_get arraysReady
      program := functions.program
      restored := restored
      accepted := accepted }⟩

theorem initializer_compiled :
    ∃ result : Compiled Gabbro.Stage0.Frontend.ConstWitness.initializerText, compile Gabbro.Stage0.Frontend.ConstWitness.initializerText = .ok result ∧
      result.unit.fns.length = 1 := by
  obtain ⟨header, count, ⟨body⟩⟩ := initializer_program_packet
  obtain ⟨result, origin, unitEq⟩ := compiled header body
  exact ⟨result, origin, (congrArg (fun unit => unit.fns.length) unitEq).trans count⟩

end Gabbro.Stage0.Frontend.ConstPhases
