module

public import Stage0.Senke.Bild.Mehr.Goal
public import Stage0.Senke.Images.AccumulatorExport
public import Stage0.Senke.Welt.Initial.Arenas
import Grammatik.Logik.Vertraege.Pruefer.Goal

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- The source's canonical bodies and initial declarations used by both
    the compiler and the goal theorem are the same. -/
structure ImageModelUnit (output : Emitted src reserve options)
    (E : Einheit (declOf output.compiled.unit)) : Prop where
  program : E.P = output.compiled.program
  locks : E.S = Gabbro.Grammatik.Parser.Cover.Differenz.sperrFamilie output.compiled.unit
  lockSources : HEq E.lockFormulas (Gabbro.Grammatik.Parser.Cover.Differenz.sperrQuellen output.compiled.unit)
  memory : E.sp0 = output.sp0
  starts : E.starts = ⟨output.compiled.main, output.args⟩ :: output.starts
  checks : E.pruefungen = output.compiled.checkedDeclarations.val
  measure : E.measure = Gabbro.Grammatik.Parser.Cover.Differenz.massVon output.compiled.unit
  pointerSignatures : E.pointerSignatures =
    some (Gabbro.Grammatik.Parser.Cover.Differenz.zeigerSignaturen output.compiled.unit)
  runtimeRoots : E.gestartet.map (·.1) =
    output.compiled.unit.gestartet.filterMap (Gabbro.Grammatik.Parser.Cover.Differenz.wurzelIdx output.compiled.unit)
  runtimeParams : ∀ root ∈ E.gestartet, (declOf output.compiled.unit).params root.1 = []
  arenaTables : ∀ t : (declOf output.compiled.unit).Tab, (output.compiled.unit.tabs.get t).arena = true ↔
    ∃ arena ∈ E.arenen, arena.A.tab = t
  arenaStorage : ∀ arena ∈ E.arenen,
    ∃ storage : ResolvedArenaStorage output.compiled.unit arena.A.tab,
      resolveArenaStorage output.compiled.unit arena.A.tab = .ok storage ∧ storage.shape = arena.A
  accumulators : List.Forall₂ (ImageAccumulator output) (imageAccumulatorItems output) E.akku
  summary : ∀ item world value, E.Q item world value = true ↔
    ∃ old arguments, AxNach E.P.axVertrag item old arguments world value

/-- The post summary derived from the source covers every declared
    foreign postcondition, including those of software bindings. -/
theorem ImageModelUnit.postDeckt {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E) : PostDeckt E :=
  fun item _ old arguments world value post => (unit.summary item world value).mpr ⟨old, arguments, post⟩

/-- Export the exact checked descriptors of a unit whose declaration
    table contains no arena. -/
theorem Emitted.image_model_without_arenas (output : Emitted src reserve options)
    (Q : AxEns (declOf output.compiled.unit))
    (sources : Option (Vertraege.Pruefer.AxiomSources Q))
    (summary : ∀ item world value, Q item world value = true ↔
      ∃ old arguments, AxNach output.compiled.program.axVertrag item old arguments world value)
    (noArenas : (output.compiled.unit.tabs.all fun t => !t.arena) = true)
    (acc : List (Kernzelle.AccumulatorDecl (declOf output.compiled.unit)))
    (accumulators : List.Forall₂ (ImageAccumulator output) (imageAccumulatorItems output) acc) :
    ImageModelUnit output { output.goalUnit Q with axiomSources := sources, akku := acc } := by
  refine {
    program := rfl
    locks := rfl
    lockSources := HEq.rfl
    memory := rfl
    starts := rfl
    checks := rfl
    measure := rfl
    pointerSignatures := rfl
    runtimeRoots := OldSource.gestartet_leer _ output.compiled.hostedStarts.noDynamicRoots
    runtimeParams := ?_
    arenaTables := ?_
    arenaStorage := ?_
    accumulators := accumulators
    summary := summary
  }
  · intro root member
    change root ∈ ([] : List _) at member
    cases member
  · intro t
    have marked := List.all_eq_true.mp noArenas _ (List.get_mem output.compiled.unit.tabs t)
    have closed : (output.compiled.unit.tabs.get t).arena = false := by
      cases ht : (output.compiled.unit.tabs.get t).arena with
      | false => rfl
      | true =>
        rw [ht, Bool.not_true] at marked
        cases marked
    change _ ↔ ∃ arena ∈ ([] : List (ArenaOwnership.Body.ArenaIface (declOf output.compiled.unit))), arena.A.tab = t
    simp only [closed, Bool.false_eq_true, List.not_mem_nil, false_and, exists_false]
  · intro arena present
    change arena ∈ ([] : List _) at present
    cases present

private theorem Emitted.image_model_empty_accumulators (output : Emitted src reserve options)
    (Q : AxEns (declOf output.compiled.unit))
    (sources : Option (Vertraege.Pruefer.AxiomSources Q))
    (summary : ∀ item world value, Q item world value = true ↔
      ∃ old arguments, AxNach output.compiled.program.axVertrag item old arguments world value)
    (noOwnership : OldSource.zertifizierbar output.compiled.unit = true)
    (noAccumulators : imageAccumulatorItems output = []) :
    ImageModelUnit output { output.goalUnit Q with axiomSources := sources } :=
  output.image_model_without_arenas Q sources summary (OldSource.zertifizierbar_teile noOwnership).1
    [] (by rw [noAccumulators]; exact .nil)

/-- For the part of the current emitter with no foreign or ownership
    declarations, the checked output supplies the specified source unit
    and its checker verdict without an extra unit-check hypothesis. -/
theorem Emitted.checked_image_model_empty (output : Emitted src reserve options)
    (noAxioms : output.compiled.unit.axs.length = 0)
    (noOwnership : OldSource.zertifizierbar output.compiled.unit = true)
    (noAccumulators : imageAccumulatorItems output = []) :
    let E := output.goalUnit (axWahr _)
    ImageModelUnit output E ∧
      akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true := by
  refine ⟨output.image_model_empty_accumulators _ _ ?_ noOwnership noAccumulators,
    output.goal_checker_concurrent _ (output.goal_axiomFree _ noAxioms)⟩
  intro item _ _
  exact False.elim ((Nat.not_lt_zero item.val) (noAxioms ▸ item.isLt))

/-- An actual retained foreign-logic certificate supplies the exact model
    unit and full checker verdict, including its original foreign posts. -/
theorem Emitted.checked_image_model_foreign (output : Emitted src reserve options)
    {checked : output.CheckedForeign} (produced : output.foreignLogic = .ok checked)
    (noOwnership : OldSource.zertifizierbar output.compiled.unit = true)
    (noAccumulators : imageAccumulatorItems output = []) :
    let E := withForeignSummary (output.goalUnit (axWahr _)) checked.summary
    ImageModelUnit output E ∧
      akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true :=
  ⟨output.image_model_empty_accumulators _ _ checked.summary.exactPost noOwnership noAccumulators,
    output.foreign_goal_checker produced⟩

/-- The actual returned payload determines the canonical program once.
    Its retained foreign check certifies the same unit for the full
    checker, with the source's foreign post and declared starts. -/
theorem irBild_checked_foreign_unit {bytes : List Runner.B}
    (wrote : irBild src reserve options = .ok bytes) :
    ∃ output : Emitted src reserve options, emit src reserve options = .ok output ∧
      output.bytes = bytes ∧ CanonicalSourceProgram output.compiled ∧
      ∀ {checked : output.CheckedForeign}, output.foreignLogic = .ok checked →
        OldSource.zertifizierbar output.compiled.unit = true → imageAccumulatorItems output = [] →
        let E := withForeignSummary (output.goalUnit (axWahr _)) checked.summary
        ImageModelUnit output E ∧
          akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true ∧ PostDeckt E := by
  obtain ⟨output, emitted, payload⟩ := irBild_emitted src reserve bytes wrote
  refine ⟨output, emitted, payload, compile_source_program src output.compiled, ?_⟩
  intro checked produced noOwnership noAccumulators
  obtain ⟨unit, accepted⟩ := output.checked_image_model_foreign produced noOwnership noAccumulators
  exact ⟨unit, accepted, unit.postDeckt⟩

/-- A checked model export retains the very unit judged by the goal's
    checker, together with its correspondence to the emitted image. -/
structure CheckedImageUnit (output : Emitted src reserve options) where
  unit : Einheit (declOf output.compiled.unit)
  exactModel : ImageModelUnit output unit
  accepted : akzeptiertX_pruefer.akzeptiert unit output.fsA.1 output.lsA.1 output.csA.1 = true

/-- Retain the exact model and the verdict computed on that model. -/
def Emitted.finishImageUnit (output : Emitted src reserve options)
    (unit : Einheit (declOf output.compiled.unit)) (exactModel : ImageModelUnit output unit) :
    Except String (CheckedImageUnit output) :=
  if accepted : checkAkzeptiertX unit output.fsA.1 output.lsA.1 output.csA.1 = true then
    .ok ⟨unit, exactModel, (akzeptiertX_pruefer_decision unit _ _ _).trans accepted⟩
  else .error "ir: model checker refused the exported image unit"

theorem Emitted.finishImageUnit_ok (output : Emitted src reserve options)
    (unit : Einheit (declOf output.compiled.unit)) (exactModel : ImageModelUnit output unit)
    (accepted : akzeptiertX_pruefer.akzeptiert unit output.fsA.1 output.lsA.1 output.csA.1 = true) :
    output.finishImageUnit unit exactModel = .ok ⟨unit, exactModel, accepted⟩ := by
  have verdict := (akzeptiertX_pruefer_decision unit output.fsA.1 output.lsA.1 output.csA.1).symm.trans accepted
  simp only [finishImageUnit, dif_pos verdict]

/-- Resolve the logic decision on the actual emitted unit. Both the
    axiom-free and foreign branches produce the same checked interface.
    A missing arena export or refused model check returns a diagnostic. -/
def Emitted.checkImageUnit (output : Emitted src reserve options) :
    Except String (CheckedImageUnit output) := do
  if noArenas : (output.compiled.unit.tabs.all fun t => !t.arena) = true then
    let acc ← collectImageAccumulators output (imageAccumulatorItems output)
    if noAxioms : output.compiled.unit.axs.length = 0 then
      let initial := output.goalUnit (axWahr _)
      output.finishImageUnit { initial with akku := acc.val }
        (output.image_model_without_arenas _ initial.axiomSources
          (fun item _ _ => False.elim ((Nat.not_lt_zero item.val) (noAxioms ▸ item.isLt)))
          noArenas acc.val acc.property)
    else
      let certificate ← output.foreignLogic
      let initial := withForeignSummary (output.goalUnit (axWahr _)) certificate.summary
      output.finishImageUnit { initial with akku := acc.val }
        (output.image_model_without_arenas _ initial.axiomSources certificate.summary.exactPost
          noArenas acc.val acc.property)
  else throw "ir: arena declarations have no checked image export"

/-- The deployed checker already certifies every emitted axiom-free
    unit in the complete no-ownership fragment. Running the exact
    exporter on it yields precisely that verdict on the same unit. -/
theorem Emitted.checkImageUnit_axiomFree (output : Emitted src reserve options)
    (noAxioms : output.compiled.unit.axs.length = 0)
    (noOwnership : OldSource.zertifizierbar output.compiled.unit = true)
    (noAccumulators : imageAccumulatorItems output = []) :
    ∃ checked : CheckedImageUnit output, output.checkImageUnit = .ok checked ∧
      checked.unit = output.goalUnit (axWahr _) := by
  obtain ⟨model, accepted⟩ := output.checked_image_model_empty noAxioms noOwnership noAccumulators
  have noArenas := (OldSource.zertifizierbar_teile noOwnership).1
  refine ⟨⟨output.goalUnit (axWahr _), model, accepted⟩, ?_, rfl⟩
  simp only [checkImageUnit, dif_pos noArenas, collectImageAccumulators_empty output noAccumulators,
    bind, Except.bind, dif_pos noAxioms]
  exact output.finishImageUnit_ok _ model accepted

/-- A retained, successful foreign certificate yields the exact checked
    unit when the source has ordinary carriers and no accumulators. -/
theorem Emitted.checkImageUnit_foreign (output : Emitted src reserve options)
    {certificate : output.CheckedForeign} (produced : output.foreignLogic = .ok certificate)
    (foreign : output.compiled.unit.axs.length ≠ 0)
    (noOwnership : OldSource.zertifizierbar output.compiled.unit = true)
    (noAccumulators : imageAccumulatorItems output = []) :
    ∃ checked : CheckedImageUnit output, output.checkImageUnit = .ok checked ∧
      checked.unit = withForeignSummary (output.goalUnit (axWahr _)) certificate.summary := by
  obtain ⟨model, accepted⟩ := output.checked_image_model_foreign produced noOwnership noAccumulators
  have noArenas := (OldSource.zertifizierbar_teile noOwnership).1
  refine ⟨⟨_, model, accepted⟩, ?_, rfl⟩
  simp only [checkImageUnit, dif_pos noArenas, collectImageAccumulators_empty output noAccumulators,
    bind, Except.bind, dif_neg foreign, produced]
  exact output.finishImageUnit_ok _ model accepted

/-- The returned bytes and the complete checker verdict on their exact
    model can be obtained from one canonical emission and one export. -/
theorem irBild_checkImageUnit {bytes : List Runner.B} (wrote : irBild src reserve options = .ok bytes) :
    ∃ output : Emitted src reserve options, emit src reserve options = .ok output ∧
      output.bytes = bytes ∧ CanonicalSourceProgram output.compiled ∧
      ∀ checked : CheckedImageUnit output, output.checkImageUnit = .ok checked →
        PostDeckt checked.unit ∧ NutzerPflichtA checked.unit := by
  obtain ⟨output, emitted, payload⟩ := irBild_emitted src reserve bytes wrote
  exact ⟨output, emitted, payload, compile_source_program src output.compiled,
    fun checked _ => ⟨checked.exactModel.postDeckt,
      nutzerPflicht_of_akzeptiert output.fsA output.lsA checked.accepted⟩⟩

end Gabbro.Stage0
