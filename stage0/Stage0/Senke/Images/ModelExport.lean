module

public import Stage0.Senke.Bild.Mehr.Goal
public import Stage0.Senke.Images.AccumulatorExport
public import Stage0.Senke.Welt.Initial.Arenas
import Grammatik.Logik.Vertraege.Pruefer.Goal

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Stage0.Senke

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
  accumulators : List.Forall₂ (ImageAccumulator output.compiled) (imageAccumulatorItems output.compiled) E.akku
  summary : ∀ item world value, E.Q item world value = true ↔
    ∃ old arguments, AxNach E.P.axVertrag item old arguments world value

/-- The post summary derived from the source covers every declared
    foreign postcondition, including those of software bindings. -/
theorem ImageModelUnit.postDeckt {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E) : PostDeckt E :=
  fun item _ old arguments world value post => (unit.summary item world value).mpr ⟨old, arguments, post⟩

/-- Export the exact checked descriptors, including the arena footprint
    selected by the finite, typed declaration reader. -/
theorem Emitted.image_model (output : Emitted src reserve options)
    (Q : AxEns (declOf output.compiled.unit))
    (sources : Option (Vertraege.Pruefer.AxiomSources Q))
    (summary : ∀ item world value, Q item world value = true ↔
      ∃ old arguments, AxNach output.compiled.program.axVertrag item old arguments world value)
    (arenas : List (ArenaOwnership.Body.ArenaIface (declOf output.compiled.unit)))
    (coverage : ∀ t : (declOf output.compiled.unit).Tab, (tabAt output.compiled.unit t).arena = true ↔
      ∃ arena ∈ arenas, arena.A.tab = t)
    (origin : ∀ arena ∈ arenas,
      ∃ storage : ResolvedArenaStorage output.compiled.unit arena.A.tab,
        resolveArenaStorage output.compiled.unit arena.A.tab = .ok storage ∧ storage.shape = arena.A)
    (acc : List (Kernzelle.AccumulatorDecl (declOf output.compiled.unit)))
    (accumulators : List.Forall₂ (ImageAccumulator output.compiled) (imageAccumulatorItems output.compiled) acc) :
    ImageModelUnit output { output.goalUnit Q with axiomSources := sources, arenen := arenas, akku := acc } := by
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
    arenaTables := coverage
    arenaStorage := origin
    accumulators := accumulators
    summary := summary
  }
  · intro root member
    change root ∈ ([] : List _) at member
    cases member

/-- A checked model export retains the very unit judged by the goal's
    checker, together with its correspondence to the emitted image. -/
structure CheckedImageUnit (output : Emitted src reserve options) where
  unit : Einheit (declOf output.compiled.unit)
  exactModel : ImageModelUnit output unit
  accepted : akzeptiertX_pruefer.akzeptiert unit output.fsA.1 output.lsA.1 output.csA.1 = true

/-- Read the model checked before the actual image was emitted. Its
    program, owned memory, starts and foreign logic come from that emission. -/
def Emitted.checkedUnit (output : Emitted src reserve options) : CheckedImageUnit output :=
  let plan := output.checkedImage.plan
  ⟨plan.unit output.sp0 (⟨output.compiled.main, output.args⟩ :: output.starts),
    output.image_model plan.post plan.axiomSources plan.postExact plan.arenas.localInterfaces
      plan.arenas.localInterfaces_coverage plan.arenas.localInterfaces_exact
      plan.accumulators.val plan.accumulators.property,
    output.checkedImage.accepted⟩

/-- Every set of bytes returned by the CLI already has the complete
    model verdict, with the exact canonical program and declared duties. -/
theorem irBild_checkImageUnit {bytes : List Runner.B} (wrote : irBild src reserve options = .ok bytes) :
    ∃ output : Emitted src reserve options, emit src reserve options = .ok output ∧
      output.bytes = bytes ∧ CanonicalSourceProgram output.compiled ∧
      ImageModelUnit output output.checkedUnit.unit ∧
      akzeptiertX_pruefer.akzeptiert output.checkedUnit.unit output.fsA.1 output.lsA.1 output.csA.1 = true ∧
      PostDeckt output.checkedUnit.unit ∧ NutzerPflichtA output.checkedUnit.unit := by
  obtain ⟨output, emitted, payload⟩ := irBild_emitted src reserve bytes wrote
  let checked := output.checkedUnit
  exact ⟨output, emitted, payload, compile_source_program src output.compiled, checked.exactModel,
    checked.accepted, checked.exactModel.postDeckt,
    nutzerPflicht_of_akzeptiert output.fsA output.lsA checked.accepted⟩

end Gabbro.Stage0
