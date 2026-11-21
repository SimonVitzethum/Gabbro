module

public import Stage0.Senke.Bild.Mehr.Goal

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {src : String} {reserve : Nat} {options : Profil.Options}

def imageAccumulatorItems (output : Emitted src reserve options) : List SItemTief :=
  (uMembers (pre108 output.compiled.source.prepared.elaborierbar)).filter fun item =>
    match item with
    | .accT .. => true
    | _ => false

/-- An accumulator descriptor elaborates the actual selected declaration
    with its generated cells, locks and functions. -/
def ImageAccumulator (output : Emitted src reserve options) (item : SItemTief)
    (acc : Kernzelle.AccumulatorDecl (declOf output.compiled.unit)) : Prop :=
  let unit := output.compiled.unit
  let scopes := output.compiled.source.scopes
  (∃ cells locks, uAkkuDecl scopes.values scopes.types item cells locks
    acc.kernAbfrage acc.aktualisiere acc.falte = .ok acc) ∧
  (∀ i, (unit.globs.get (acc.zellen i)).name = acc.name ++ "#zelle" ++ toString i.val) ∧
  (∀ i, (unit.locks.get (acc.sperren i)).name = acc.name ++ "#sperre" ++ toString i.val) ∧
  (fnAt unit acc.kernAbfrage).name = acc.name ++ "#query" ∧
  (fnAt unit acc.aktualisiere).name = acc.name ++ "#aktualisiere" ∧
  (fnAt unit acc.falte).name = acc.name ++ "#falte"

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
  accumulators : List.Forall₂ (ImageAccumulator output) (imageAccumulatorItems output) E.akku
  summary : ∀ item world value, E.Q item world value = true ↔
    ∃ old arguments, AxNach E.P.axVertrag item old arguments world value

/-- The post summary derived from the source covers every declared
    foreign postcondition, including those of software bindings. -/
theorem ImageModelUnit.postDeckt {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E) : PostDeckt E :=
  fun item _ old arguments world value post => (unit.summary item world value).mpr ⟨old, arguments, post⟩

private theorem Emitted.image_model_without_ownership (output : Emitted src reserve options)
    (Q : AxEns (declOf output.compiled.unit))
    (sources : Option (Vertraege.Pruefer.AxiomSources Q))
    (summary : ∀ item world value, Q item world value = true ↔
      ∃ old arguments, AxNach output.compiled.program.axVertrag item old arguments world value)
    (noOwnership : OldSource.zertifizierbar output.compiled.unit = true)
    (noAccumulators : imageAccumulatorItems output = []) :
    ImageModelUnit output { output.goalUnit Q with axiomSources := sources } := by
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
    accumulators := ?_
    summary := summary
  }
  · intro root member
    change root ∈ ([] : List _) at member
    cases member
  · intro t
    have closed := OldSource.zertifizierbar_ohne_arena _ noOwnership (output.compiled.unit.tabs.get t)
      (List.get_mem _ _)
    change _ ↔ ∃ arena ∈ ([] : List (ArenaOwnership.Body.ArenaIface (declOf output.compiled.unit))), arena.A.tab = t
    simp only [closed, Bool.false_eq_true, List.not_mem_nil, false_and, exists_false]
  · rw [noAccumulators]
    exact .nil

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
  refine ⟨output.image_model_without_ownership _ _ ?_ noOwnership noAccumulators,
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
  ⟨output.image_model_without_ownership _ _ checked.summary.exactPost noOwnership noAccumulators,
    output.foreign_goal_checker produced⟩

end Gabbro.Stage0
