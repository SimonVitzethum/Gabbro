/-
  The compiler's result and the goal checker: for a certifiable unit the Bool the goal theorem
  quantifies over (`akzeptiertX_pruefer`) answers `true` on the judged `Einheit` of the unit
  Stage 0 compiled (`OldSource.einheitDer`: the compiled entry as first start, the unit's derived
  checks), with the complete enumerations of its functions, locks and carriers.
-/
module
public import Stage0.Compiler
public import Stage0.IRBild
public import Stage0.Senke.Ausdruck.Old.JudgedUnit
public import Grammatik.Parser.Item.ElementTief.ModuleBody
public import Grammatik.Parser.Elab.UebersetzeAllg3.FunctionResults
@[expose] public section

namespace Gabbro.Stage0
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.Cover.Differenz Gabbro.Grammatik.Zielsatz

/-- The actual compiler's checker proves the semantic contract duties of
    each function of the exact restored typed program. -/
theorem Compiled.contract_duties {text : String} {options : Profil.Options}
    (result : Compiled text options) :
    ∀ f, Vertraege.Pruefer.ContractDuties result.program (sperrFamilie result.unit) f :=
  OldSource.accepts_contract_duties result.unit result.program result.main result.accepted

/-- The model's program judgment for the exact production enumerations.
    Unit-level ownership and initial-state checks have their own judgment. -/
theorem Compiled.admission [RootNativeFloat.Hardware] {text : String} {options : Profil.Options}
    (result : Compiled text options) :
    AkzeptiertSpecX result.program (sperrFamilie result.unit) (List.finRange result.unit.fns.length)
      (OldSource.judgedRoots result.unit result.main) [] [] :=
  OldSource.accepts_program_spec result.unit result.program result.main result.accepted

/-- At each typed AST function index, the checked program uses the body
    returned by lowering and exactly its lowered precondition. Restoring
    entry snapshots supplies the postcondition from the same source header. -/
theorem Compiled.function_from_ast {text : String} {options : Profil.Options}
    (result : Compiled text options) (f : (declOf result.unit).Fn) :
    ∃ raw functions lowered expanded requirements,
      lowerAllg result.unit = .ok (raw, functions) ∧
      lowerFnAt result.unit f = .ok lowered ∧ result.program.rumpf f = lowered.2.1 ∧
      result.program.requires f = (if (fnAt result.unit f).needs = [] then .tru else lowered.2.2) ∧
      expandU (pre108 result.source.prepared.elaborierbar) = .ok (expanded, requirements) ∧
      OldSource.atFunction (OldSource.koepfeVon expanded) result.unit raw f = .ok (result.program.ensures f) := by
  obtain ⟨raw, functions, assembled, restored⟩ := result.lowered
  obtain ⟨lowered, loweredAt, _, body, _⟩ := lowerAllg_fields result.unit raw functions assembled f
  obtain ⟨same, expanded, requirements, source, post⟩ := OldSource.restore_fields _ _ _ _ restored
  have bodyRestored := congrArg (fun p => p.rumpf f) same
  have preRestored := congrArg (fun p => p.requires f) same
  exact ⟨raw, functions, lowered, expanded, requirements, assembled, loweredAt,
    bodyRestored.trans body, preRestored.trans (lowerAllg_requires _ _ _ assembled f loweredAt),
    source, post f⟩

/-- Each CLI payload uses the AST derived from its original token sequence
    and the exact elaborated program whose functions pass the model's
    semantic contract checker. -/
theorem irBild_frontend_sound {text : String} {K : Nat} {options : Profil.Options} {bytes : List Runner.B}
    (emitted : irBild text K options = .ok bytes) :
    ∃ output : Emitted text K options, emit text K options = .ok output ∧ output.bytes = bytes ∧
      ItemSequence (output.compiled.source.tokens.length * 8 + 32) output.compiled.source.tokens
        output.compiled.source.items [.ende] ∧ CanonicalSourceProgram output.compiled ∧
      ∀ f, Vertraege.Pruefer.ContractDuties output.compiled.program (sperrFamilie output.compiled.unit) f := by
  obtain ⟨output, built, exactBytes⟩ := irBild_emitted text K bytes emitted
  exact ⟨output, built, exactBytes, parseTopTief_iff.mp output.compiled.source.parsed,
    compile_source_program text output.compiled, output.compiled.contract_duties⟩

/-- The declaration list actually used by the successful production check. -/
def Compiled.checkedDeclarations {text : String} {options : Profil.Options} (result : Compiled text options) :
    {checks : List (CheckDecl (declOf result.unit)) // uCheckDecls result.unit = .ok checks} :=
  match found : uCheckDecls result.unit with
  | .ok checks => ⟨checks, found⟩
  | .error _ => False.elim (by
    obtain ⟨_, _, _, derived, _⟩ := OldSource.accepts_core _ _ _ result.accepted
    rw [found] at derived
    cases derived)

/-- Premise (a) for the exported unit with its actual check declarations
    and the checked judgment on its initial memory and typed starts. -/
theorem Compiled.goal_checker {text : String} {options : Profil.Options}
    (result : Compiled text options) (Q : AxEns (declOf result.unit))
    (sp : Speicher (declOf result.unit))
    (args : Env (declOf result.unit) ((declOf result.unit).params result.main))
    (roots gestartet :
      List (Σ w : (declOf result.unit).Fn, Env (declOf result.unit) ((declOf result.unit).params w)))
    (hr : roots.map (·.1) = result.unit.roots.filterMap fun n => wurzelIdx result.unit n)
    (hg : gestartet.map (·.1) = result.unit.gestartet.filterMap fun n => wurzelIdx result.unit n)
    (hStart : unitStartGeprueftB
      (OldSource.einheitDer result.unit result.program Q sp result.main args roots gestartet result.checkedDeclarations.val)
      (List.finRange result.unit.fns.length) (List.finRange result.unit.locks.length) = true) :
    Zielsatz.akzeptiertX_pruefer.akzeptiert
      (OldSource.einheitDer result.unit result.program Q sp result.main args roots gestartet result.checkedDeclarations.val)
      (List.finRange result.unit.fns.length) (List.finRange result.unit.locks.length)
      ((List.finRange result.unit.tabs.length).map Sum.inl ++
        (List.finRange result.unit.globs.length).map Sum.inr) = true :=
  OldSource.accepts_gibt_pruefer result.unit result.program Q sp result.main args roots gestartet
    result.checkedDeclarations.val (hFn := inferInstance) (hC := result.checkedDeclarations.property) (hr := hr) (hg := hg) (h := result.accepted) (hStart := hStart)

/-- Premise (a) for a compiled unit whose only start is its entry (no declared roots, no
    run-time roots): the judged `Einheit` starts `result.main` alone and carries its actual check declarations. -/
theorem Compiled.goal_checker_main {text : String} {options : Profil.Options}
    (result : Compiled text options) (Q : AxEns (declOf result.unit))
    (sp : Speicher (declOf result.unit))
    (args : Env (declOf result.unit) ((declOf result.unit).params result.main))
    (hr : result.unit.roots = []) (hg : result.unit.gestartet = [])
    (hStart : unitStartGeprueftB
      (OldSource.einheitDer result.unit result.program Q sp result.main args [] [] result.checkedDeclarations.val)
      (List.finRange result.unit.fns.length) (List.finRange result.unit.locks.length) = true) :
    Zielsatz.akzeptiertX_pruefer.akzeptiert
      (OldSource.einheitDer result.unit result.program Q sp result.main args [] [] result.checkedDeclarations.val)
      (List.finRange result.unit.fns.length) (List.finRange result.unit.locks.length)
      ((List.finRange result.unit.tabs.length).map Sum.inl ++
        (List.finRange result.unit.globs.length).map Sum.inr) = true :=
  OldSource.accepts_gibt_pruefer_main result.unit result.program Q sp result.main args
    (hFn := inferInstance) result.checkedDeclarations.val result.checkedDeclarations.property (hr := hr) (hg := hg) (h := result.accepted) (hStart := hStart)

private theorem findRoot_eq_fnIdx (functions : List UFn) (name : String) :
    (List.finRange functions.length).find? (fun f => (functions.get f).name == name) =
      (fnIdx functions name).toOption := by
  induction functions with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.length_cons, List.finRange_succ, List.find?_cons, List.get_cons_zero, fnIdx]
    cases same : first.name == name with
    | true => simp only [same, ↓reduceIte, Except.toOption]
    | false =>
      simp only [same, Bool.false_eq_true, ↓reduceIte, List.find?_map, Function.comp_def, List.get_cons_succ', ih]
      cases fnIdx rest name <;> rfl

/-- The selected entry is named by the profile and has a unique typed
    function index in the admitted AST. -/
theorem Compiled.entry_name_unique {text : String} {options : Profil.Options}
    (result : Compiled text options) :
    (fnAt result.unit result.main).name = Profil.entryName options ∧
      ∀ f : (declOf result.unit).Fn, (fnAt result.unit f).name = Profil.entryName options → f = result.main := by
  have found : (List.finRange result.unit.fns.length).find?
      (fun f => (fnAt result.unit f).name == Profil.entryName options) = some result.main := by
    change (List.finRange result.unit.fns.length).find?
      (fun f => (result.unit.fns.get f).name == Profil.entryName options) = some result.main
    simp only [findRoot_eq_fnIdx, result.entry, Except.toOption]
    rfl
  have nameEq := List.find?_some
    (p := fun f => (fnAt result.unit f).name == Profil.entryName options) found
  have named : (fnAt result.unit result.main).name = Profil.entryName options := beq_iff_eq.mp nameEq
  refine ⟨named, ?_⟩
  intro f entryNamed
  apply Fin.ext
  have bound (i : (declOf result.unit).Fn) : i.val < (result.unit.fns.map (·.name)).length := by
    simpa only [List.length_map] using i.isLt
  apply result.functionNames.eq_of_getElem_eq (bound f) (bound result.main)
  have same := entryNamed.trans named.symm
  unfold fnAt at same
  rw [List.get_eq_getElem (i := f), List.get_eq_getElem (i := result.main)] at same
  simpa only [List.getElem_map] using same

/-- The explicit concurrent prefix has precisely the function occurrences
    judged by the source checker, with their original order and multiplicity. -/
theorem StartArgument.Plan.concurrent_roots {u : UProg} {items : List SItemTief}
    {main : (declOf u).Fn} (plan : StartArgument.Plan u items main) (world : World (declOf u))
    (dispatch : plan.dispatch = []) (runtime : u.gestartet = []) :
    (plan.starts world).map (·.1) = u.roots.filterMap (wurzelIdx u) := by
  have named := plan.namedOrigin
  rw [dispatch, runtime] at named
  change (Except.ok [] : Except String (List (StartArgument.NamedStart u))) = .ok plan.named at named
  have empty : plan.named = [] := (Except.ok.inj named).symm
  rw [plan.canonicalRoots, dispatch, List.append_nil]
  simp only [StartArgument.Plan.starts, empty, List.map_nil, List.filter_nil, List.append_nil,
    List.map_map, List.filterMap_map]
  change plan.concurrent.map (fun start => start.resolved.function) =
    plan.concurrent.filterMap (fun start => wurzelIdx u start.name)
  have lookup (start : StartArgument.SourceStart u items) :
      wurzelIdx u start.name = some start.resolved.function := by
    unfold wurzelIdx fnAt
    rw [findRoot_eq_fnIdx, start.resolved.named]
    rfl
  simp only [lookup]
  exact (congrFun (List.filterMap_eq_map'
    (f := fun start : StartArgument.SourceStart u items => start.resolved.function)) plan.concurrent).symm

/-- Premise (a) for the exact typed roots and initial memory serialized by the
    emitter, when every additional root comes from an explicit concurrent member. -/
theorem Emitted.goal_checker_concurrent {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) (Q : AxEns (declOf output.compiled.unit))
    (dispatch : output.startPlan.dispatch = []) (runtime : output.compiled.unit.gestartet = [])
    (start : unitStartGeprueftB
      (OldSource.einheitDer output.compiled.unit output.compiled.program Q
        (Senke.initialWorld output.compiled.unit output.initialValid).speicher
        output.compiled.main output.args output.starts [] output.compiled.checkedDeclarations.val)
      (List.finRange output.compiled.unit.fns.length) (List.finRange output.compiled.unit.locks.length) = true) :
    akzeptiertX_pruefer.akzeptiert
      (OldSource.einheitDer output.compiled.unit output.compiled.program Q
        (Senke.initialWorld output.compiled.unit output.initialValid).speicher
        output.compiled.main output.args output.starts [] output.compiled.checkedDeclarations.val)
      (List.finRange output.compiled.unit.fns.length) (List.finRange output.compiled.unit.locks.length)
      ((List.finRange output.compiled.unit.tabs.length).map Sum.inl ++
        (List.finRange output.compiled.unit.globs.length).map Sum.inr) = true :=
  output.compiled.goal_checker Q _ output.args output.starts []
    (output.startPlan.concurrent_roots _ dispatch runtime) (OldSource.gestartet_leer _ runtime) start

/-- **The image of a unit without declared and run-time roots starts no thread besides `main`**:
    its canonical start plan has no `concurrent` occurrence and no named root. -/
theorem Emitted.starts_leer {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) (hr : output.compiled.unit.roots = [])
    (hg : output.compiled.unit.gestartet = []) : output.starts = [] := by
  have h0 : output.startPlan.concurrent.map (·.name) ++ output.startPlan.dispatch = [] :=
    output.startPlan.canonicalRoots.symm.trans hr
  have hcon : output.startPlan.concurrent = [] :=
    List.map_eq_nil_iff.mp (List.append_eq_nil_iff.mp h0).1
  have hdis : output.startPlan.dispatch = [] := (List.append_eq_nil_iff.mp h0).2
  have hn := output.startPlan.namedOrigin
  rw [hdis, hg] at hn
  change (Except.ok [] : Except String (List (StartArgument.NamedStart output.compiled.unit))) =
    .ok output.startPlan.named at hn
  have hnamed : output.startPlan.named = [] := (Except.ok.inj hn).symm
  simp only [Emitted.starts, StartArgument.Plan.starts, hcon, hnamed, List.map_nil, List.filter_nil,
    List.append_nil]

/-- **Premise (a) on the emitted image of a unit whose only start is its entry**: the judged
    `Einheit` starts `main` with exactly the environment the image carries (`output.args`,
    `Senke.mainEnv`), and the image starts no other thread (`Emitted.starts_leer`). -/
theorem Emitted.goal_checker_main {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) (Q : AxEns (declOf output.compiled.unit))
    (sp : Speicher (declOf output.compiled.unit))
    (hr : output.compiled.unit.roots = []) (hg : output.compiled.unit.gestartet = [])
    (hStart : unitStartGeprueftB
      (OldSource.einheitDer output.compiled.unit output.compiled.program Q sp output.compiled.main output.args [] [] output.compiled.checkedDeclarations.val)
      (List.finRange output.compiled.unit.fns.length) (List.finRange output.compiled.unit.locks.length) = true) :
    Zielsatz.akzeptiertX_pruefer.akzeptiert
      (OldSource.einheitDer output.compiled.unit output.compiled.program Q sp output.compiled.main
        output.args [] [] output.compiled.checkedDeclarations.val)
      (List.finRange output.compiled.unit.fns.length) (List.finRange output.compiled.unit.locks.length)
      ((List.finRange output.compiled.unit.tabs.length).map Sum.inl ++
        (List.finRange output.compiled.unit.globs.length).map Sum.inr) = true ∧
      output.starts = [] :=
  ⟨output.compiled.goal_checker_main Q sp output.args hr hg hStart, output.starts_leer hr hg⟩

end Gabbro.Stage0
