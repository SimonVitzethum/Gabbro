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
@[expose] public section

namespace Gabbro.Stage0
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Parser.Cover.Differenz Gabbro.Grammatik.Zielsatz

/-- Premise (a) of the goal theorem for what Stage 0 compiled. The judged `Einheit` starts the
    compiled entry `result.main` with `args` (the image's start environment of `main`,
    `Senke.mainEnv`), then `roots` naming the unit's declared roots, and carries the run-time
    roots `gestartet` and the unit's derived checks `checks` (`hC`). `zertifizierbar` excludes
    the forms whose goal leg the compiler's own check does not judge or the elaborator does not
    export (arena tables, declared checks, accumulators). The compiler assumes neither: a unit
    outside `zertifizierbar` compiles, and this theorem is silent on it. -/
theorem Compiled.goal_checker {text : String} {options : Profil.Options}
    (result : Compiled text options) (Q : AxEns (declOf result.unit))
    (sp : Speicher (declOf result.unit))
    (args : Env (declOf result.unit) ((declOf result.unit).params result.main))
    (roots gestartet :
      List (Σ w : (declOf result.unit).Fn, Env (declOf result.unit) ((declOf result.unit).params w)))
    (checks : List (CheckDecl (declOf result.unit)))
    (hZ : OldSource.zertifizierbar result.unit = true)
    (hC : uCheckDecls result.unit = .ok checks)
    (hr : roots.map (·.1) = result.unit.roots.filterMap fun n => wurzelIdx result.unit n)
    (hg : gestartet.map (·.1) = result.unit.gestartet.filterMap fun n => wurzelIdx result.unit n) :
    Zielsatz.akzeptiertX_pruefer.akzeptiert
      (OldSource.einheitDer result.unit result.program Q sp result.main args roots gestartet checks)
      (List.finRange result.unit.fns.length) (List.finRange result.unit.locks.length)
      ((List.finRange result.unit.tabs.length).map Sum.inl ++
        (List.finRange result.unit.globs.length).map Sum.inr) = true :=
  OldSource.accepts_gibt_pruefer result.unit result.program Q sp result.main args roots gestartet
    checks (hFn := inferInstance) (hZ := hZ) (hC := hC) (hr := hr) (hg := hg) (h := result.accepted)

/-- Premise (a) for a compiled unit whose only start is its entry (no declared roots, no
    run-time roots): the judged `Einheit` starts `result.main` alone and carries no check. -/
theorem Compiled.goal_checker_main {text : String} {options : Profil.Options}
    (result : Compiled text options) (Q : AxEns (declOf result.unit))
    (sp : Speicher (declOf result.unit))
    (args : Env (declOf result.unit) ((declOf result.unit).params result.main))
    (hZ : OldSource.zertifizierbar result.unit = true)
    (hr : result.unit.roots = []) (hg : result.unit.gestartet = []) :
    Zielsatz.akzeptiertX_pruefer.akzeptiert
      (OldSource.einheitDer result.unit result.program Q sp result.main args [] [] [])
      (List.finRange result.unit.fns.length) (List.finRange result.unit.locks.length)
      ((List.finRange result.unit.tabs.length).map Sum.inl ++
        (List.finRange result.unit.globs.length).map Sum.inr) = true :=
  OldSource.accepts_gibt_pruefer_main result.unit result.program Q sp result.main args
    (hFn := inferInstance) (hZ := hZ) (hr := hr) (hg := hg) (h := result.accepted)

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
    (hZ : OldSource.zertifizierbar output.compiled.unit = true)
    (hr : output.compiled.unit.roots = []) (hg : output.compiled.unit.gestartet = []) :
    Zielsatz.akzeptiertX_pruefer.akzeptiert
      (OldSource.einheitDer output.compiled.unit output.compiled.program Q sp output.compiled.main
        output.args [] [] [])
      (List.finRange output.compiled.unit.fns.length) (List.finRange output.compiled.unit.locks.length)
      ((List.finRange output.compiled.unit.tabs.length).map Sum.inl ++
        (List.finRange output.compiled.unit.globs.length).map Sum.inr) = true ∧
      output.starts = [] :=
  ⟨output.compiled.goal_checker_main Q sp output.args hZ hr hg, output.starts_leer hr hg⟩

end Gabbro.Stage0
