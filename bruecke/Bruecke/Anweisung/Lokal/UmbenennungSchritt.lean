module
public import Bruecke.Anweisung.Lokal.Umbenennung
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Body

theorem evalAll_renameScalars (name : String → Option String) (s : State) :
    ∀ es es', renameStep.renameScalars name es = some es' →
      evalAll s es' = evalAll ⟨s.world, visibleBinding name s.local'⟩ es
  | [], es', h => by
      cases h
      rfl
  | e :: es, es', h => by
      simp only [renameStep.renameScalars] at h
      split at h
      · rename_i e' rest he hr
        cases h
        simp only [evalAll, eval_renameScalar name s e e' he,
          evalAll_renameScalars name s es rest hr]
      · cases h

/-- A renamed store or call keeps the actual caller binding, while its scalar reads use the
    visible projection. Callee parameter names and the callee precondition are unchanged. -/
theorem step_renameStep (name : String → Option String) (ρB : Env) (s : State)
    (raw renamed : Stmt) (h : renameStep name raw = some renamed) :
    step ρB renamed s =
      match step ρB raw ⟨s.world, visibleBinding name s.local'⟩ with
      | .running t => .running ⟨t.world, s.local'⟩
      | o => o := by
  cases raw
  case assign c i f v =>
    simp only [renameStep] at h
    split at h
    · rename_i i' v' hi hv
      cases h
      simp only [step, eval_renameScalar name s i i' hi, eval_renameScalar name s v v' hv]
      cases eval ⟨s.world, visibleBinding name s.local'⟩ i with
      | none => rfl
      | some k => cases k <;> cases eval ⟨s.world, visibleBinding name s.local'⟩ v <;> rfl
    · cases h
  case assignGlobal g v =>
    simp only [renameStep] at h
    cases hv : renameScalar name v with
    | none => rw [hv] at h; cases h
    | some v' =>
      rw [hv] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst renamed
      simp only [step, eval_renameScalar name s v v' hv]
      cases eval ⟨s.world, visibleBinding name s.local'⟩ v <;> rfl
  case call c ps es pre =>

    simp only [renameStep] at h
    cases hr : renameStep.renameScalars name es with
    | none => rw [hr] at h; cases h
    | some es' =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst renamed
      simp only [step, evalAll_renameScalars name s es es' hr]
      cases evalAll ⟨s.world, visibleBinding name s.local'⟩ es with
      | none => rfl
      | some vs =>
        dsimp only
        cases eval ⟨s.world, bindAll ps vs (fun _ => .absent)⟩ pre with
        | none => rfl
        | some v =>
          cases v <;> try rfl
          case bool b => cases b <;> rfl
  all_goals cases h

end Gabbro.Bruecke
