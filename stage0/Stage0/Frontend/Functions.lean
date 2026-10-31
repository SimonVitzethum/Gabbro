import Stage0.Frontend.Aliases

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Compile-time function types denote the same canonical integer types as runtime signatures. -/
theorem fieldType_sound (env : List (String × (Int × Int))) (ty : STyp) (lo hi : Int)
    (h : uFeldTyp env ty = .ok (lo, hi)) :
    uTyp env [] ty = .ok (.int lo hi) := by
  cases ty <;> simp only [uFeldTyp] at h
  all_goals try contradiction
  case atom name => simp [uTyp, h]
  case range base lower upper exclusive =>
    cases hl : uSchranke env lower <;> cases hu : uSchranke env upper <;>
      simp only [hl, hu] at h
    all_goals try contradiction
    all_goals
      have hp := Except.ok.inj h
      cases hp
      simp [uTyp, hl, hu]

/-- The current canonical const evaluator has no contract/effect interpreter. Only pure effects
    and declared costs may accompany a newly extracted body; logical contracts need a proved call rule. -/
def evaluationClauses (clauses : List SKlausel) : Bool :=
  clauses.all fun
    | .effs effects => effects.all fun | .pure => true | _ => false
    | .cost _ => true
    | _ => false

/-- Extract exact parameter/result ranges for the existing single-return const-function model.
    Source bodies and signatures remain unchanged for runtime compilation. -/
def constantFunction (env : List (String × (Int × Int))) : SItemTief → Option UKonstFn
  | .fnT { art := "const", name, params, res := some result, fehler := none, klauseln := clauses }
      (.block [] (some (.ret (some body)))) => do
    if !evaluationClauses clauses then none else do
    let range ← (uFeldTyp env result).toOption
    let args ← params.mapM fun (name, ty) =>
      ((uFeldTyp env ty).toOption).map fun r => (name, r)
    pure ⟨name, args, range, body⟩
  | _ => none

/-- The origin of a compile-time function candidate, expressed in canonical type elaborations. -/
def FunctionMeaning (env : List (String × (Int × Int))) (item : SItemTief) (fn : UKonstFn) : Prop :=
  ∃ params result clauses,
    item = .fnT ⟨"const", fn.name, params, some result, none, clauses⟩
      (.block [] (some (.ret (some fn.rumpf)))) ∧
    evaluationClauses clauses = true ∧
    (uFeldTyp env result).toOption = some fn.erg ∧
    params.mapM (fun (name, ty) => ((uFeldTyp env ty).toOption).map fun r => (name, r)) = some fn.params

/-- Every extracted candidate has the original body/name and exactly the canonical signature ranges. -/
theorem constantFunction_sound (env : List (String × (Int × Int))) (item : SItemTief) (fn : UKonstFn)
    (h : constantFunction env item = some fn) : FunctionMeaning env item fn := by
  unfold constantFunction at h
  split at h
  · rename_i name params result clauses body
    by_cases hs : evaluationClauses clauses = true
    · simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hr : (uFeldTyp env result).toOption with
      | none => simp [hr] at h
      | some range =>
        cases hp : params.mapM (fun (name, ty) => ((uFeldTyp env ty).toOption).map fun r => (name, r)) with
        | none => simp [hr, hp] at h
        | some args =>
          simp [hr, hp] at h
          subst fn
          exact ⟨params, result, clauses, rfl, hs, hr, hp⟩
    · simp [hs] at h
  · contradiction

def constantFunctions (env : List (String × (Int × Int))) (items : List SItemTief) : List UKonstFn :=
  items.filterMap (constantFunction env)

/-- No compile-time function is introduced without a source declaration and canonical range checks. -/
theorem constantFunctions_sound (env : List (String × (Int × Int))) (items : List SItemTief) :
    ∀ fn ∈ constantFunctions env items, ∃ item ∈ items, FunctionMeaning env item fn := by
  intro fn h
  simp only [constantFunctions, List.mem_filterMap] at h
  obtain ⟨item, hm, hc⟩ := h
  exact ⟨item, hm, constantFunction_sound env item fn hc⟩

theorem constantFunction_sound_zeuge :
    FunctionMeaning [("Count", (0, 100))]
      (.fnT ⟨"const", "identity", [("x", .atom "Count")], some (.atom "Count"), none, []⟩
        (.block [] (some (.ret (some (.variable "x"))))))
      ⟨"identity", [("x", (0, 100))], (0, 100), .variable "x"⟩ :=
  constantFunction_sound _ _ _ (by rfl)

end Gabbro.Stage0.Frontend
