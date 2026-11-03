module
public import Stage0.Frontend.Aliases
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Extract precisely the statement shape supported by the canonical const evaluator. -/
def UKonstFn.returnExpr? (fn : UKonstFn) : Option SExpr :=
  match fn.rumpf with
  | .block [] (some (.ret (some expression))) => some expression
  | _ => none

theorem UKonstFn.returnExpr?_eq_some (fn : UKonstFn) (expression : SExpr) :
    fn.returnExpr? = some expression ↔
      fn.rumpf = .block [] (some (.ret (some expression))) := by
  unfold UKonstFn.returnExpr?
  split <;> simp_all

/-- Compile-time function types denote the same canonical integer types as runtime signatures. -/
theorem fieldType_sound (env : List (String × (Int × Int))) (ty : STyp) (lo hi : Int)
    (h : uFeldTyp env ty = .ok (lo, hi)) :
    uTyp env [] [] ty = .ok (.int lo hi) := by
  cases ty <;> simp only [uFeldTyp] at h
  all_goals try contradiction
  case atom name => simp [uTyp, uTypIn, h]
  case range base lower upper exclusive =>
    cases hl : uSchranke env lower <;> cases hu : uSchranke env upper <;>
      simp only [hl, hu] at h
    all_goals try contradiction
    all_goals
      have hp := Except.ok.inj h
      cases hp
      simp [uTyp, uTypIn, hl, hu]

/-- Predicate clauses are evaluated by the canonical evaluator and certified against
    machine G at source call substitution. Effects must remain pure. -/
def evaluationClauses (clauses : List SKlausel) : Bool :=
  clauses.all fun
    | .effs effects => effects.all fun | .pure => true | _ => false
    | .needs _ | .gives _ => true
    | .cost _ => true
    | _ => false

/-- Extract exact parameter/result ranges for the existing single-return const-function model.
    Source bodies and signatures remain unchanged in the declaration list. The canonical elaborator
    omits const functions from runtime function bodies; their evaluation therefore needs this proof. -/
def constantFunction (env : List (String × (Int × Int))) : SItemTief → Option UKonstFn
  | .fnT { art := "const", name, params, res := some result, fehler := none, klauseln := clauses }
      (.block [] (some (.ret (some body)))) => do
    if !evaluationClauses clauses then none else do
    let range ← (uFeldTyp env result).toOption
    let args ← params.mapM fun (name, ty) =>
      ((uFeldTyp env ty).toOption).map fun r => (name, r)
    pure ⟨name, args.map (fun (n, r) => (n, .int r.1 r.2)), .int range.1 range.2, .block [] (some (.ret (some body))), ⟨"const", name, params, some result, none, clauses⟩, [], []⟩
  | _ => none

/-- The origin of a compile-time function candidate, expressed in canonical type elaborations. -/
def FunctionMeaning (env : List (String × (Int × Int))) (item : SItemTief) (fn : UKonstFn) : Prop :=
  ∃ params result clauses expression range args,
    item = .fnT ⟨"const", fn.name, params, some result, none, clauses⟩
      (.block [] (some (.ret (some expression)))) ∧
    fn.returnExpr? = some expression ∧
    evaluationClauses clauses = true ∧
    (uFeldTyp env result).toOption = some range ∧
    params.mapM (fun (name, ty) => ((uFeldTyp env ty).toOption).map fun r => (name, r)) = some args ∧
    fn.erg = .int range.1 range.2 ∧
    fn.params = args.map (fun (n, r) => (n, .int r.1 r.2)) ∧
    fn.signature = ⟨"const", fn.name, params, some result, none, clauses⟩

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
          exact ⟨params, result, clauses, body, range, args, rfl,
            (UKonstFn.returnExpr?_eq_some _ _).mpr rfl, hs, hr, hp, rfl, rfl, rfl⟩
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
      ⟨"identity", [("x", .int 0 100)], .int 0 100, .block [] (some (.ret (some (.variable "x")))), ⟨"const", "identity", [("x", .atom "Count")], some (.atom "Count"), none, []⟩, [], []⟩ :=
  constantFunction_sound _ _ _ (by rfl)

end Gabbro.Stage0.Frontend
