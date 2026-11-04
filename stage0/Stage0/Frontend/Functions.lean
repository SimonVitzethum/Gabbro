module
public import Stage0.Frontend.Aliases
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Compile-time function types denote the same canonical integer types as runtime signatures. -/
theorem fieldType_sound (env : List (String × (Int × Int))) (ty : STyp) (lo hi : Int)
    (h : uFeldTyp env ty = .ok (lo, hi)) :
    uTyp env [] [] [] ty = .ok (.int lo hi) := by
  unfold uFeldTyp at h
  cases ht : uTyp env [] [] [] ty with
  | error e => simp only [ht, reduceCtorEq] at h
  | ok canonical =>
    cases canonical <;> simp only [ht, Except.ok.injEq, reduceCtorEq] at h
    case int lower upper =>
      cases h
      rfl

/-- The scalar reader is exactly the integer projection of canonical source typing. This
    transports a final validation fact back to the scalar classifier without a caller premise. -/
theorem fieldType_iff (env : List (String × (Int × Int))) (ty : STyp) (lo hi : Int) :
    uFeldTyp env ty = .ok (lo, hi) ↔ uTyp env [] [] [] ty = .ok (.int lo hi) := by
  constructor
  · exact fieldType_sound env ty lo hi
  · intro typed
    simp only [uFeldTyp, typed]

/-- The scalar candidate gate and canonical collector retain identical ordered parameter types. -/
private theorem scalarParameters (env : List (String × (Int × Int)))
    (params : List (String × STyp)) (args : List (String × (Int × Int)))
    (accepted : params.mapM (fun (name, ty) =>
      ((uFeldTyp env ty).toOption).map fun range => (name, range)) = some args) :
    params.mapM (fun (name, ty) => (uTyp env [] [] [] ty).map fun type => (name, type)) =
      .ok (args.map (fun (name, range) => (name, .int range.1 range.2))) := by
  induction params generalizing args with
  | nil =>
    change some [] = some args at accepted
    cases accepted
    rfl
  | cons param rest ih =>
    rcases param with ⟨name, ty⟩
    cases ht : uFeldTyp env ty with
    | error error => simp [List.mapM_cons, ht, Except.toOption] at accepted
    | ok range =>
      cases hr : rest.mapM (fun (name, ty) =>
          ((uFeldTyp env ty).toOption).map fun range => (name, range)) with
      | none => simp [List.mapM_cons, ht, Except.toOption, hr] at accepted
      | some tail =>
        have same : (name, range) :: tail = args := by
          simpa [List.mapM_cons, ht, Except.toOption, hr] using accepted
        subst args
        simp only [List.mapM_cons, fieldType_sound env ty range.1 range.2 ht,
          Except.map, bind, Except.bind, ih tail hr, pure, Except.pure, List.map_cons]

/-- The old base-ignoring reader admitted this nonnumeric range. The canonical reader refuses. -/
theorem fieldType_noninteger_range_refused_zeuge :
    uFeldTyp [] (.range (.atom "bool") (.lit 0) (.lit 1) false) =
      .error "range requires a numeric type and known bounds" := rfl

/-- Shadowing a reserved spelling in scalar candidates cannot turn Bool into an integer. -/
theorem fieldType_builtin_shadow_refused_zeuge :
    uFeldTyp [("bool", (0, 1))] (.atom "bool") =
      .error "field type without G form: bool" := rfl

/-- Ordinary integer aliases retain their exact original bounds. -/
theorem fieldType_sound_zeuge :
    uTyp [("Small", (-10, 100))] [] [] [] (.atom "Small") = .ok (.int (-10) 100) :=
  fieldType_sound _ _ _ _ rfl

/-- Predicate clauses are evaluated by the canonical evaluator and certified against
    machine G at source call substitution. Effects must remain pure. -/
def evaluationClauses (clauses : List SKlausel) : Bool :=
  clauses.all fun
    | .effs effects => effects.all fun | .pure => true | _ => false
    | .needs _ | .gives _ => true
    | .cost _ => true
    | _ => false

/-- The scalar candidate gate retains its clause and range checks, then delegates construction
    to the canonical collector. Full source signatures and statement bodies remain unchanged. -/
def constantFunction (env : List (String × (Int × Int))) : SItemTief → Option UKonstFn
  | .fnT { art := "const", name, params, res := some result, fehler := none,
      klauseln := clauses, generics := generics }
      (.block [] (some (.ret (some body)))) => do
    if !evaluationClauses clauses then none else do
    let _ ← (uFeldTyp env result).toOption
    let _ ← params.mapM fun (name, ty) =>
      ((uFeldTyp env ty).toOption).map fun r => (name, r)
    (uKonstFnsWith env [.fnT ⟨"const", name, params, some result, none, clauses, generics⟩
      (.block [] (some (.ret (some body))))]).head?
  | _ => none

/-- The origin of a compile-time function candidate, expressed in canonical type elaborations. -/
def FunctionMeaning (env : List (String × (Int × Int))) (item : SItemTief) (fn : UKonstFn) : Prop :=
  ∃ params result clauses generics expression range args,
    item = .fnT ⟨"const", fn.name, params, some result, none, clauses, generics⟩
      (.block [] (some (.ret (some expression)))) ∧
    fn.rumpf = .block [] (some (.ret (some expression))) ∧
    evaluationClauses clauses = true ∧
    (uFeldTyp env result).toOption = some range ∧
    params.mapM (fun (name, ty) => ((uFeldTyp env ty).toOption).map fun r => (name, r)) = some args ∧
    fn.erg = .int range.1 range.2 ∧
    fn.params = args.map (fun (n, r) => (n, .int r.1 r.2)) ∧
    fn.signature = ⟨"const", fn.name, params, some result, none, clauses, generics⟩

/-- Every extracted candidate has the original body/name and exactly the canonical signature ranges. -/
theorem constantFunction_sound (env : List (String × (Int × Int))) (item : SItemTief) (fn : UKonstFn)
    (h : constantFunction env item = some fn) : FunctionMeaning env item fn := by
  unfold constantFunction at h
  split at h
  · rename_i name params result clauses generics body
    by_cases hs : evaluationClauses clauses = true
    · simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hr : (uFeldTyp env result).toOption with
      | none => simp [hr] at h
      | some range =>
        cases hp : params.mapM (fun (name, ty) => ((uFeldTyp env ty).toOption).map fun r => (name, r)) with
        | none => simp [hr, hp] at h
        | some args =>
          have resultType : uFeldTyp env result = .ok range := by
            cases ht : uFeldTyp env result with
            | error error => simp [ht, Except.toOption] at hr
            | ok value =>
              have same : value = range := by
                simpa only [ht, Except.toOption, Option.some.injEq] using hr
              subst value
              rfl
          have typed := fieldType_sound env result range.1 range.2 resultType
          have parameters := scalarParameters env params args hp
          simp [hr, hp, uKonstFnsWith, typed, parameters, strEq] at h
          subst fn
          exact ⟨params, result, clauses, generics, body, range, args,
            rfl, rfl, hs, hr, hp, rfl, rfl, rfl⟩
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
      (.fnT ⟨"const", "identity", [("x", .atom "Count")], some (.atom "Count"), none, [], []⟩
        (.block [] (some (.ret (some (.variable "x"))))))
      ⟨"identity", [("x", .int 0 100)], .int 0 100, .block [] (some (.ret (some (.variable "x")))), ⟨"const", "identity", [("x", .atom "Count")], some (.atom "Count"), none, [], []⟩, [], []⟩ :=
  constantFunction_sound _ _ _ (by rfl)

end Gabbro.Stage0.Frontend
