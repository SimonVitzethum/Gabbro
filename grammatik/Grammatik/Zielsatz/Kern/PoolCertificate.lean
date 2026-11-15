module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1.Teil1Basis

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.PoolCertificate

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Vertraege.Pruefer Vertraege.Pruefer.SelectionWitness Invarianten.Pruefer

abbrev scalar := Ty.int 0 100

def domain : LocalDomain zD scalar :=
  (localDomain (D := zD) 128 scalar).toOption.get (by rfl)

theorem domain_result : localDomain (D := zD) 128 scalar = .ok domain := rfl

def post (value : Zahl 0 100) :=
  (postFormula zPB zLies .nil value).toOption.get (by rfl)

theorem post_result (value : Zahl 0 100) :
    postFormula zPB zLies .nil value = .ok (post value) := rfl

theorem post_meaning (value : Zahl 0 100) (values : Assignment (Observation zD)) :
    (post value).val.denote values ↔ value.n = values (.slot () () 0) := by
  exact (lower_denote _ values).trans Iff.rfl

abbrev slotExpr : Expr zD [] zL scalar := .slot () () zIdx zDarf

def slotRelation (value : Zahl 0 100) :
    { formula : LProp (Observation zD) // ∀ world,
      formula.denote (assignment world) ↔
        eval world (.slot () () zIdx zDarf) world (.nil : Env zD []) = value } :=
  ⟨.eq (.var (.slot () () 0)) (.konst value.n), fun _ =>
    ⟨fun same => zahl_ext same, fun same => congrArg Zahl.n same⟩⟩

theorem slotRelation_result (value : Zahl 0 100) :
    localEquality (τ := scalar) slotExpr .nil value = .ok (slotRelation value) := by
  with_unfolding_all
    simp only [localEquality, scalar]
    simp only [slotExpr]
    unfold integerEquality
    rfl

theorem slotRelation_meaning (value : Zahl 0 100) (values : Assignment (Observation zD)) :
    (slotRelation value).val.denote values ↔ values (.slot () () 0) = value.n := Iff.rfl

abbrev variableExpr : Expr zD [scalar] zL scalar := .var .here

def varRelation (bound value : Zahl 0 100) :
    { formula : LProp (Observation zD) // ∀ world,
      formula.denote (assignment world) ↔
        eval world variableExpr world (.cons bound .nil) = value } :=
  ⟨.eq (.konst bound.n) (.konst value.n), fun _ =>
    ⟨fun same => zahl_ext same, fun same => congrArg Zahl.n same⟩⟩

theorem varRelation_result (bound value : Zahl 0 100) :
    localEquality variableExpr (.cons bound .nil) value =
      .ok (varRelation bound value) := by
  simp only [localEquality, integerEquality, variableExpr]
  rfl

theorem varRelation_meaning (bound value : Zahl 0 100) (values : Assignment (Observation zD)) :
    (varRelation bound value).val.denote values ↔ bound.n = value.n := Iff.rfl

def invariants : InvariantFormula zPB (zD.invs.filter (schuldet zLies)) :=
  (invariantFormula zPB []).toOption.get (by rfl)

def goals : Vertraege.Pruefer.Goals zD (vertragVon zD zLies) [] :=
  contractGoals zPB zLies .nil invariants

def returned (value : Zahl 0 100) := goals.returned value

def leaf (value : Zahl 0 100) :
    Condition (fun (_ : Runtime zPB (fun _ => []) zS) world => denotes (returned value) world) :=
  (requireCondition (returned value)).toOption.get (by rfl)

theorem leaf_result (value : Zahl 0 100) :
    requireCondition (returned value) = .ok (leaf value) := rfl

theorem leaf_meaning (value : Zahl 0 100) (values : Assignment (Observation zD)) :
    (leaf value).formula.denote values ↔ value.n = values (.slot () () 0) := by
  change (conj (post value).val .tru).denote values ↔ _
  rw [conj_denote]
  simp only [QF.denote, and_true]
  exact post_meaning value values

def tail : Endblock zD (vertragVon zD zLies) false [scalar] zL :=
  .ret (.val (.var .here)) (List.Perm.refl _)

def branch (sources : Invarianten.Pruefer.LockSources zS) (bound : Zahl 0 100) :=
  ending (S := zS) (requiresPolicy zPB) (lockFormula zS sources) {} none 127
    tail (.cons bound .nil) (goals.shrink scalar)

/-- The return half of the actual 101-value binder, proved for every selected value. -/
theorem branch_valid (sources : Invarianten.Pruefer.LockSources zS) (bound : Zahl 0 100) :
    ∃ result, branch sources bound = .ok result ∧
      ∀ values, values (.slot () () 0) = bound.n → result.formula.denote values := by
  with_unfolding_all
    have each (value : Zahl 0 100) :
        ∃ relation head, localEquality variableExpr (.cons bound .nil) value = .ok relation ∧
          requireCondition (program := zPB) (checked := fun _ => []) (S := zS) (returned value) = .ok head ∧
          ∀ values, values (.slot () () 0) = bound.n → relation.val.denote values → head.formula.denote values := by
      refine ⟨varRelation bound value, leaf value, varRelation_result bound value, leaf_result value, ?_⟩
      intro values ready related
      apply (leaf_meaning value values).mpr
      have same := (varRelation_meaning bound value values).mp related
      omega
    obtain ⟨pre, hpre, valid⟩ := localSelect_valid 128 variableExpr (.cons bound .nil)
      (fun value (_ : Runtime zPB (fun _ => []) zS) world => denotes (returned value) world)
      (fun value => requireCondition (returned value)) domain domain_result
      (fun values => values (.slot () () 0) = bound.n) each
    cases result : branch sources bound with
    | error cause =>
        simp only [branch, tail] at result
        rw [ending] at result
        simp only [returnCondition, hpre, bind, Except.bind, pure,
          Except.pure, reduceCtorEq] at result
    | ok out =>
        refine ⟨out, rfl, ?_⟩
        have shape : out.formula = pre.formula := by
          simp only [branch, tail] at result
          rw [ending] at result
          simp only [returnCondition, hpre, bind, Except.bind, pure,
            Except.pure] at result
          exact (congrArg Condition.formula (Except.ok.inj result)).symm
        rw [shape]
        exact valid

end Gabbro.Grammatik.Zielsatz.PoolCertificate
