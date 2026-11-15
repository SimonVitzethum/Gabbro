module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1.Teil1Basis

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.PoolCertificate

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Vertraege.Pruefer Vertraege.Pruefer.SelectionWitness Invarianten.Pruefer

abbrev scalar := Ty.int 0 100

def cell : Observation zD := .slot () () 0

def number (value : Wert zD scalar) : Int := value.n

def domain : LocalDomain zD scalar :=
  (localDomain (D := zD) 128 scalar).toOption.get (by rfl)

theorem domain_result : localDomain (D := zD) 128 scalar = .ok domain := rfl

def post (value : Wert zD scalar) :=
  (postFormula zPB zLies .nil value).toOption.get (by rfl)

theorem post_result (value : Wert zD scalar) :
    postFormula zPB zLies .nil value = .ok (post value) := rfl

theorem post_meaning (value : Wert zD scalar) (values : Assignment (Observation zD)) :
    (post value).val.denote values ↔ number value = values cell := by
  exact (lower_denote _ values).trans Iff.rfl

abbrev slotExpr : Expr zD [] zL scalar := .slot () () zIdx zDarf

def slotRelation (value : Wert zD scalar) :
    { formula : LProp (Observation zD) // ∀ world,
      formula.denote (assignment world) ↔
        eval world (.slot () () zIdx zDarf) world (.nil : Env zD []) = value } :=
  ⟨.eq (.var cell) (.konst (number value)), fun _ =>
    ⟨fun same => zahl_ext same, fun same => congrArg Zahl.n same⟩⟩

theorem slotRelation_result (value : Wert zD scalar) :
    localEquality (τ := scalar) slotExpr .nil value = .ok (slotRelation value) := by
  with_unfolding_all
    simp only [localEquality, scalar]
    simp only [slotExpr]
    delta integerEquality
    rfl

theorem slotRelation_meaning (value : Wert zD scalar) (values : Assignment (Observation zD)) :
    (slotRelation value).val.denote values ↔ values cell = number value := Iff.rfl

abbrev variableExpr : Expr zD [scalar] zL scalar := .var .here

def varRelation (bound value : Wert zD scalar) :
    { formula : LProp (Observation zD) // ∀ world,
      formula.denote (assignment world) ↔
        eval world variableExpr world (.cons bound .nil) = value } :=
  ⟨.eq (.konst (number bound)) (.konst (number value)), fun _ =>
    ⟨fun same => zahl_ext same, fun same => congrArg Zahl.n same⟩⟩

theorem varRelation_result (bound value : Wert zD scalar) :
    localEquality variableExpr (.cons bound .nil) value =
      .ok (varRelation bound value) := by
  simp only [localEquality, integerEquality, variableExpr]
  rfl

theorem varRelation_meaning (bound value : Wert zD scalar) (values : Assignment (Observation zD)) :
    (varRelation bound value).val.denote values ↔ number bound = number value := Iff.rfl

def invariants : InvariantFormula zPB (zD.invs.filter (schuldet zLies)) :=
  (invariantFormula zPB []).toOption.get (by rfl)

def goals : Vertraege.Pruefer.Goals zD (vertragVon zD zLies) [] :=
  contractGoals zPB zLies .nil invariants

def returned (value : Wert zD scalar) := goals.returned value

def leaf (value : Wert zD scalar) :
    Condition (fun (_ : Runtime zPB (fun _ => []) zS) world => denotes (returned value) world) :=
  (requireCondition (returned value)).toOption.get (by rfl)

theorem leaf_result (value : Wert zD scalar) :
    requireCondition (returned value) = .ok (leaf value) := rfl

theorem leaf_meaning (value : Wert zD scalar) (values : Assignment (Observation zD)) :
    (leaf value).formula.denote values ↔ number value = values cell := by
  change (conj (post value).val .tru).denote values ↔ _
  rw [conj_denote]
  simp only [QF.denote, and_true]
  exact post_meaning value values

def tail : Endblock zD (vertragVon zD zLies) false [scalar] zL :=
  .ret (.val (.var .here)) (List.Perm.refl _)

def branch (sources : Invarianten.Pruefer.LockSources zS) (bound : Wert zD scalar) :=
  ending (S := zS) (requiresPolicy zPB) (lockFormula zS sources) {} none 127
    tail (.cons bound .nil) (goals.shrink scalar)

/-- The return half of the actual 101-value binder, proved for every selected value. -/
theorem branch_valid (sources : Invarianten.Pruefer.LockSources zS) (bound : Wert zD scalar) :
    ∃ result, branch sources bound = .ok result ∧
      ∀ values, values cell = number bound → result.formula.denote values := by
  with_unfolding_all
    have each (value : Wert zD scalar) :
        ∃ relation head, localEquality variableExpr (.cons bound .nil) value = .ok relation ∧
          requireCondition (program := zPB) (checked := fun _ => []) (S := zS) (returned value) = .ok head ∧
          ∀ values, values cell = number bound → relation.val.denote values → head.formula.denote values := by
      refine ⟨varRelation bound value, leaf value, varRelation_result bound value, leaf_result value, ?_⟩
      intro values ready related
      apply (leaf_meaning value values).mpr
      have same := (varRelation_meaning bound value values).mp related
      omega
    obtain ⟨pre, hpre, valid⟩ := localSelect_valid 128 variableExpr (.cons bound .nil)
      (fun value (_ : Runtime zPB (fun _ => []) zS) world => denotes (returned value) world)
      (fun value => requireCondition (returned value)) domain domain_result
      (fun values => values cell = number bound) each
    cases result : branch sources bound with
    | error cause =>
        delta branch tail at result
        rw [Vertraege.Pruefer.ending.eq_2] at result
        delta returnCondition at result
        rw [hpre] at result
        dsimp only [bind, Except.bind, pure, Except.pure] at result
        cases result
    | ok out =>
        refine ⟨out, rfl, ?_⟩
        have shape : out.formula = pre.formula := by
          delta branch tail at result
          rw [Vertraege.Pruefer.ending.eq_2] at result
          delta returnCondition at result
          rw [hpre] at result
          dsimp only [bind, Except.bind, pure, Except.pure] at result
          exact (congrArg Condition.formula (Except.ok.inj result)).symm
        rw [shape]
        exact valid

end Gabbro.Grammatik.Zielsatz.PoolCertificate
