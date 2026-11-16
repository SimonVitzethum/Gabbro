module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
public import Grammatik.Logik.Invarianten.Pruefer.Program
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

/-- Shared source metadata for the probe, pool and linked library fixtures. -/
def zPoolSources : Invarianten.Pruefer.LockSources zS := fun _ => some
  { resources := [], expression := .tru, correct := fun _ => rfl }

/-- The footprint witness keeps the guarded read/write and every body. Its
    unrelated imported posts use truth rather than unsupported old-memory logic. -/
def zPCFragment : Programm zD := { zPC with ensures := fun _ => .tru }

namespace PoolCertificate

local instance : DecidableEq zD.Ax := inferInstanceAs (DecidableEq Empty)

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Vertraege.Pruefer Vertraege.Pruefer.SelectionWitness Invarianten.Pruefer

attribute [local implicit_reducible] Invarianten.Frag.Payload

abbrev scalar := Ty.int 0 100
abbrev context := zD.params zLies

def arguments : Env zD context := .nil

def cell : Observation zD := .slot () () 0

def number (value : Wert zD scalar) : Int := value.n

def domain : LocalDomain zD scalar :=
  (localDomain (D := zD) 128 scalar).toOption.get (by rfl)

theorem domain_result : localDomain (D := zD) 128 scalar = .ok domain := rfl

def post (value : Wert zD scalar) :=
  (postFormula zPB zLies arguments value).toOption.get (by rfl)

theorem post_result (value : Wert zD scalar) :
    postFormula zPB zLies arguments value = .ok (post value) := rfl

theorem post_meaning (value : Wert zD scalar) (values : Assignment (Observation zD)) :
    (post value).val.denote values ↔ number value = values cell := by
  exact (lower_denote _ values).trans Iff.rfl

abbrev slotExpr : Expr zD context zL scalar := .slot () () zIdx zDarf

def slotRelation (value : Wert zD scalar) :
    { formula : LProp (Observation zD) // ∀ world,
      formula.denote (assignment world) ↔
        eval world (.slot () () zIdx zDarf) world arguments = value } :=
  ⟨.eq (.var cell) (.konst (number value)), fun _ =>
    ⟨fun same => zahl_ext same, fun same => congrArg Zahl.n same⟩⟩

theorem slotRelation_result (value : Wert zD scalar) :
    localEquality (τ := scalar) slotExpr arguments value = .ok (slotRelation value) := by
  with_unfolding_all
    simp only [localEquality, scalar]
    simp only [slotExpr]
    delta integerEquality
    rfl

theorem slotRelation_meaning (value : Wert zD scalar) (values : Assignment (Observation zD)) :
    (slotRelation value).val.denote values ↔ values cell = number value := Iff.rfl

abbrev variableExpr : Expr zD (scalar :: context) zL scalar := .var .here

def varRelation (bound value : Wert zD scalar) :
    { formula : LProp (Observation zD) // ∀ world,
      formula.denote (assignment world) ↔
        eval world variableExpr world (.cons bound arguments) = value } :=
  ⟨.eq (.konst (number bound)) (.konst (number value)), fun _ =>
    ⟨fun same => zahl_ext same, fun same => congrArg Zahl.n same⟩⟩

theorem varRelation_result (bound value : Wert zD scalar) :
    localEquality variableExpr (.cons bound arguments) value =
      .ok (varRelation bound value) := by
  simp only [localEquality, integerEquality, variableExpr]
  rfl

theorem varRelation_meaning (bound value : Wert zD scalar) (values : Assignment (Observation zD)) :
    (varRelation bound value).val.denote values ↔ number bound = number value := Iff.rfl

def invariants : InvariantFormula zPB (zD.invs.filter (schuldet zLies)) :=
  (invariantFormula zPB []).toOption.get (by rfl)

def goals : Vertraege.Pruefer.Goals zD (vertragVon zD zLies) context :=
  contractGoals zPB zLies arguments invariants

def returned (value : Wert zD scalar) := goals.returned value

def leaf (program : Programm zD) (value : Wert zD scalar) :
    Condition (fun (_ : Runtime program (fun _ => []) zS) world => denotes (returned value) world) :=
  (requireCondition (returned value)).toOption.get (by rfl)

theorem leaf_result (program : Programm zD) (value : Wert zD scalar) :
    requireCondition (returned value) = .ok (leaf program value) := rfl

theorem leaf_meaning (program : Programm zD) (value : Wert zD scalar) (values : Assignment (Observation zD)) :
    (leaf program value).formula.denote values ↔ number value = values cell := by
  change (conj (post value).val .tru).denote values ↔ _
  rw [conj_denote]
  simp only [QF.denote, and_true]
  exact post_meaning value values

def returnExpr : ErgExpr zD (scalar :: context) zL (vertragVon zD zLies).erg := .val (.var .here)

theorem returnedResources : List.Perm zL (vertragVon zD zLies).ende := List.Perm.refl _

def tail : Endblock zD (vertragVon zD zLies) false (scalar :: context) zL :=
  .ret returnExpr returnedResources

theorem returnCondition_eq (bound : Wert zD scalar) :
    returnCondition (program := program) (S := zS) 128 returnExpr (.cons bound arguments)
      (goals.shrink scalar).returned =
    localSelect 128 variableExpr (.cons bound arguments)
      (fun value (_ : Runtime program (fun _ => []) zS) world => denotes (returned value) world)
      (fun value => requireCondition (returned value)) := rfl

def branch (program : Programm zD) (sources : Invarianten.Pruefer.LockSources zS) (bound : Wert zD scalar) :=
  ending (S := zS) (requiresPolicy program) (lockFormula zS sources) {} none 127
    tail (.cons bound arguments) (goals.shrink scalar)

/-- The return half of the actual 101-value binder, proved for every selected value. -/
theorem branch_valid (program : Programm zD) (sources : Invarianten.Pruefer.LockSources zS) (bound : Wert zD scalar) :
    ∃ result, branch program sources bound = .ok result ∧
      ∀ values, values cell = number bound → result.formula.denote values := by
  with_unfolding_all
    have each (value : Wert zD scalar) :
        ∃ relation head, localEquality variableExpr (.cons bound arguments) value = .ok relation ∧
          requireCondition (program := program) (checked := fun _ => []) (S := zS) (returned value) = .ok head ∧
          ∀ values, values cell = number bound → relation.val.denote values → head.formula.denote values := by
      refine ⟨varRelation bound value, leaf program value, varRelation_result bound value, leaf_result program value, ?_⟩
      intro values ready related
      apply (leaf_meaning program value values).mpr
      have same := (varRelation_meaning bound value values).mp related
      omega
    obtain ⟨pre, hpre, valid⟩ := localSelect_valid 128 variableExpr (.cons bound arguments)
      (fun value (_ : Runtime program (fun _ => []) zS) world => denotes (returned value) world)
      (fun value => requireCondition (returned value)) domain domain_result
      (fun values => values cell = number bound) each
    cases result : branch program sources bound with
    | error cause =>
        delta branch tail at result
        rw [Vertraege.Pruefer.ending.eq_2] at result
        rw [returnCondition_eq] at result
        rw [hpre] at result
        dsimp only [bind, Except.bind, pure, Except.pure] at result
        cases result
    | ok out =>
        refine ⟨out, rfl, ?_⟩
        have shape : out.formula = pre.formula := by
          delta branch tail at result
          rw [Vertraege.Pruefer.ending.eq_2] at result
          rw [returnCondition_eq] at result
          rw [hpre] at result
          dsimp only [bind, Except.bind, pure, Except.pure] at result
          exact (congrArg Condition.formula (Except.ok.inj result)).symm
        rw [shape]
        exact valid

def body : Endblock zD (vertragVon zD zLies) false context zL := .bind slotExpr tail

theorem body_eq : zPB.rumpf zLies = body := rfl

def compiled (program : Programm zD) (sources : LockSources zS) :=
  ending (S := zS) (requiresPolicy program) (lockFormula zS sources) {} none 128 body arguments goals

/-- The complete generated binder VC is valid for every integer assignment. -/
theorem compiled_valid (program : Programm zD) (sources : LockSources zS) :
    ∃ result, compiled program sources = .ok result ∧ ∀ values, result.formula.denote values := by
  have each (value : Wert zD scalar) :
      ∃ relation head, localEquality slotExpr arguments value = .ok relation ∧
        branch program sources value = .ok head ∧
        ∀ values, True → relation.val.denote values → head.formula.denote values := by
    obtain ⟨head, hhead, valid⟩ := branch_valid program sources value
    refine ⟨slotRelation value, head, slotRelation_result value, hhead, ?_⟩
    intro values _ related
    exact valid values ((slotRelation_meaning value values).mp related)
  obtain ⟨pre, hpre, valid⟩ := localSelect_valid 128 slotExpr arguments _ (branch program sources)
    domain domain_result (fun _ => True) each
  cases result : compiled program sources with
  | error cause =>
      delta compiled body at result
      rw [Vertraege.Pruefer.ending.eq_8] at result
      change (do
        let pre ← localSelect 128 slotExpr arguments _ (branch program sources)
        pure ((pre.read zL slotExpr.orte).map _)) = .error cause at result
      rw [hpre] at result
      dsimp only [bind, Except.bind, pure, Except.pure] at result
      cases result
  | ok out =>
      refine ⟨out, rfl, ?_⟩
      have shape : out.formula = pre.formula := by
        delta compiled body at result
        rw [Vertraege.Pruefer.ending.eq_8] at result
        change (do
          let pre ← localSelect 128 slotExpr arguments _ (branch program sources)
          pure ((pre.read zL slotExpr.orte).map _)) = .ok out at result
        rw [hpre] at result
        dsimp only [bind, Except.bind, pure, Except.pure] at result
        exact (congrArg Condition.formula (Except.ok.inj result)).symm
      rw [shape]
      exact fun values => valid values trivial

def resultDomain : Results zD (zD.erg zLies) :=
  { values := domain.values, complete := domain.complete }

theorem resultDomain_result : results (D := zD) 128 (zD.erg zLies) = .ok resultDomain := rfl

abbrev postCheck (value : ErgVal zD (zD.erg zLies)) :=
  checkPostFormula zPB zLies arguments value

theorem requirement_present : (translate (zPB.requires zLies) arguments).toOption.isSome = true := rfl

def requirement := (translate (zPB.requires zLies) arguments).toOption.get requirement_present

theorem requirement_result : translate (zPB.requires zLies) arguments = .ok requirement := rfl

theorem requirement_payload : requirement.payload = .tru := rfl

/-- Only bodies vary; the reader's declaration and all contract metadata stay fixed. -/
abbrev Bodies := (f : zD.Fn) → Endblock zD (vertragVon zD f) false
  (zD.params f) (Signatur.anfang zD (zD.signatur f))

def withBodies (bodies : Bodies) : Programm zD := { zPB with rumpf := bodies }

def invariantsFor (bodies : Bodies) :
    InvariantFormula (withBodies bodies) (zD.invs.filter (schuldet zLies)) :=
  (invariantFormula (withBodies bodies) []).toOption.get (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The strict reader VC is independent of unrelated function bodies. -/
theorem environment_checked_for (bodies : Bodies) (same : bodies zLies = body)
    (sources : LockSources zS) :
    (Vertraege.Pruefer.checkEnvironment (withBodies bodies) zS (requiresPolicy (withBodies bodies))
      sources {} none zLies (invariantsFor bodies) arguments).toOption.isSome = true := by
  have ready : ∃ pre : Vertraege.Pruefer.EndCondition (S := zS)
      (requiresPolicy (withBodies bodies)) (bodies zLies) arguments goals,
      ending (requiresPolicy (withBodies bodies)) (lockFormula zS sources) {} none 128
        (bodies zLies) arguments goals = .ok pre ∧ ∀ values, pre.formula.denote values := by
    rw [same]
    exact compiled_valid (withBodies bodies) sources
  obtain ⟨pre, hpre, valid⟩ := ready
  have hbody : ending (S := zS) (requiresPolicy (withBodies bodies)) (lockFormula zS sources)
      {} none 128 ((withBodies bodies).rumpf zLies) arguments
      (contractGoals (withBodies bodies) zLies arguments (invariantsFor bodies)) = .ok pre := hpre
  obtain ⟨posts, hposts⟩ := collect_success resultDomain.values
    (fun value => ∃ result, postFormula zPB zLies arguments value = .ok result) postCheck (by
      intro value
      refine ⟨⟨⟨post value, post_result value⟩⟩, ?_⟩
      simp only [postCheck, checkPostFormula, post_result])
  have decided : decideB (close (writerMatrix .tru .tru pre.formula))
      (close_closed (writerMatrix .tru .tru pre.formula)) = true := by
    apply (close_decide_true_iff _).mpr
    intro values
    apply (lower_denote _ _).mpr
    intro _
    apply (quoteQF_denote _ _).mpr
    apply (lower_denote _ _).mpr
    intro _
    exact (quoteQF_denote _ _).mpr (valid values)
  exact environment_success (withBodies bodies) zS (requiresPolicy (withBodies bodies)) sources {}
    none zLies (invariantsFor bodies) arguments requirement requirement_result resultDomain
    resultDomain_result posts hposts pre hbody decided

/-- The strict arithmetic gate accepts the original body and its original post. -/
theorem environment_checked (sources : LockSources zS) :
    (Vertraege.Pruefer.checkEnvironment zPB zS (requiresPolicy zPB) sources {} none
      zLies invariants arguments).toOption.isSome = true :=
  environment_checked_for zPB.rumpf body_eq sources

def inputDomain : Invarianten.Pruefer.Environments zD context :=
  (Invarianten.Pruefer.environments (D := zD) 128 context).toOption.get (by rfl)

theorem inputDomain_result : Invarianten.Pruefer.environments (D := zD) 128 context = .ok inputDomain := rfl

/-- The reader certificate composes with arbitrary other bodies and actual replay. -/
theorem reader_checked_for (bodies : Bodies) (same : bodies zLies = body)
    (sources : LockSources zS)
    (replay : (Invarianten.Pruefer.atomicReplay? (withBodies bodies) zLies).isSome = true) :
    (checkFunction (withBodies bodies) zS sources {} none zLies).toOption.isSome = true := by
  apply function_success (withBodies bodies) zS sources {} none zLies
  · rfl
  · exact replay
  · apply execution_success (withBodies bodies) zS (requiresPolicy (withBodies bodies)) sources {}
      none zLies (invariantsFor bodies) (by rfl) inputDomain inputDomain_result
    · change argumentSpecializations 16384 context * endSpecializations 16384 (bodies zLies) ≤ 16384
      rw [same]
      decide +kernel
    · intro locals
      have equal : locals = arguments := by cases locals; rfl
      subst locals
      exact environment_checked_for bodies same sources

/-- The original reader function, including its 101-value binder, is accepted. -/
theorem reader_checked (sources : LockSources zS) :
    (checkFunction zPB zS sources {} none zLies).toOption.isSome = true :=
  reader_checked_for zPB.rumpf body_eq sources (by decide +kernel)

#print axioms reader_checked

/-- Full function enumeration retains the strict gate; only the reader's
    kernel proof uses the symbolic certificate above. -/
theorem contracts_checked : KontrakteGeprueftB zPB zS zFs zPoolSources = true := by
  apply contracts_success zPB zS zPoolSources {} zFs
  intro f
  cases f with
  | ein => decide +kernel
  | lies => exact reader_checked zPoolSources
  | wrap => decide +kernel
  | haupt => decide +kernel

#print axioms contracts_checked

/-- Both existing VC gates accept; no invariant or contract duty is skipped. -/
theorem vc_checked : Invarianten.Pruefer.invariantVCB zPB zS zFs zPoolSources {}
    (fun _ => none) [()] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, contracts_checked⟩

#print axioms vc_checked

/-- The guarded read/write fixture remains a non-degenerate positive witness. -/
theorem c_contracts_checked : KontrakteGeprueftB zPCFragment zS zFs zPoolSources = true := by
  decide +kernel

theorem c_vc_checked : Invarianten.Pruefer.invariantVCB zPCFragment zS zFs zPoolSources {}
    (fun _ => none) [()] = true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, c_contracts_checked⟩

theorem c_accepted : Akzeptiert zPCFragment zS zFs [()] [.inl ()] [zHaupt]
    (sources := zPoolSources) = true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide +kernel, c_vc_checked⟩

/-- Joint non-degeneracy witness for symbolic branch composition and strict admission. -/
theorem reader_pipeline_zeuge :
    domain.values.length = 101 ∧ zPB.rumpf zLies = body ∧
    (∃ result, compiled zPB zPoolSources = .ok result ∧
      ∀ values, result.formula.denote values) ∧
    (checkFunction zPB zS zPoolSources {} none zLies).toOption.isSome = true :=
  ⟨by decide +kernel, body_eq, compiled_valid zPB zPoolSources, reader_checked zPoolSources⟩

end PoolCertificate



end Gabbro.Grammatik.Zielsatz
