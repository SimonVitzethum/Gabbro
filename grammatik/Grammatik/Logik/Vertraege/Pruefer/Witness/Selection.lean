module

public import Grammatik.Logik.Vertraege.Pruefer.Program

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.SelectionWitness

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC

variable {D : Deklaration}

/-- Prove the actual generated branch VC symbolically, without replaying
    integer elimination in the kernel. This lemma changes no decision gate. -/
theorem freshImplication_valid (type : Ty) (value : Wert D type)
    (guard : LProp (Observation D)) (post : QF (Observation D))
    (values : Assignment (Observation D))
    (valid : guard.denote values → post.denote values) :
    (freshImplication type value guard post).denote values := by
  apply (dropLocalQF_denote _ values).mpr
  apply (lower_denote _ _).mpr
  intro code _ selected
  have projection :
      (fun key => (Assignment.bind (dropBase values) none code) (some key)) = values := by
    funext key
    simp only [Assignment.bind, reduceCtorEq, ↓reduceIte, dropBase]
  have present := (lower_denote _ _).mp
    ((liftLocalQF_denote _ _).mp ((quoteQF_denote _ _).mp selected))
  rw [projection] at present
  apply (quoteQF_denote _ _).mpr
  apply (liftLocalQF_denote _ _).mpr
  rw [projection]
  exact valid present

variable {program : Programm D} {checked : D.Fn → List D.Inv} {S : SperrInv D}
  {Γ : Ctx} {Λ : List (Res D)} {type : Ty}

/-- Balanced proof composition over the actual branch generator. Its inputs
    certify successful translation and validity of each generated implication. -/
theorem localBranches_valid (items : List (Wert D type))
    (expression : Expr D Γ Λ type) (locals : Env D Γ)
    (target : Wert D type → Runtime program checked S → World D → Prop)
    (compile : ∀ value, Except Frag.Refusal (Condition (target value)))
    (premise : Assignment (Observation D) → Prop)
    (valid : ∀ value, ∃ relation head,
      localEquality expression locals value = .ok relation ∧ compile value = .ok head ∧
      ∀ values, premise values → relation.val.denote values → head.formula.denote values) :
    ∃ result, localBranches items expression locals target compile = .ok result ∧
      ∀ values, premise values → result.formula.denote values := by
  induction items with
  | nil => exact ⟨_, rfl, fun _ _ => trivial⟩
  | cons value items ih =>
      obtain ⟨relation, head, hrelation, hhead, hvalid⟩ := valid value
      obtain ⟨tail, htail, hvalidTail⟩ := ih
      cases result : localBranches (value :: items) expression locals target compile with
      | error cause =>
          simp only [localBranches, hrelation, hhead, htail, bind, Except.bind, pure, Except.pure, reduceCtorEq] at result
      | ok out =>
          refine ⟨out, rfl, ?_⟩
          have shape : out.formula = conj (freshImplication type value relation.val head.formula) tail.formula := by
            simp only [localBranches, hrelation, hhead, htail, bind, Except.bind, pure, Except.pure] at result
            exact (congrArg Condition.formula (Except.ok.inj result)).symm
          intro values ready
          rw [shape, conj_denote]
          exact ⟨freshImplication_valid type value relation.val head.formula values
            (hvalid values ready), hvalidTail values ready⟩

/-- Lift the branch certificate through the actual complete typed domain. -/
theorem localSelect_valid (budget : Nat)
    (expression : Expr D Γ Λ type) (locals : Env D Γ)
    (target : Wert D type → Runtime program checked S → World D → Prop)
    (compile : ∀ value, Except Frag.Refusal (Condition (target value)))
    (domain : LocalDomain D type) (hdomain : localDomain budget type = .ok domain)
    (premise : Assignment (Observation D) → Prop)
    (valid : ∀ value, ∃ relation head,
      localEquality expression locals value = .ok relation ∧ compile value = .ok head ∧
      ∀ values, premise values → relation.val.denote values → head.formula.denote values) :
    ∃ result, localSelect budget expression locals target compile = .ok result ∧
      ∀ values, premise values → result.formula.denote values := by
  obtain ⟨pre, hpre, hvalid⟩ := localBranches_valid domain.values expression locals target compile premise valid
  cases result : localSelect budget expression locals target compile with
  | error cause =>
      simp only [localSelect, hdomain, hpre, bind, Except.bind, pure, Except.pure, reduceCtorEq] at result
  | ok out =>
      refine ⟨out, rfl, ?_⟩
      have shape : out.formula = pre.formula := by
        simp only [localSelect, hdomain, hpre, bind, Except.bind, pure, Except.pure] at result
        exact (congrArg Condition.formula (Except.ok.inj result)).symm
      rw [shape]
      exact hvalid

/-- Compose successful proof-producing checks without normalizing their proofs. -/
theorem collect_success {α : Type} (items : List α) (property : α → Prop)
    (check : ∀ item, Except Frag.Refusal (PLift (property item)))
    (success : ∀ item, ∃ result, check item = .ok result) :
    ∃ result, Invarianten.Pruefer.collect items property check = .ok result := by
  induction items with
  | nil => exact ⟨_, rfl⟩
  | cons item items ih =>
      obtain ⟨head, hhead⟩ := success item
      obtain ⟨tail, htail⟩ := ih
      cases result : Invarianten.Pruefer.collect (item :: items) property check with
      | error cause =>
          simp only [Invarianten.Pruefer.collect, hhead, htail, bind, Except.bind,
            pure, Except.pure, reduceCtorEq] at result
      | ok out => exact ⟨out, rfl⟩

/-- Replay successful syntax/compilation results and a proved actual VC decision.
    The checker still computes all of these results; this is an off-path proof
    rule for its Bool, with no semantic proof supplied to the executable gate. -/
theorem environment_success (program : Programm D) (S : SperrInv D) (policy : CallPolicy program)
    (sources : Invarianten.Pruefer.LockSources S) (budget : VCBudget)
    (hint : Option (QF (Observation D))) (f : D.Fn)
    (invariants : InvariantFormula program (D.invs.filter (schuldet f)))
    (locals : Env D (D.params f))
    (entry : Encoded D .bool (fun world => eval world (program.requires f) world locals))
    (hentry : translate (program.requires f) locals = .ok entry)
    (domain : Results D (D.erg f)) (hdomain : results (D := D) budget.expansion (D.erg f) = .ok domain)
    (posts : PLift (∀ value ∈ domain.values, ∃ post, postFormula program f locals value = .ok post))
    (hposts : Invarianten.Pruefer.collect domain.values
      (fun value => ∃ post, postFormula program f locals value = .ok post)
      (checkPostFormula program f locals) = .ok posts)
    (compiled : Vertraege.Pruefer.EndCondition (S := S) policy (program.rumpf f) locals
      (contractGoals program f locals invariants))
    (hcompiled : ending policy (Invarianten.Pruefer.lockFormula S sources) budget hint budget.depth
      (program.rumpf f) locals (contractGoals program f locals invariants) = .ok compiled)
    (decided : decideB (close (writerMatrix entry.payload .tru compiled.formula))
      (close_closed (writerMatrix entry.payload .tru compiled.formula)) = true) :
    (Vertraege.Pruefer.checkEnvironment program S policy sources budget hint f invariants locals).toOption.isSome = true := by
  unfold Vertraege.Pruefer.checkEnvironment
  rw [hentry, hdomain]
  dsimp only [bind, Except.bind]
  rw [hposts]
  dsimp only [bind, Except.bind]
  rw [hcompiled]
  dsimp only [bind, Except.bind]
  split
  · rfl
  · rename_i refused
    exact False.elim (refused decided)

theorem success_of_isSome {α ε : Type} (result : Except ε α)
    (ready : result.toOption.isSome = true) : ∃ value, result = .ok value := by
  cases result with
  | error cause => cases ready
  | ok value => exact ⟨value, rfl⟩

/-- The complete parameter traversal uses the same checked environment results. -/
theorem execution_success (program : Programm D) (S : SperrInv D) (policy : CallPolicy program)
    (sources : Invarianten.Pruefer.LockSources S) (budget : VCBudget)
    (hint : Option (QF (Observation D))) (f : D.Fn)
    (invariants : InvariantFormula program (D.invs.filter (schuldet f)))
    (hinvariants : invariantFormula program (D.invs.filter (schuldet f)) = .ok invariants)
    (domain : Invarianten.Pruefer.Environments D (D.params f))
    (hdomain : Invarianten.Pruefer.environments (D := D) budget.expansion (D.params f) = .ok domain)
    (ready : ∀ locals, (Vertraege.Pruefer.checkEnvironment program S policy sources budget hint f invariants locals).toOption.isSome = true) :
    (checkExecution program S policy sources budget hint f).toOption.isSome = true := by
  obtain ⟨checked, hchecked⟩ := collect_success domain.values
    (fun locals => CheckedEnvironment (S := S) policy f locals)
    (Vertraege.Pruefer.checkEnvironment program S policy sources budget hint f invariants)
    (fun locals => success_of_isSome _ (ready locals))
  unfold checkExecution
  rw [hinvariants, hdomain]
  dsimp only [bind, Except.bind]
  delta CheckedEnvironment at hchecked
  rw [hchecked]
  rfl

/-- The actual function gate preserves its syntax certificate, atomic replay
    and checked strict execution; this is a proof rule, not a new gate path. -/
theorem function_success (program : Programm D) (S : SperrInv D)
    (sources : Invarianten.Pruefer.LockSources S) (budget : VCBudget)
    (hint : Option (QF (Observation D))) (f : D.Fn)
    (basic : checkBasicFunction program S sources budget f = none)
    (replay : (Invarianten.Pruefer.atomicReplay? program f).isSome = true)
    (execution : (checkExecution program S (requiresPolicy program) sources budget hint f).toOption.isSome = true) :
    (checkFunction program S sources budget hint f).toOption.isSome = true := by
  obtain ⟨checked, hchecked⟩ := success_of_isSome _ execution
  cases h : Invarianten.Pruefer.atomicReplay? program f with
  | none => simp only [h, Option.isSome_none, Bool.false_eq_true] at replay
  | some certificate =>
      unfold checkFunction
      rw [basic, h, hchecked]
      rfl

/-- Compose successful function checks through the actual default-hint gate. -/
theorem contracts_success (program : Programm D) (S : SperrInv D)
    (sources : Invarianten.Pruefer.LockSources S) (budget : VCBudget) (functions : List D.Fn)
    (ready : ∀ f, (checkFunction program S sources budget none f).toOption.isSome = true) :
    KontrakteGeprueftB program S functions sources budget = true := by
  obtain ⟨checked, hchecked⟩ := collect_success functions (ContractDuties program S)
    (fun f => do
      let hint ← loopHint (fun _ => none) f
      checkFunction program S sources budget hint f) (by
        intro f
        dsimp only [loopHint, bind, Except.bind]
        exact success_of_isSome _ (ready f))
  unfold KontrakteGeprueftB checkContracts
  rw [hchecked]
  rfl

end Gabbro.Grammatik.Vertraege.Pruefer.SelectionWitness
