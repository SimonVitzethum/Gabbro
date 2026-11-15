module

public import Grammatik.Logik.Invarianten.VC.Fresh
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration} {S : SperrInv D}

/-- Finite elimination of a fresh local observation. The range is the actual
    decoded type, including both endpoints, never an author-supplied sample. -/
structure LocalDomain (D : Deklaration) (τ : Ty) where
  values : List (Wert D τ)
  complete : ∀ value : Wert D τ, value ∈ values

def integerValues (lo hi : Int) (remaining : Nat) : List (Zahl lo hi) :=
  (List.range remaining).filterMap fun (offset : Nat) =>
    if h : lo ≤ lo + (offset : Int) ∧ lo + (offset : Int) ≤ hi then
      some ⟨lo + (offset : Int), h.1, h.2⟩
    else none

theorem integerValues_complete (lo hi : Int) (value : Zahl lo hi) :
    value ∈ integerValues lo hi (hi - lo + 1).toNat := by
  have lower := value.lo_le
  have upper := value.le_hi
  have nonnegative : 0 ≤ value.n - lo := by omega
  have offset : ((value.n - lo).toNat : Int) = value.n - lo := Int.toNat_of_nonneg nonnegative
  have inside : (value.n - lo).toNat < (hi - lo + 1).toNat := by omega
  apply List.mem_filterMap.mpr
  refine ⟨(value.n - lo).toNat, List.mem_range.mpr inside, ?_⟩
  have same : lo + ((value.n - lo).toNat : Int) = value.n := by omega
  simpa only [same, lower, upper, and_self, ↓reduceDIte]

def localDomain (budget : Nat) (τ : Ty) : Except Frag.Refusal (LocalDomain D τ) :=
  match τ with
  | .int lo hi =>
      if (hi - lo + 1).toNat ≤ budget then
        .ok
          { values := integerValues lo hi (hi - lo + 1).toNat
            complete := integerValues_complete lo hi }
      else .error (.unsupported "local observation type range exceeds the VC budget")
  | .bool =>
      if 2 ≤ budget then
        .ok
          { values := (([false, true] : List Bool) : List (Wert D .bool))
            complete := by
              show ∀ value : Bool, value ∈ ([false, true] : List Bool)
              decide }
      else .error (.unsupported "Boolean local observation exceeds the VC budget")
  | .ptr capability =>
      -- G carries pointer authority in the type; its decoded value is Unit.
      if 1 ≤ budget then
        .ok
          { values := [show Wert D (.ptr capability) from ()]
            complete := fun value => by cases value; exact List.mem_cons_self }
      else .error (.unsupported "pointer capability exceeds the VC budget")
  | _ => .error (.unsupported "local observation needs a bounded integer, Boolean or pointer capability type")

/-- Piecewise scalar initialization, including the model's narrowing fallback.
    The equality is exact in both arms, so local snapshots retain correlations. -/
def integerEquality (expression : Expr D Γ Λ (.int lo hi)) (locals : Env D Γ) (number : Int) :
    Except Frag.Refusal { formula : LProp (Observation D) // ∀ world,
      formula.denote (assignment world) ↔ (eval world expression world locals).n = number } :=
  match expression with
  | .eng value low high fallback => do
      let encoded ← translateScalar value locals
      let yes ← integerEquality value locals number
      let no ← integerEquality fallback locals number
      let guard : LProp (Observation D) :=
        .and (.le (.konst low) encoded.term) (.le encoded.term (.konst high))
      return ⟨.and (.imp guard yes.val) (.imp (.not guard) no.val), fun world => by
        have guardCorrect : guard.denote (assignment world) ↔
            low ≤ (eval world value world locals).n ∧ (eval world value world locals).n ≤ high := by
          change low ≤ encoded.term.denote _ ∧ encoded.term.denote _ ≤ high ↔ _
          rw [encoded.correct world]
          rfl
        change (guard.denote _ → yes.val.denote _) ∧
          (¬ guard.denote _ → no.val.denote _) ↔ _
        rw [guardCorrect, yes.property world, no.property world]
        by_cases fits : low ≤ (eval world value world locals).n ∧ (eval world value world locals).n ≤ high
        · have evaluated : eval world (.eng value low high fallback) world locals =
              (⟨(eval world value world locals).n, fits.1, fits.2⟩ : Zahl low high) :=
            dif_pos fits
          have equivalent := congrArg (fun v : Wert D (.int low high) => v.n = number) evaluated
          simp only [fits, true_implies, not_true_eq_false, false_implies, and_true]
          exact ⟨Eq.mpr equivalent, Eq.mp equivalent⟩
        · have evaluated : eval world (.eng value low high fallback) world locals =
              eval world fallback world locals := dif_neg fits
          have equivalent := congrArg (fun v : Wert D (.int low high) => v.n = number) evaluated
          simp only [fits, false_implies, not_false_eq_true, true_implies, true_and]
          exact ⟨Eq.mpr equivalent, Eq.mp equivalent⟩⟩
  | .wenn test positive negative => do
      let guard ← translate test locals
      let yes ← integerEquality positive locals number
      let no ← integerEquality negative locals number
      return ⟨.and (.imp guard.payload yes.val) (.imp (.not guard.payload) no.val), fun world => by
        change (guard.payload.denote _ → yes.val.denote _) ∧
          (¬ guard.payload.denote _ → no.val.denote _) ↔ _
        rw [← guard.bool_iff world, yes.property world, no.property world]
        cases tested : wahr? (eval world test world locals) with
        | true =>
            have evaluated : eval world (.wenn test positive negative) world locals =
                eval world positive world locals := if_pos tested
            have equivalent := congrArg (fun v : Wert D (.int lo hi) => v.n = number) evaluated
            simp only [tested, true_implies, not_true_eq_false, false_implies, and_true]
            exact ⟨Eq.mpr equivalent, Eq.mp equivalent⟩
        | false =>
            have declined : ¬ wahr? (eval world test world locals) = true :=
              fun taken => Bool.noConfusion (tested.symm.trans taken)
            have evaluated : eval world (.wenn test positive negative) world locals =
                eval world negative world locals := if_neg declined
            have equivalent := congrArg (fun v : Wert D (.int lo hi) => v.n = number) evaluated
            simp only [tested, Bool.false_eq_true, false_implies, not_false_eq_true,
              true_implies, true_and]
            exact ⟨Eq.mpr equivalent, Eq.mp equivalent⟩⟩
  | expression => do
      let encoded ← translate expression locals
      return ⟨.eq encoded.payload (.konst number), fun world => by
        change encoded.payload.denote _ = number ↔ _
        rw [encoded.correct world]⟩
termination_by sizeOf expression

/-- The equality relating a fresh local observation to its initializer. This
    preserves correlation with memory even if that memory is overwritten later. -/
def localEquality (expression : Expr D Γ Λ τ) (locals : Env D Γ) (value : Wert D τ) :
    Except Frag.Refusal { formula : LProp (Observation D) // ∀ world,
      formula.denote (assignment world) ↔ eval world expression world locals = value } :=
  match τ with
  | .int lo hi => do
      let encoded ← integerEquality expression locals value.n
      return ⟨encoded.val, fun world => by
        rw [encoded.property world]
        exact ⟨fun h => zahl_ext h, fun h => congrArg Zahl.n h⟩⟩
  | .bool => do
      let encoded ← translate expression locals
      return ⟨if wahr? value then encoded.payload else .not encoded.payload, fun world => by
        change (if wahr? value then encoded.payload else .not encoded.payload).denote _ ↔
          wahr? (eval world expression world locals) = wahr? value
        cases expected : wahr? value with
        | true =>
            simp only [expected, ↓reduceIte]
            exact (encoded.bool_iff world).symm
        | false =>
            simp only [expected, Bool.false_eq_true, ↓reduceIte, LProp.denote]
            constructor
            · intro absent
              cases actual : wahr? (eval world expression world locals) with
              | false => rfl
              | true => exact (absent ((encoded.bool_iff world).mp actual)).elim
            · intro absent present
              have actual := (encoded.bool_iff world).mpr present
              exact Bool.noConfusion (absent.symm.trans actual)⟩
  | .ptr _ => .ok ⟨.tru, fun world => by
      change True ↔ (eval world expression world locals : Unit) = (value : Unit)
      exact ⟨fun _ => Subsingleton.elim (α := Unit) _ _, fun _ => trivial⟩⟩
  | _ => .error (.unsupported "local initializer is outside the supported local fragment")

/-- Conjoin certified branches. The chosen domain is complete; empty types are
    handled constructively, without assuming the existence of a decoded value. -/
def localBranches {program : Programm D} {checked : D.Fn → List D.Inv}
    (values : List (Wert D τ)) (expression : Expr D Γ Λ τ) (locals : Env D Γ)
    (target : Wert D τ → Runtime program checked S → World D → Prop)
    (compile : ∀ value, Except Frag.Refusal (Condition (target value))) :
    Except Frag.Refusal (Condition (fun runtime world => ∀ value ∈ values,
      eval world expression world locals = value → target value runtime world)) :=
  match values with
  | [] => .ok
      { formula := .tru
        sound := fun _ _ _ value member => by simp at member }
  | value :: values => do
      let relation ← localEquality expression locals value
      let head ← compile value
      let tail ← localBranches values expression locals target compile
      return {
          formula := conj (freshImplication τ value relation.val head.formula) tail.formula
          sound := fun runtime world valid current member equals => by
            have parts := (conj_denote _ _ _).mp valid
            rcases List.mem_cons.mp member with same | member
            · have reached : eval world expression world locals = value := same ▸ equals
              have result := head.sound runtime world (freshImplication_sound τ value relation.val
                head.formula (assignment world) parts.1 ((relation.property world).mpr reached))
              exact same ▸ result
            · exact tail.sound runtime world parts.2 current member equals }

def localSelect {program : Programm D} {checked : D.Fn → List D.Inv}
    (budget : Nat) (expression : Expr D Γ Λ τ) (locals : Env D Γ)
    (target : Wert D τ → Runtime program checked S → World D → Prop)
    (compile : ∀ value, Except Frag.Refusal (Condition (target value))) :
    Except Frag.Refusal (Condition (fun runtime world =>
      target (eval world expression world locals) runtime world)) := do
  let domain ← localDomain (D := D) budget τ
  let branches ← localBranches domain.values expression locals target compile
  return branches.map (fun runtime world valid =>
    valid _ (domain.complete _) rfl)

/-- Call results are unconstrained decoded values. No result/argument relation
    from the callee contract is smuggled into this conjunction. -/
def allConditions {program : Programm D} {checked : D.Fn → List D.Inv}
    (values : List α) (target : α → Runtime program checked S → World D → Prop)
    (compile : ∀ value, Except Frag.Refusal (Condition (target value))) :
    Except Frag.Refusal (Condition (fun runtime world => ∀ value ∈ values, target value runtime world)) :=
  match values with
  | [] => .ok
      { formula := .tru
        sound := fun _ _ _ value member => by simp at member }
  | value :: values => do
      let head ← compile value
      let tail ← allConditions values target compile
      return {
          formula := conj head.formula tail.formula
          sound := fun runtime world valid current member => by
            have parts := (conj_denote _ _ _).mp valid
            rcases List.mem_cons.mp member with same | member
            · subst current
              exact head.sound runtime world parts.1
            · exact tail.sound runtime world parts.2 current member }

end Gabbro.Grammatik.Invarianten.VC
