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
  (List.range remaining).filterMap fun offset =>
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

def localDomain (budget : Nat) (τ : Ty) : Except Refusal (LocalDomain D τ) :=
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
          { values := [false, true]
            complete := fun value => by cases value <;> simp }
      else .error (.unsupported "Boolean local observation exceeds the VC budget")
  | _ => .error (.unsupported "local observation needs a bounded integer or Boolean type")

/-- Piecewise scalar initialization, including the model's narrowing fallback.
    The equality is exact in both arms, so local snapshots retain correlations. -/
def integerEquality (expression : Expr D Γ Λ (.int lo hi)) (locals : Env D Γ) (number : Int) :
    Except Refusal { formula : LProp (Observation D) // ∀ world,
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
        · simp only [fits, true_implies, not_true_eq_false, false_implies, and_true, eval, dif_pos fits]
        · simp only [fits, false_implies, not_false_eq_true, true_implies, true_and, eval, dif_neg fits]⟩
  | .wenn test positive negative => do
      let guard ← translate test locals
      let yes ← integerEquality positive locals number
      let no ← integerEquality negative locals number
      return ⟨.and (.imp guard.payload yes.val) (.imp (.not guard.payload) no.val), fun world => by
        change (guard.payload.denote _ → yes.val.denote _) ∧
          (¬ guard.payload.denote _ → no.val.denote _) ↔ _
        rw [← guard.correct world, yes.property world, no.property world]
        cases tested : eval world test world locals <;> simp [eval, tested, wahr?]⟩
  | expression => do
      let encoded ← translate expression locals
      return ⟨.eq encoded.payload (.konst number), fun world => by
        change encoded.payload.denote _ = number ↔ _
        rw [encoded.correct world]⟩

/-- The equality relating a fresh local observation to its initializer. This
    preserves correlation with memory even if that memory is overwritten later. -/
def localEquality (expression : Expr D Γ Λ τ) (locals : Env D Γ) (value : Wert D τ) :
    Except Refusal { formula : LProp (Observation D) // ∀ world,
      formula.denote (assignment world) ↔ eval world expression world locals = value } :=
  match τ with
  | .int lo hi => do
      let encoded ← integerEquality expression locals value.n
      return ⟨encoded.val, fun world => by
        rw [encoded.property world]
        exact ⟨fun h => zahl_ext h, fun h => congrArg Zahl.n h⟩⟩
  | .bool => do
      let encoded ← translate expression locals
      return ⟨if value then encoded.payload else .not encoded.payload, fun world => by
        cases value with
        | true => exact (encoded.correct world).symm
        | false =>
            change ¬ encoded.payload.denote (assignment world) ↔ _ = false
            rw [← encoded.correct world]
            cases eval world expression world locals <;> simp⟩
  | _ => .error (.unsupported "local initializer is outside the scalar fragment")

/-- Conjoin certified branches. The chosen domain is complete; empty types are
    handled constructively, without assuming the existence of a decoded value. -/
def localBranches {program : Programm D} {checked : D.Fn → List D.Inv}
    (values : List (Wert D τ)) (expression : Expr D Γ Λ τ) (locals : Env D Γ)
    (target : Wert D τ → Runtime program checked S → World D → Prop)
    (compile : ∀ value, Except Refusal (Condition (target value))) :
    Except Refusal (Condition (fun runtime world => ∀ value ∈ values,
      eval world expression world locals = value → target value runtime world)) :=
  match values with
  | [] => .ok
      { formula := .tru
        sound := fun _ _ _ value member => by simp at member }
  | value :: values => do
      let relation ← localEquality expression locals value
      let head ← compile value
      let tail ← localBranches values expression locals target compile
      return { formula := conj (freshImplication τ value relation.val head.formula) tail.formula
          sound := fun runtime world valid current member equals => by
            have parts := (conj_denote _ _ _).mp valid
            rcases List.mem_cons.mp member with same | member
            · subst current
              exact head.sound runtime world (freshImplication_sound τ value relation.val head.formula
                (assignment world) parts.1 ((relation.property world).mpr equals))
            · exact tail.sound runtime world parts.2 current member equals }

def localSelect {program : Programm D} {checked : D.Fn → List D.Inv}
    (budget : Nat) (expression : Expr D Γ Λ τ) (locals : Env D Γ)
    (target : Wert D τ → Runtime program checked S → World D → Prop)
    (compile : ∀ value, Except Refusal (Condition (target value))) :
    Except Refusal (Condition (fun runtime world =>
      target (eval world expression world locals) runtime world)) := do
  let domain ← localDomain (D := D) budget τ
  let branches ← localBranches domain.values expression locals target compile
  return branches.map (fun runtime world valid =>
    valid _ (domain.complete _) rfl)

/-- Call results are unconstrained decoded values. No result/argument relation
    from the callee contract is smuggled into this conjunction. -/
def allConditions {program : Programm D} {checked : D.Fn → List D.Inv}
    (values : List α) (target : α → Runtime program checked S → World D → Prop)
    (compile : ∀ value, Except Refusal (Condition (target value))) :
    Except Refusal (Condition (fun runtime world => ∀ value ∈ values, target value runtime world)) :=
  match values with
  | [] => .ok
      { formula := .tru
        sound := fun _ _ _ value member => by simp at member }
  | value :: values => do
      let head ← compile value
      let tail ← allConditions values target compile
      return { formula := conj head.formula tail.formula
          sound := fun runtime world valid current member => by
            have parts := (conj_denote _ _ _).mp valid
            rcases List.mem_cons.mp member with same | member
            · subst current
              exact head.sound runtime world parts.1
            · exact tail.sound runtime world parts.2 current member }

end Gabbro.Grammatik.Invarianten.VC
