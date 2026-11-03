module

public import Grammatik.Logik.Fortschritt.KostenG.T1.Teil2
public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.ScopeMarkers

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Every pending lexical marker contributes a unit to the unchanged
    residue potential, in addition to its terminal unit. -/
theorem GRest.freis_budget (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ) :
    r.freis.length + 1 ≤ potRest c pa r := by
  induction r <;> simp only [GRest.freis, potRest, List.length_cons] at *
  all_goals first
    | exact kostenEnd_pos c pa _
    | omega

/-- Evaluation costs one step. A nonempty cleanup costs exactly one more
    step per scope, because the final release also delivers the answer.
    Thus there is neither an empty cleanup step nor a delivery surcharge. -/
def scopedReturnSteps (scopes : List D.Lock) : Nat :=
  match scopes with
  | [] => 1
  | _ :: _ => 1 + scopes.length

/-- The cleanup budget is already present in the lexical scope markers;
    this argument does not change any source cost or the numerical goal.
    Its use in the cost engine requires the reachable balance invariant. -/
theorem GRest.scopedReturn_budget (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ)
    (R : RueckRessourcen D V Λ) (h : r.scopeBalance) :
    scopedReturnSteps R.scopes ≤ potRest c pa r := by
  have heq := r.scopes_length R h
  have hbudget := r.freis_budget c pa
  cases hs : R.scopes with
  | nil => simp only [scopedReturnSteps]; omega
  | cons L Ls =>
      simp only [scopedReturnSteps, List.length_cons]
      simp only [hs, List.length_cons] at heq
      omega

end Gabbro.Grammatik
