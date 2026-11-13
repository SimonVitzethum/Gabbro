module
public import Grammatik.Parser.Lex.Tafel
@[expose] public section

namespace Gabbro.Grammatik.Parser.CallHoist

/-- Stateful emission in source order. The specification retains the append fold;
    compiled code accumulates reversed chunks and reverses the completed output once. -/
def collectSteps {σ α β : Type} (step : σ → α → List β × σ)
    (items : List α) (state : σ) : List β × σ :=
  items.foldl (fun acc item =>
    let next := step acc.2 item
    (acc.1 ++ next.1, next.2)) ([], state)

def collectStepsFast {σ α β : Type} (step : σ → α → List β × σ)
    (items : List α) (state : σ) : List β × σ :=
  let result := items.foldl (fun acc item =>
    let next := step acc.2 item
    (next.1.reverse ++ acc.1, next.2)) ([], state)
  (result.1.reverse, result.2)

/-- Every emitted element and every intermediate state is unchanged. -/
@[csimp] theorem collectSteps_eq_fast : @collectSteps = @collectStepsFast := by
  funext σ α β step items state
  unfold collectSteps collectStepsFast
  have key : ∀ (items : List α) (acc accF : List β × σ),
      acc = (accF.1.reverse, accF.2) →
      items.foldl (fun acc item =>
        let next := step acc.2 item
        (acc.1 ++ next.1, next.2)) acc =
      ((items.foldl (fun acc item =>
        let next := step acc.2 item
        (next.1.reverse ++ acc.1, next.2)) accF).1.reverse,
       (items.foldl (fun acc item =>
        let next := step acc.2 item
        (next.1.reverse ++ acc.1, next.2)) accF).2) := by
    intro items
    induction items with
    | nil => intro acc accF h; exact h
    | cons item rest ih =>
      intro acc accF h
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      subst h
      simp only [List.reverse_append, List.reverse_reverse]
  exact key items ([], state) ([], state) rfl

/-- Nonempty chunks and an empty emission keep their source order and state transitions. -/
theorem collectSteps_zeuge :
    collectSteps (fun (state : Nat) item =>
      (if item == 0 then [] else [item, state], state + 1)) [0, 3, 4] 10 =
        ([3, 11, 4, 12], 13) ∧
    collectStepsFast (fun (state : Nat) item =>
      (if item == 0 then [] else [item, state], state + 1)) [0, 3, 4] 10 =
        ([3, 11, 4, 12], 13) := by
  decide +kernel

end Gabbro.Grammatik.Parser.CallHoist
