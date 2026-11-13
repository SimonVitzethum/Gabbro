module
public import Grammatik.Parser.Elab.Modules.CallHoist.Collect
@[expose] public section

namespace Gabbro.Grammatik.Parser.CallHoist

/-- Fallible stateful emission, in source order. A refusal retains exactly the
    first error of the canonical left fold. -/
def collectStepsM {ε σ α β : Type} (step : σ → α → Except ε (List β × σ))
    (items : List α) (state : σ) : Except ε (List β × σ) :=
  items.foldlM (fun (acc : List β × σ) item => do
    let next ← step acc.2 item
    pure (acc.1 ++ next.1, next.2)) ([], state)

def collectStepsMFast {ε σ α β : Type} (step : σ → α → Except ε (List β × σ))
    (items : List α) (state : σ) : Except ε (List β × σ) :=
  (items.foldlM (fun (acc : List β × σ) item => do
    let next ← step acc.2 item
    pure (next.1.reverse ++ acc.1, next.2)) ([], state)).map fun (acc : List β × σ) =>
      (acc.1.reverse, acc.2)

/-- Lift a fallible single-item rewrite into the canonical prefix fold. The
    equality includes the first error, independently of the emitted prefix. -/
theorem collectStepsM_singleton {ε σ α β : Type}
    (step : σ → α → Except ε (β × σ)) (items : List α) (state : σ) :
    collectStepsM (fun state item => do
      let next ← step state item
      pure ([next.1], next.2)) items state =
    items.foldlM (fun (acc : List β × σ) item => do
      let next ← step acc.2 item
      pure (acc.1 ++ [next.1], next.2)) ([], state) := by
  have fold_eq : ∀ (items : List α) (acc : List β × σ),
      items.foldlM (fun (acc : List β × σ) item => do
        let next ← (do
          let result ← step acc.2 item
          pure ([result.1], result.2) : Except ε (List β × σ))
        pure (acc.1 ++ next.1, next.2)) acc =
      items.foldlM (fun (acc : List β × σ) item => do
        let next ← step acc.2 item
        pure (acc.1 ++ [next.1], next.2)) acc := by
    intro items
    induction items with
    | nil => intro acc; rfl
    | cons item rest ih =>
      intro acc
      cases hstep : step acc.2 item with
      | error reason =>
        simp only [List.foldlM_cons, hstep, bind, Except.bind, pure, Except.pure]
      | ok next =>
        simp only [List.foldlM_cons, hstep, bind, Except.bind, pure, Except.pure]
        exact ih (acc.1 ++ [next.1], next.2)
  exact fold_eq items ([], state)

@[csimp] theorem collectStepsM_eq_fast : @collectStepsM = @collectStepsMFast := by
  funext ε σ α β step items state
  unfold collectStepsM collectStepsMFast
  have key : ∀ (items : List α) (acc accF : List β × σ),
      acc = (accF.1.reverse, accF.2) →
      items.foldlM (fun (acc : List β × σ) item => do
        let next ← step acc.2 item
        pure (acc.1 ++ next.1, next.2)) acc =
      (items.foldlM (fun (acc : List β × σ) item => do
        let next ← step acc.2 item
        pure (next.1.reverse ++ acc.1, next.2)) accF).map
          (fun (result : List β × σ) => (result.1.reverse, result.2)) := by
    intro items
    induction items with
    | nil =>
      intro acc accF h
      exact congrArg Except.ok h
    | cons item rest ih =>
      intro acc accF h
      subst acc
      cases hn : step accF.2 item with
      | error reason =>
        simp only [List.foldlM_cons, hn, bind, Except.bind, Except.map] <;> rfl
      | ok next =>
        simp only [List.foldlM_cons, hn, bind, Except.bind, pure, Except.pure]
        exact ih (accF.1.reverse ++ next.1, next.2)
          (next.1.reverse ++ accF.1, next.2) (by
            simp only [List.reverse_append, List.reverse_reverse])
  exact key items ([], state) ([], state) rfl

end Gabbro.Grammatik.Parser.CallHoist
