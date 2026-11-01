module

public import Lean
public import Gabbro.Body.Teil7

@[expose] public section


/-- **`gabbro_auto2` -- the pipeline, and once more on what it left** (GabbroV lane,
    2026-09-29). A call chain of five (`beispiele/147` `fnv`) is deeper than one round of
    `gabbro_calls` instantiates; the second pass closes it (measured: `fnv` 51 s -> closed with
    the same tactic run twice). The second list is the first WITHOUT the names `simp_all` clears
    (`hall`, `hpass`) -- an unknown identifier fails a whole pass. A pass over no goals costs
    nothing, so a unit the first pass closes pays nothing. -/
macro "gabbro_auto2" "[" ts:simpLemma,* "]" "[" us:simpLemma,* "]" "using" t:ident : tactic =>
  `(tactic| (gabbro_pipeline [$ts,*] using $t;
             all_goals (try (gabbro_pipeline [$us,*] using $t));
             all_goals sorry))

open Lean.Parser.Tactic in
/-- `gabbro_auto?` -- the same, and it PRINTS what is left before the `sorry`. For a
    person who wants to see their own logic before writing it. -/
macro "gabbro_auto?" "[" ts:simpLemma,* "]" "using" t:ident : tactic =>
  `(tactic| (gabbro_pipeline [$ts,*] using $t; trace_state; all_goals sorry))

namespace Gabbro.Body

/-! ## 8. Recursion INSIDE a loop -- the induction and the loop rule in one step
     (agent a, 2026-09-08)

    `contract_of_duty_rec` runs the induction over the `decreases` around the routine's
    BODY; `looprule_of_body_in` turns one pass of a loop into that loop's rule. A routine
    that calls itself from inside its own loop needs both at once, and the order matters:
    the loop rule has to be built INSIDE the induction, because the pass needs the bounded
    self-contract, and only the induction hands one down.

    **What the pass may assume, and what it owes for it.** It may assume `ContractBelow ρ f
    e s0 …` -- the routine's own contract on every state strictly below the ROUTINE'S ENTRY
    state `s0` in the measure. That is the only bound the induction has. But a loop rule is
    stated over an arbitrary pass state, and nothing ties that state to `s0` -- so the pass
    also owes that the measure has not moved: `eval t' e = eval s0 e`. It is carried across
    the passes as part of the loop's state predicate, exactly where `looprule_of_body_in`
    carries the well-typed world.

    **Why the second half is not decoration.** Without it a pass could lower the measure and
    then call the routine "below" a bound that no longer holds -- the assumption would be
    about a state the loop has left. With it, the bound the induction proved is the bound
    every pass still stands on.

    **And EVERY loop of the routine carries it, not only the one that holds the call**
    (agent b, 2026-09-08). Measured on `messung/proben/probe-rekursion-zwei-schleifen.gab`:
    with the measure carried by the recursive loop alone, one goal stood in the routine's
    duty -- `x = w_n`, the value of `n` after the FIRST loop against its value at entry. A
    `LoopRule` says nothing about the locals, so as far as the model knew a loop in front of
    the recursive one could have moved the measure. It cannot, and each loop proves that of
    its own body; the emitter states it for all of them and instantiates the innocent ones at
    the routine's entry state.

    **A `retry`/`forever` loop needs the same composition without the range**
    (`contract_of_duty_rec_loop`, below). The refusal it replaces named the missing index
    range as the ground, and the ground was wrong: the induction is over the `decreases`,
    never over the index.

    **What is still refused: a STACK of loops.** Every loop on the way from the routine's
    body to the recursive call would have to carry the measure, and their rules would have to
    be composed inside one another inside the induction -- the inner loop's rule is a
    hypothesis of the outer loop's pass. The composition here composes ONE rule.
-/

/-- **A contract holds below every state.** The one direction that is free: what holds for
    every state holds for the states below one. Used after the induction, to hand the loop
    its own rule under the plain well-typed world. -/
theorem contractBelow_of_contract (ρ : Env) (f : String) (e : Expr) (s : State)
    (pre : State → Prop) (post : State → State → Option Value → Prop)
    (h : Contract ρ f pre post) : ContractBelow ρ f e s pre post :=
  fun t' ht' _ => h t' ht'

/-- **The contract of a routine whose recursive call stands inside ONE ranged loop.**
    `hb` is the loop's pass, `hd` the routine's body; the induction over `e` and the
    induction over the passes are composed here once, so that no person writes either. -/
theorem contract_of_duty_rec_loop_in
    (ρ : Env) (f : String) (body : List Stmt) (pre : State → Prop)
    (post : State → State → Option Value → Prop) (e : Expr) (wf : State → Prop)
    (id : String) (lbody : List Stmt) (v : String) (lo hi : Int) (inv : Expr)
    (hr : Runs ρ f body)
    (hl : RunsLoopIn ρ id lbody v lo hi)
    (hb : ∀ (s0 : State), pre s0 → ContractBelow ρ f e s0 pre post →
      ∀ (t : State) (k : Int), lo ≤ k → k < hi → wf t → eval t e = eval s0 e →
        eval t inv = some (.bool true) →
        ∃ t', finalState (exec ρ lbody { t with local' := bindLocal t.local' v (.int k) })
                = some t'
              ∧ (wf t' ∧ eval t' e = eval s0 e) ∧ eval t' inv = some (.bool true))
    (hd : ∀ t, pre t → ContractBelow ρ f e t pre post →
        LoopRule ρ id (fun u => wf u ∧ eval u e = eval t e) inv →
      ∃ s', finalState (exec ρ body t) = some s' ∧ post t s' (finalValue (exec ρ body t))) :
    Contract ρ f pre post :=
  contract_of_duty_rec ρ f body pre post e hr (fun t ht hcb =>
    hd t ht hcb
      (looprule_of_body_in ρ id (fun u => wf u ∧ eval u e = eval t e) inv lbody v lo hi hl
        (fun u k hlo hhi hu hiv => hb t ht hcb u k hlo hhi hu.1 hu.2 hiv)))

/-- **The same, for a loop with NO index range** -- a `retry`/`forever` pass (agent b,
    2026-09-08).

    The refusal this replaces read *"no index range to induct over"*, and the ground was
    wrong: **the induction is over the `decreases`, never over the index.** What the range
    buys is `lo ≤ k < hi` in the pass -- an assumption about the pass, not a premise of the
    composition -- and `looprule_of_body` builds a `LoopRule` without it. So the only
    difference to `contract_of_duty_rec_loop_in` is which loop-rule builder stands inside
    the induction; the measure is carried across the passes exactly as there. -/
theorem contract_of_duty_rec_loop
    (ρ : Env) (f : String) (body : List Stmt) (pre : State → Prop)
    (post : State → State → Option Value → Prop) (e : Expr) (wf : State → Prop)
    (id : String) (lbody : List Stmt) (v : String) (inv : Expr)
    (hr : Runs ρ f body)
    (hl : RunsLoop ρ id lbody v)
    (hb : ∀ (s0 : State), pre s0 → ContractBelow ρ f e s0 pre post →
      ∀ (t : State) (k : Int), wf t → eval t e = eval s0 e →
        eval t inv = some (.bool true) →
        ∃ t', finalState (exec ρ lbody { t with local' := bindLocal t.local' v (.int k) })
                = some t'
              ∧ (wf t' ∧ eval t' e = eval s0 e) ∧ eval t' inv = some (.bool true))
    (hd : ∀ t, pre t → ContractBelow ρ f e t pre post →
        LoopRule ρ id (fun u => wf u ∧ eval u e = eval t e) inv →
      ∃ s', finalState (exec ρ body t) = some s' ∧ post t s' (finalValue (exec ρ body t))) :
    Contract ρ f pre post :=
  contract_of_duty_rec ρ f body pre post e hr (fun t ht hcb =>
    hd t ht hcb
      (looprule_of_body ρ id (fun u => wf u ∧ eval u e = eval t e) inv lbody v hl
        (fun u k hu hiv => hb t ht hcb u k hu.1 hu.2 hiv)))


end Gabbro.Body
