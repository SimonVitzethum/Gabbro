module

public import Lean
public meta import Lean
public import Gabbro.Body.Teil6

@[expose] public section


open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| gabbro_cases $n:num [$ts,*]) => do
  let depth := n.getNat
  if depth == 0 then return
  let g ← getMainGoal
  let ps ← g.withContext do
    let all ← GabbroMeta.collectDecides (← instantiateMVars (← g.getType))
    -- a condition already decided by a hypothesis (`p` or `¬ p`) is not split again --
    -- that is what bounds the recursion
    let lctx ← getLCtx
    all.filterM fun p => do
      let np := mkNot p
      -- `¬ a < b` reads, once `simp_all` has been over it, as `b ≤ a` -- and `¬ a ≤ b`
      -- as `b < a`: the normalised form of the other branch decides the condition too
      let flipped : Option Lean.Expr ←
        try
          if p.isAppOfArity ``LT.lt 4 then
            let a := p.getAppArgs
            pure (some (← mkAppM ``LE.le #[a[3]!, a[2]!]))
          else if p.isAppOfArity ``LE.le 4 then
            let a := p.getAppArgs
            pure (some (← mkAppM ``LT.lt #[a[3]!, a[2]!]))
          else pure none
        catch _ => pure none
      let decided ← lctx.anyM fun d => do
        if d.isImplementationDetail then return false
        let ty ← instantiateMVars d.type
        if (← isDefEq ty p) || (← isDefEq ty np) then return true
        match flipped with
        | some f => isDefEq ty f
        | none => return false
      return !decided
  if ps.isEmpty then return
  let p := ps[0]!
  let pstx ← g.withContext do Term.exprToSyntax p
  let hn := mkIdent (← mkFreshUserName `hcase)
  evalTactic (← `(tactic| by_cases $hn : $pstx))
  -- the decision itself, as an equation of the `Bool` the program reads: `decide p =
  -- true` / `= false` -- stated, not left to `simp` to see through the instance (measured
  -- 2026-09-08, `58`: a `¬ x < y` in the context and a `decide (x < y)` in the goal, and
  -- the goal stood)
  evalTactic (← `(tactic| all_goals (try simp only [decide_eq_true $hn:ident])))
  evalTactic (← `(tactic| all_goals (try simp only [decide_eq_false $hn:ident])))
  -- the branch is taken cheaply: the condition rewritten, closed decisions evaluated,
  -- the `match` on the outcome reduced -- the model's full simp set runs once, later
  evalTactic (← `(tactic| all_goals (try simp only
    [$hn:ident, $ts,*, Gabbro.Body.bindLocal, Gabbro.Body.bindAll, Gabbro.Body.eval,
     Bool.not_eq_true,
     decide_true, decide_false, decide_eq_true_eq, decide_eq_false_iff_not, decide_not,
     eq_self_iff_true, Bool.not_true, Bool.not_false, Bool.true_and, Bool.and_true,
     Bool.false_and, Bool.and_false, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
     ite_true, ite_false, if_true, if_false, not_false_eq_true, not_true_eq_false])))
  let n' := Syntax.mkNumLit (toString (depth - 1))
  evalTactic (← `(tactic| all_goals (try gabbro_cases $n' [$ts,*])))

open Lean Elab Tactic Meta in
/-- **`gabbro_try n tac` runs `tac` under a budget of `n` thousand heartbeats, and where
    `tac` fails OR runs out of the budget the state is restored** -- the goal then goes to
    the next step, and at the end to the person, instead of the theorem going red. A plain
    `try` would not do: a heartbeat timeout is a runtime exception it does not catch, and a
    `set_option maxHeartbeats … in` inside a tactic block changes the options but not the
    limit the check reads (`Core.Context.maxHeartbeats`, measured 2026-09-07). -/
elab "gabbro_try " n:num tac:tactic : tactic => do
  let s ← saveState
  -- `n` is in the unit of the `maxHeartbeats` option (thousands of raw heartbeats)
  let budget := n.getNat * 1000 * 1000
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := budget }) <|
      Core.withCurrHeartbeats <| evalTactic tac)
    (fun _ => s.restore)

/-! ### `simp_all`, run at most once per goal (agent b, 2026-09-08)

    **The pipeline runs `simp_all` FOUR times** (steps 33, 37, 40, 45 of `gabbro_pipeline_b`),
    and `_pruefung/zeit.sh` says what that costs. Measured 2026-09-08, per module, summed over
    its theorems:

    | module | s33 | s37 | s40 | s45 | whole pipeline |
    |---|---|---|---|---|---|
    | `beispiele/01-tabelle`   |  7.0 s | 24.4 s |  6.5 s | 22.6 s |  86.1 s |
    | `messung/fragmente/F01`  | 43.8 s |  9.2 s |  9.0 s |  9.4 s | 122.2 s |
    | `beispiele/09-ohne-zeiger` |  9.1 s | 10.3 s |  3.5 s |  3.1 s |  37.8 s |
    | `messung/caprock/kapraum` | 13.1 s |  2.6 s |  0.3 s |  0.2 s |  58.4 s |

    **Between 27 % and 70 % of the pipeline is these four steps**, and no other step comes
    near (the next largest anywhere is `gabbro_calls` at 6.6 s). The steps BETWEEN them are
    cheap -- `gabbro_shape`, `gabbro_wf`, `gabbro_split`, `gabbro_instantiate` together cost
    0.75 s on `01-tabelle` between step 40 and step 45 -- so where they change nothing, step 45
    re-derives step 40's answer from step 40's goal.

    **A goal that has not moved does not need the tactic again**, and "has not moved" is not a
    guess here: a tactic that changes a goal produces a NEW metavariable, and one that fails
    under `try` leaves the old one. So the memo is by `MVarId`, and it is exact.

    **What is NOT memoised: a step the heartbeat budget cut off.** `gabbro_try` shares one
    budget over `all_goals`, so a goal late in the list can be left untouched for want of
    budget and be reached with plenty at the next step. Recording that goal would lose the
    closure the later step would have made -- so a runtime cut-off records nothing.

    **And the FOURTH `simp_all` (old step 45) is gone entirely.** With the memo in, it still
    cost 22.8 s on `01-tabelle` -- its goals really had moved under steps 41-44 -- so whether
    it closes anything was measured and not argued: the pipeline was run over the whole
    corpus without it. **192 modules, 0 Lean errors, 24 `sorry`, and the `sorry`s stand on
    exactly the same nine files with exactly the same counts**; the corpus fell from 417 s to
    402 s and `01-tabelle` from 39 s to 27 s. *That is a statement about THIS corpus:* a step
    that closes nothing over 192 units and 500-odd theorems is not thereby a step that closes
    nothing. Putting it back is one line, and a unit that needs it will say so with a `sorry`,
    not silently. -/
meta initialize gabbroSimpAllFixed : IO.Ref (Array Lean.MVarId) ← IO.mkRef #[]

open Lean Elab Tactic in
/-- Forget every goal the memo holds -- at the head of the pipeline, so that one theorem's
    metavariable numbers can never answer for another's. -/
elab "gabbro_simp_all_reset" : tactic => do
  gabbroSimpAllFixed.set #[]

open Lean Elab Tactic in
/-- `simp_all` on this goal, unless it has already been run on exactly this goal. Never
    throws: the pipeline reads it as `try simp_all` did. -/
elab "gabbro_simp_all_once" : tactic => do
  if (← getGoals).isEmpty then return
  let g ← getMainGoal
  if (← gabbroSimpAllFixed.get).contains g then return
  let saved ← saveState
  let decided ← tryCatchRuntimeEx
    (do
      try
        evalTactic (← `(tactic| simp_all))
      catch _ =>
        saved.restore
      pure true)
    (fun _ => do saved.restore; pure false)
  if decided then
    let gs ← getGoals
    gabbroSimpAllFixed.modify fun a => gs.foldl (fun a m => if a.contains m then a else a.push m) a

/-- Every `a.tdiv b` / `a.tmod b` (closed) in `e` -- `true` for a division. -/
meta partial def GabbroMeta.collectDivMod (e : Lean.Expr) (acc : Array (Bool × Lean.Expr × Lean.Expr)) :
    Array (Bool × Lean.Expr × Lean.Expr) :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let acc := args.foldl (fun a x => GabbroMeta.collectDivMod x a) (GabbroMeta.collectDivMod fn acc)
    if args.size == 2 && !args[0]!.hasLooseBVars && !args[1]!.hasLooseBVars then
      if fn.isConstOf ``Int.tdiv then acc.push (true, args[0]!, args[1]!)
      else if fn.isConstOf ``Int.tmod then acc.push (false, args[0]!, args[1]!)
      else acc
    else acc
  | .lam _ _ b _ | .forallE _ _ b _ => GabbroMeta.collectDivMod b acc
  | .letE _ _ v b _ => GabbroMeta.collectDivMod b (GabbroMeta.collectDivMod v acc)
  | .mdata _ b => GabbroMeta.collectDivMod b acc
  | .proj _ _ b => GabbroMeta.collectDivMod b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- **`gabbro_divmod` -- the bounds of every truncated division and remainder in the goal.**
    `omega` reads `/` and `%` only by a literal; a `summe / n` over a variable `n` is opaque
    to it, and a declared range on the quotient (`0 ≤ summe / n ≤ 1000000`) was the person's.
    For every `a.tdiv b` and `a.tmod b` the goal mentions, the facts `0 ≤ a → 0 ≤ b → 0 ≤
    a.tdiv b`, `0 ≤ a → a.tdiv b ≤ a`, `0 ≤ a → 0 ≤ a.tmod b`, `0 < b → a.tmod b < b` are
    added where their premises are arithmetic the context already decides (`omega`); a fact
    whose premise is not is left out, not left open. -/
elab "gabbro_divmod" : tactic => do
  let g ← getMainGoal
  -- in the goal and in the hypotheses: a split condition (`hcase`) carries the term too
  let terms ← g.withContext do
    let mut acc := GabbroMeta.collectDivMod (← instantiateMVars (← g.getType)) #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      acc := GabbroMeta.collectDivMod (← instantiateMVars d.type) acc
    pure acc
  let close ← `(tactic| first | assumption | omega)
  -- each term once: the same quotient stands in the goal and in three hypotheses
  let terms := terms.foldl (fun acc t => if acc.any (fun u => u.1 == t.1 && u.2.1 == t.2.1 && u.2.2 == t.2.2) then acc else acc.push t) #[]
  for (isDiv, a, b) in terms do
    let as ← (← getMainGoal).withContext do Term.exprToSyntax a
    let bs ← (← getMainGoal).withContext do Term.exprToSyntax b
    let facts : Array (TSyntax `tactic) ←
      if isDiv then
        pure #[← `(tactic| have := @Int.tdiv_nonneg $as $bs ?_ ?_),
               ← `(tactic| have := Int.tdiv_le_self (a := $as) $bs ?_)]
      else
        pure #[← `(tactic| have := Int.tmod_nonneg (a := $as) $bs ?_),
               ← `(tactic| have := Int.tmod_lt_of_pos $as (b := $bs) ?_)]
    for f in facts do
      let saved ← saveState
      try
        GabbroMeta.haveClosed f close
      catch _ =>
        saved.restore

/-- Every closed `a * b` over `Int` in `e`. -/
meta partial def GabbroMeta.collectMul (e : Lean.Expr) (acc : Array (Lean.Expr × Lean.Expr)) :
    Array (Lean.Expr × Lean.Expr) :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let acc := args.foldl (fun a x => GabbroMeta.collectMul x a) (GabbroMeta.collectMul fn acc)
    if fn.isConstOf ``HMul.hMul && args.size == 6 && args[0]!.isConstOf ``Int
        && !args[4]!.hasLooseBVars && !args[5]!.hasLooseBVars then
      acc.push (args[4]!, args[5]!)
    else acc
  | .lam _ _ b _ | .forallE _ _ b _ => GabbroMeta.collectMul b acc
  | .letE _ _ v b _ => GabbroMeta.collectMul b (GabbroMeta.collectMul v acc)
  | .mdata _ b => GabbroMeta.collectMul b acc
  | .proj _ _ b => GabbroMeta.collectMul b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- **`gabbro_mul` -- the bounds of every product in the goal.** `omega` is linear: a
    `versatz * faktor` over two variables is an atom to it, and the declared range of a sum
    that holds such a product (`basis + versatz * faktor ≤ 2^64 - 1`) -- the very arithmetic
    the checker decided over the operands' ranges -- was the person's. For every `a * b`
    the goal mentions: `0 ≤ a * b` where both factors are non-negative, and `a * b ≤ A * B`
    where the context bounds each factor by a literal (`a ≤ A`, `b ≤ B`) -- each fact only
    where `omega` closes its premises. -/
elab "gabbro_mul" : tactic => do
  let g ← getMainGoal
  let prods ← g.withContext do
    let mut acc := GabbroMeta.collectMul (← instantiateMVars (← g.getType)) #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      acc := GabbroMeta.collectMul (← instantiateMVars d.type) acc
    pure acc
  let close ← `(tactic| first | assumption | omega)
  -- the literal upper bound of `x` the context holds, if any: a hypothesis `x ≤ A`
  let upper (x : Lean.Expr) : TacticM (Option (TSyntax `term)) := do
    (← getMainGoal).withContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        if ty.isAppOfArity ``LE.le 4 && ty.getAppArgs[0]!.isConstOf ``Int then
          let a := ty.getAppArgs[2]!
          let b := ty.getAppArgs[3]!
          if (← isDefEq a x) && b.isAppOfArity ``OfNat.ofNat 3 then
            return some (← Term.exprToSyntax d.toExpr)
      return none
  let prods := prods.foldl (fun acc t => if acc.any (fun u => u.1 == t.1 && u.2 == t.2) then acc else acc.push t) #[]
  for (a, b) in prods do
    let as ← (← getMainGoal).withContext do Term.exprToSyntax a
    let bs ← (← getMainGoal).withContext do Term.exprToSyntax b
    let saved ← saveState
    try
      GabbroMeta.haveClosed (← `(tactic| have := @Int.mul_nonneg $as $bs ?_ ?_)) close
    catch _ => saved.restore
    if let (some ha, some hb) := (← upper a, ← upper b) then
      let saved ← saveState
      try
        GabbroMeta.haveClosed (← `(tactic| have := Int.mul_le_mul $ha $hb ?_ ?_)) close
      catch _ => saved.restore

open Lean Elab Tactic Meta in
/-- **`gabbro_values` -- a callee's answer without a shape promise, by cases.**
    A `let x = f(a) else (e) { … }` reads the answer as `match some v with | reason e => …
    | v => …`, and where `f`'s promise carries no shape (a record or a token) it
    only says `∃ v, r = some v`: the `match` stands on a variable. It is split by its
    constructors here -- each arm is one program path, and the other steps close them. -/
elab "gabbro_values" : tactic => do
  let g ← getMainGoal
  let vs ← g.withContext do
    let e ← instantiateMVars (← g.getType)
    let mut out : Array Lean.FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if d.type.isConstOf ``Gabbro.Body.Value && e.containsFVar d.fvarId then
        out := out.push d.fvarId
    pure out
  for v in vs.toList.take 2 do
    let vs ← (← getMainGoal).withContext do Term.exprToSyntax (mkFVar v)
    evalTactic (← `(tactic| all_goals (try cases $vs:term)))

open Lean.Parser.Tactic in
/-- **The pipeline** -- what `gabbro_auto` runs before it gives up on a goal: the model's
    simp set, the control-flow split, the composition over the calls, the well-typed world,
    the split on undecided reads, `simp_all`, and the arithmetic. Every step runs under its
    own budget (`gabbro_try`), so that no step can take the theorem down with it. -/
macro "gabbro_pipeline" "[" ts:simpLemma,* "]" "using" t:ident : tactic =>
  `(tactic| (gabbro_simp_all_reset;
             gabbro_try 300 (gabbro_simp [$ts,*]);
             gabbro_try 300 (all_goals (try gabbro_cases 4 [$ts,*]));
             gabbro_try 600 (all_goals (try gabbro_calls $t [$ts,*]));
             gabbro_try 100 (all_goals (try gabbro_open_hyps));
             gabbro_try 300 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 300 (all_goals (try gabbro_forall [$ts,*]));
             gabbro_try 300 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_cases 3 [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 50 (all_goals (try (repeat' apply And.intro)));
             gabbro_try 50 (all_goals (try intros));
             gabbro_try 100 (all_goals (try gabbro_wf $t));
             gabbro_try 50 (all_goals (try gabbro_shape $t));
             -- the witnesses `gabbro_shape` opened are new conditions and new indices --
             -- and a branch opened by a call's answer may hold a call of its own
             gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_cases 3 [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_calls $t [$ts,*]));
             -- an answer without a shape, by its constructors -- and the call after it
             gabbro_try 100 (all_goals (try gabbro_values));
             gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 300 (all_goals (try gabbro_calls $t [$ts,*]));
             gabbro_try 100 (all_goals (try gabbro_values));
             gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 300 (all_goals (try gabbro_calls $t [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_forall [$ts,*]));
             gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*]));
             gabbro_try 50 (all_goals (try (repeat' apply And.intro)));
             gabbro_try 50 (all_goals (try intros));
             gabbro_try 100 (all_goals (try gabbro_wf $t));
             gabbro_try 50 (all_goals (try gabbro_shape $t));
             gabbro_try 200 (all_goals (try (simp [$ts,*, *]; done)));
             gabbro_try 300 (all_goals (try (gabbro_split <;> (try intros) <;> (try (simp [$ts,*, *]; done)))));
             gabbro_try 200 (all_goals (try (simp [$ts,*, *]; done)));
             gabbro_try 100 (all_goals (try gabbro_instantiate));
             -- a witness named twice (`x = x'`, a case name `"Kurz" = w`) is one name --
             -- and two case names for one value are a contradiction `simp_all` then sees
             gabbro_try 50 (all_goals (try subst_vars));
             -- from here on WITHOUT the caller's list: `simp_all` clears a hypothesis it
             -- has used up (`hall`), and a name in the list that is gone fails the step
             gabbro_try 600 (all_goals (try gabbro_simp_all_once));
             -- what `simp_all` exposed: reads at the indices in play, stores at them,
             -- instances one binder further in -- twice, because each round opens the next
             gabbro_try 50 (all_goals (try gabbro_shape $t));
             -- a store whose value a late witness names is well-typed by that witness
             gabbro_try 100 (all_goals (try gabbro_wf $t));
             -- a condition a late witness made decidable (`narrow i to 0 ..< hinterlegt`
             -- reads a global whose witness came with `gabbro_shape`) is split here again
             gabbro_try 200 (all_goals (try gabbro_cases 3 []));
             gabbro_try 300 (all_goals (try gabbro_simp_all_once));
             gabbro_try 200 (all_goals (try (gabbro_split <;> (try intros))));
             gabbro_try 100 (all_goals (try gabbro_instantiate));
             gabbro_try 300 (all_goals (try gabbro_simp_all_once));
             gabbro_try 50 (all_goals (try gabbro_shape $t));
             gabbro_try 100 (all_goals (try gabbro_wf $t));
             gabbro_try 200 (all_goals (try (gabbro_split <;> (try intros))));
             gabbro_try 100 (all_goals (try gabbro_instantiate));
             gabbro_try 100 (all_goals (try gabbro_wf $t));
             -- the bounds of a division or remainder by a variable, then the arithmetic
             gabbro_try 100 (all_goals (try gabbro_divmod));
             gabbro_try 100 (all_goals (try gabbro_mul));
             gabbro_try 100 (all_goals (try gabbro_bits));
             gabbro_try 100 (all_goals (try omega))))


/-! ### The measuring copy of the pipeline (agent b, 2026-09-08)

    `gabbro_pipeline_b` is `gabbro_pipeline` with every step wrapped in `gabbro_timed`, which
    logs the step's wall time. It exists so that "which step burns the seconds" is a
    measurement and not a guess; nothing generated uses it, and it is never in a proof. -/

open Lean Elab Tactic in
/-- Run a tactic and log how long it took, under a name. -/
elab "gabbro_timed" nm:str tac:tactic : tactic => do
  let t0 ← IO.monoMsNow
  evalTactic tac
  let t1 ← IO.monoMsNow
  logInfo m!"GTIME {nm.getString} {t1 - t0}"

open Lean.Parser.Tactic in
macro "gabbro_pipeline_b" "[" ts:simpLemma,* "]" "using" t:ident : tactic =>
  `(tactic| (gabbro_simp_all_reset;
             gabbro_timed "s00" (gabbro_try 300 (gabbro_simp [$ts,*]));
             gabbro_timed "s01" (gabbro_try 300 (all_goals (try gabbro_cases 4 [$ts,*])));
             gabbro_timed "s02" (gabbro_try 600 (all_goals (try gabbro_calls $t [$ts,*])));
             gabbro_timed "s03" (gabbro_try 100 (all_goals (try gabbro_open_hyps)));
             gabbro_timed "s04" (gabbro_try 300 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s05" (gabbro_try 300 (all_goals (try gabbro_forall [$ts,*])));
             gabbro_timed "s06" (gabbro_try 300 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s07" (gabbro_try 200 (all_goals (try gabbro_cases 3 [$ts,*])));
             gabbro_timed "s08" (gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s09" (gabbro_try 50 (all_goals (try (repeat' apply And.intro))));
             gabbro_timed "s10" (gabbro_try 50 (all_goals (try intros)));
             gabbro_timed "s11" (gabbro_try 100 (all_goals (try gabbro_wf $t)));
             gabbro_timed "s12" (gabbro_try 50 (all_goals (try gabbro_shape $t)));
             -- the witnesses `gabbro_shape` opened are new conditions and new indices --
             -- and a branch opened by a call's answer may hold a call of its own
             gabbro_timed "s13" (gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s14" (gabbro_try 200 (all_goals (try gabbro_cases 3 [$ts,*])));
             gabbro_timed "s15" (gabbro_try 200 (all_goals (try gabbro_calls $t [$ts,*])));
             -- an answer without a shape, by its constructors -- and the call after it
             gabbro_timed "s16" (gabbro_try 100 (all_goals (try gabbro_values)));
             gabbro_timed "s17" (gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s18" (gabbro_try 300 (all_goals (try gabbro_calls $t [$ts,*])));
             gabbro_timed "s19" (gabbro_try 100 (all_goals (try gabbro_values)));
             gabbro_timed "s20" (gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s21" (gabbro_try 300 (all_goals (try gabbro_calls $t [$ts,*])));
             gabbro_timed "s22" (gabbro_try 200 (all_goals (try gabbro_forall [$ts,*])));
             gabbro_timed "s23" (gabbro_try 200 (all_goals (try gabbro_simp_hyps [$ts,*])));
             gabbro_timed "s24" (gabbro_try 50 (all_goals (try (repeat' apply And.intro))));
             gabbro_timed "s25" (gabbro_try 50 (all_goals (try intros)));
             gabbro_timed "s26" (gabbro_try 100 (all_goals (try gabbro_wf $t)));
             gabbro_timed "s27" (gabbro_try 50 (all_goals (try gabbro_shape $t)));
             gabbro_timed "s28" (gabbro_try 200 (all_goals (try (simp [$ts,*, *]; done))));
             gabbro_timed "s29" (gabbro_try 300 (all_goals (try (gabbro_split <;> (try intros) <;> (try (simp [$ts,*, *]; done))))));
             gabbro_timed "s30" (gabbro_try 200 (all_goals (try (simp [$ts,*, *]; done))));
             gabbro_timed "s31" (gabbro_try 100 (all_goals (try gabbro_instantiate)));
             -- a witness named twice (`x = x'`, a case name `"Kurz" = w`) is one name --
             -- and two case names for one value are a contradiction `simp_all` then sees
             gabbro_timed "s32" (gabbro_try 50 (all_goals (try subst_vars)));
             -- from here on WITHOUT the caller's list: `simp_all` clears a hypothesis it
             -- has used up (`hall`), and a name in the list that is gone fails the step
             gabbro_timed "s33" (gabbro_try 600 (all_goals (try gabbro_simp_all_once)));
             -- what `simp_all` exposed: reads at the indices in play, stores at them,
             -- instances one binder further in -- twice, because each round opens the next
             gabbro_timed "s34" (gabbro_try 50 (all_goals (try gabbro_shape $t)));
             -- a store whose value a late witness names is well-typed by that witness
             gabbro_timed "s35" (gabbro_try 100 (all_goals (try gabbro_wf $t)));
             -- a condition a late witness made decidable (`narrow i to 0 ..< hinterlegt`
             -- reads a global whose witness came with `gabbro_shape`) is split here again
             gabbro_timed "s36" (gabbro_try 200 (all_goals (try gabbro_cases 3 [])));
             gabbro_timed "s37" (gabbro_try 300 (all_goals (try gabbro_simp_all_once)));
             gabbro_timed "s38" (gabbro_try 200 (all_goals (try (gabbro_split <;> (try intros)))));
             gabbro_timed "s39" (gabbro_try 100 (all_goals (try gabbro_instantiate)));
             gabbro_timed "s40" (gabbro_try 300 (all_goals (try gabbro_simp_all_once)));
             gabbro_timed "s41" (gabbro_try 50 (all_goals (try gabbro_shape $t)));
             gabbro_timed "s42" (gabbro_try 100 (all_goals (try gabbro_wf $t)));
             gabbro_timed "s43" (gabbro_try 200 (all_goals (try (gabbro_split <;> (try intros)))));
             gabbro_timed "s44" (gabbro_try 100 (all_goals (try gabbro_instantiate)));
             -- **s45 is gone, and the gap in the numbers is deliberate** (agent b,
             -- 2026-09-08): the step names have to keep meaning what the measurements of
             -- this file mean by them. A measuring copy that renumbers measures a different
             -- pipeline than the one it is a copy of.
             gabbro_timed "s46" (gabbro_try 100 (all_goals (try gabbro_wf $t)));
             -- the bounds of a division or remainder by a variable, then the arithmetic
             gabbro_timed "s47" (gabbro_try 100 (all_goals (try gabbro_divmod)));
             gabbro_timed "s48" (gabbro_try 100 (all_goals (try gabbro_mul)));
             gabbro_timed "s49" (gabbro_try 100 (all_goals (try gabbro_bits)));
             gabbro_timed "s50" (gabbro_try 100 (all_goals (try omega)))))

open Lean.Parser.Tactic in
macro "gabbro_auto" "[" ts:simpLemma,* "]" "using" t:ident : tactic =>
  `(tactic| (gabbro_pipeline [$ts,*] using $t; all_goals sorry))

