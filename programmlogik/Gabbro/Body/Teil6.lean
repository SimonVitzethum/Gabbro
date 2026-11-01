module

public import Lean
public import Gabbro.Body.Teil5

@[expose] public section


/-- Every `ρ f t` in `e` where `ρ` is a local of type `Env` -- with `t` closed (no loose
    bound variables), because only a closed state can be handed to a contract. -/
partial def GabbroMeta.collectCalls (e : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let acc ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr × Lean.Expr))
  let rec go (e : Lean.Expr) : MetaM Unit := do
    match e with
    | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if fn.isFVar && args.size ≥ 2 && !args[0]!.hasLooseBVars && !args[1]!.hasLooseBVars then
        let ty ← whnf (← inferType fn)
        if (← isDefEq ty (mkConst ``Gabbro.Body.Env)) then
          acc.modify (·.push (fn, args[0]!, args[1]!))
      for a in args do go a
      go fn
    | .lam _ _ b _ | .forallE _ _ b _ => go b
    | .letE _ _ v b _ => go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  acc.get


open Lean Elab Tactic Meta in
/-- **Has an earlier pass already instantiated `key = ρ f t` on THIS goal?** The mark
    `gabbro_seen : key = key` says so -- per goal, and not per invocation: a sibling goal an
    opening left has no instance yet and gets its own. -/
def GabbroMeta.seenKey (key : Lean.Expr) : TacticM Bool := do
  (← getMainGoal).withContext do
    let lctx ← getLCtx
    lctx.anyM fun d => do
      if d.isImplementationDetail then return false
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``Eq 3 && d.userName.toString.startsWith "gabbro_seen" then
        isDefEq ty.getAppArgs[1]! key
      else
        return false

open Lean Elab Tactic Meta in
/-- **Every hypothesis of the main goal that carries a contract of `ρ f`**, with the number of
    holes its instantiation at a state opens: a plain `Contract` one (the precondition), a
    `LoopRule`, `ContractBelow` or `ContractBelowM` two, a `LoopRuleP` three (the counter at
    zero). -/
def GabbroMeta.contractDecls (ρ f : Lean.Expr) : TacticM (Array (Lean.LocalDecl × Nat)) := do
  (← getMainGoal).withContext do
    let lctx ← getLCtx
    let mut out : Array (Lean.LocalDecl × Nat) := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``Gabbro.Body.Contract 4 then
        let a := ty.getAppArgs
        if (← isDefEq a[0]! ρ) && (← isDefEq a[1]! f) then out := out.push (d, 1)
      else if ty.isAppOfArity ``Gabbro.Body.LoopRule 4 then
        let a := ty.getAppArgs
        if (← isDefEq a[0]! ρ) && (← isDefEq a[1]! f) then out := out.push (d, 2)
      -- **the rule of a loop that counts its passes** (agent b, 2026-09-08): a third
      -- premise, that the counter stands at zero -- the `bindName` right before the loop
      else if ty.isAppOfArity ``Gabbro.Body.LoopRuleP 5 then
        let a := ty.getAppArgs
        if (← isDefEq a[0]! ρ) && (← isDefEq a[1]! f) then out := out.push (d, 3)
      -- the bounded self-contract: two holes as well -- the precondition and `Below`
      else if ty.isAppOfArity ``Gabbro.Body.ContractBelow 6 then
        let a := ty.getAppArgs
        if (← isDefEq a[0]! ρ) && (← isDefEq a[1]! f) then out := out.push (d, 2)
      -- the bounded contract of a cycle member: the member is a literal, its name first
      else if ty.isAppOfArity ``Gabbro.Body.ContractBelowM 4 then
        let a := ty.getAppArgs
        let m := a[1]!
        if m.isAppOfArity ``Gabbro.Body.Member.mk 5 then
          if (← isDefEq a[0]! ρ) && (← isDefEq m.getAppArgs[0]! f) then out := out.push (d, 2)
    pure out

open Lean Elab Tactic Meta in
/-- **`gabbro_calls Γ [lemmas]` -- the composition, applied.** For every `ρ f t` the goal
    mentions and every hypothesis `Contract ρ f pre post` or `LoopRule ρ f wf inv`, the
    instance at `t` is added as a hypothesis; its precondition is tried (the well-typed
    world by `gabbro_wf`, the rest by the simp set) and stays as a goal where it is the
    person's -- a `requires` the model cannot compute is exactly the `V` duty. The instance
    is then simplified with the same set, so its clauses become rewrites. -/
elab "gabbro_calls" Γ:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  for _ in [0:12] do
    -- an instance that says `False` (a callee that never returns) closes the goal
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let calls ← g.withContext do
      let ty ← instantiateMVars (← g.getType)
      let mut cs ← GabbroMeta.collectCalls ty
      -- **A dead branch keeps its calls in its case hypotheses** (GabbroV lane, 2026-09-29).
      -- `gabbro_cases` splits on a condition that reads a call's answer -- the invariant a
      -- lock acquire hands over, a callee's promise -- and the branch where the condition
      -- fails has the goal `False`: no call is left in it to instantiate, and the very
      -- contract that refutes the condition never gets applied. The calls of the `hcase`
      -- hypotheses are collected there, and only there.
      if ty.consumeMData.isConstOf ``False then
        for d in ← getLCtx do
          if !d.isImplementationDetail && d.userName.eraseMacroScopes == `hcase then
            cs := cs ++ (← GabbroMeta.collectCalls (← instantiateMVars d.type))
      pure cs
    -- **innermost first**: a call whose state is another call's answer needs that one's
    -- instance in the context of its own precondition -- and a hole opened earlier does
    -- not see a hypothesis added later
    let calls := calls.qsort (fun a b => a.2.2.approxDepth < b.2.2.approxDepth)
    let mut progress := false
    -- the holes this round leaves open, for the second pass over them below
    let mut roundHoles : Array MVarId := #[]
    for (ρ, f, t) in calls do
      if (← getGoals).isEmpty then return
      let key := mkApp2 ρ f t
      -- in the goal's context: `isDefEq` on a state expression reads its variables --
      -- and a call instantiated by an EARLIER pass left its mark (`gabbro_seen : c = c`),
      -- so that a second pass does not instantiate (and open, and split) it again
      -- (per GOAL, by the mark, and not per invocation: a sibling goal an opening left
      -- has no instance yet, and gets its own)
      if ← GabbroMeta.seenKey key then continue
      let decls ← GabbroMeta.contractDecls ρ f
      for (d, nholes) in decls do
        -- one instance that cannot be built is skipped, not the whole composition
        let saved ← saveState
        try
          let c ← (← getMainGoal).withContext do Term.exprToSyntax d.toExpr
          let tt ← (← getMainGoal).withContext do Term.exprToSyntax t
          let hn := mkIdent (← mkFreshUserName `hc)
          let before ← getGoals
          let lctxBefore ← (← getMainGoal).withContext getLCtx
          if nholes == 3 then
            evalTactic (← `(tactic| have $hn := $c $tt ?_ ?_ ?_))
          else if nholes == 2 then
            evalTactic (← `(tactic| have $hn := $c $tt ?_ ?_))
          else
            evalTactic (← `(tactic| have $hn := $c $tt ?_))
          let after ← getGoals
          let main := after[0]!
          let holes := after.filter (fun m => m != main && !(before.contains m))
          -- the mark, on the goal that holds the instance (and so on everything opened
          -- from it), before the opening -- not on a sibling that never got it
          let ks ← main.withContext do Term.exprToSyntax key
          let mark := mkIdent (← mkFreshUserName `gabbro_seen)
          setGoals [main]
          evalTactic (← `(tactic| have $mark : $ks = $ks := rfl))
          let main ← getMainGoal
          -- the precondition: the well-typed world and what computes; the rest stays
          let mut rest : List MVarId := []
          for h in holes do
            setGoals [h]
            -- closed whole where it can be; `Below` by computation and arithmetic; else
            -- reduced as far as the simp set goes, and left
            -- **`(simp only …; done)` FIRST, and it is not decoration** (measured
            -- 2026-09-08): where the simp set closes the precondition WHOLE, the goal list
            -- is empty when `<;>` reaches it, and `<;>` on no goals is an error -- so the
            -- alternative that had just succeeded FAILED, and a precondition the model
            -- decides by itself fell through to the person. `(fun _ => True) t` is the
            -- smallest instance and it stood in `_pruefung/Thole.lean`.
            evalTactic (← `(tactic| try (first
              | (simp only [$ts,*]; done)
              | (simp only [$ts,*]; (try apply And.intro) <;> first | gabbro_wf $Γ | (gabbro_simp_hyps [$ts,*]; done))
              | (gabbro_simp_hyps [$ts,*]; done)
              | (gabbro_simp_hyps [$ts,*]; omega)
              | (simp only [$ts,*]; (try apply And.intro) <;> first | gabbro_wf $Γ | (gabbro_simp_hyps [$ts,*]; done) | skip))))
            -- what a hole leaves is kept -- every hole's, not only the last one's
            rest := rest ++ (← getGoals)
          roundHoles := roundHoles ++ rest.toArray
          setGoals ([main] ++ rest ++ (after.filter (fun m => m != main && before.contains m)))
          -- the instance, simplified into rewrites
          evalTactic (← `(tactic| try simp only [$ts,*, Gabbro.Body.Contract, Gabbro.Body.LoopRule, Gabbro.Body.LoopRuleP, Gabbro.Body.ContractBelow, Gabbro.Body.ContractBelowM] at $hn:ident))
          evalTactic (← `(tactic| try simp [$ts,*, ↓Gabbro.Body.eval_and_true_iff, ↓Gabbro.Body.eval_hasShape_true_iff, Gabbro.Body.orBool_true_iff,
            Gabbro.Body.eval, Gabbro.Body.binop, Gabbro.Body.unop, Gabbro.Body.bindLocal, Gabbro.Body.bindAll] at $hn:ident))
          -- and opened: the call's answer, the invariants, every clause as its own fact
          evalTactic (← `(tactic| try gabbro_open $hn:ident))
          -- **and the goal learns the answer at once**: the next call outward reads this
          -- one's answer through a `match`, and only with `(ρ f t).2 = some v` rewritten
          -- is its state closed -- a call under a `match` arm has a loose variable and is
          -- not collected. So the facts the opening added are used as rewrites on the goal
          -- here, in the same round, and not in a later step of the pipeline
          if !(← getGoals).isEmpty then
            let news ← (← getMainGoal).withContext do
              let mut out : Array (TSyntax `term) := #[]
              for d in ← getLCtx do
                if d.isImplementationDetail then continue
                if lctxBefore.contains d.fvarId then continue
                if (← instantiateMVars d.type).isAppOfArity ``Eq 3 then
                  out := out.push (← Term.exprToSyntax d.toExpr)
              pure out
            if !news.isEmpty then
              let lems : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← news.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:term)
              -- (with the bindings and stores at their names: the instance was built
              -- over the reduced state, and the goal has to show the same state)
              evalTactic (← `(tactic| try simp only [$lems,*, Gabbro.Body.bindLocal_here, Gabbro.Body.bindLocal_elsewhere,
                Gabbro.Body.store_here, Gabbro.Body.store_elsewhere]))
          progress := true
          if (← getGoals).isEmpty then return
        catch ex =>
          saved.restore
          logInfo m!"gabbro_calls: skipped an instance: {ex.toMessageData}"
    -- **The hole phase** (`PLAN.md` §5.2 item 4). A hole opened for one instance is a
    -- METAVARIABLE, and its context was fixed when it was opened: it never receives the
    -- `have`s the later instances of the same round add to the MAIN goal. Two calls at the
    -- SAME state have the same `approxDepth`, so innermost-first does not order them, and
    -- the second's precondition can be exactly what the first's contract says -- the hole
    -- then stands for no reason but the order.
    --
    -- The hole does hold the theorem's own contract binders, so the fact is derivable
    -- THERE. So once every instance of the round is in, **the round's calls are
    -- instantiated a second time inside each hole** -- the round's, not the hole's own: the
    -- precondition mentions the state, not the call that decides it, and `collectCalls`
    -- over the hole would find nothing.
    --
    -- **An instance whose own premises do not ALL close at once is rolled back.** That is
    -- what keeps a hole from spawning a hole -- the phase either finishes an instance or
    -- leaves the hole exactly as it was.
    if !roundHoles.isEmpty then
      let gs ← getGoals
      let mut out : List MVarId := []
      for g in gs do
        if roundHoles.contains g && !(← g.isAssigned) then
          setGoals [g]
          for (ρ, f, t) in calls do
            if (← getGoals).isEmpty then break
            let key := mkApp2 ρ f t
            if ← GabbroMeta.seenKey key then continue
            let decls ← GabbroMeta.contractDecls ρ f
            for (d, nholes) in decls do
              if (← getGoals).isEmpty then break
              let saved ← saveState
              try
                let c ← (← getMainGoal).withContext do Term.exprToSyntax d.toExpr
                let tt ← (← getMainGoal).withContext do Term.exprToSyntax t
                let hn := mkIdent (← mkFreshUserName `hc)
                let before ← getGoals
                if nholes == 3 then
                  evalTactic (← `(tactic| have $hn := $c $tt ?_ ?_ ?_))
                else if nholes == 2 then
                  evalTactic (← `(tactic| have $hn := $c $tt ?_ ?_))
                else
                  evalTactic (← `(tactic| have $hn := $c $tt ?_))
                let after ← getGoals
                let main := after[0]!
                let subs := after.filter (fun m => m != main && !(before.contains m))
                let mut closed := true
                for s in subs do
                  setGoals [s]
                  evalTactic (← `(tactic| try (first
                    | (simp only [$ts,*]; done)
                    | (simp only [$ts,*]; (try apply And.intro) <;> first | gabbro_wf $Γ | (gabbro_simp_hyps [$ts,*]; done))
                    | (gabbro_simp_hyps [$ts,*]; done)
                    | (gabbro_simp_hyps [$ts,*]; omega))))
                  unless (← getGoals).isEmpty do closed := false
                if !closed then
                  saved.restore
                else
                  setGoals [main]
                  let ks ← main.withContext do Term.exprToSyntax key
                  let mark := mkIdent (← mkFreshUserName `gabbro_seen)
                  evalTactic (← `(tactic| have $mark : $ks = $ks := rfl))
                  evalTactic (← `(tactic| try simp only [$ts,*, Gabbro.Body.Contract, Gabbro.Body.LoopRule, Gabbro.Body.LoopRuleP, Gabbro.Body.ContractBelow, Gabbro.Body.ContractBelowM] at $hn:ident))
                  evalTactic (← `(tactic| try simp [$ts,*, ↓Gabbro.Body.eval_and_true_iff, ↓Gabbro.Body.eval_hasShape_true_iff, Gabbro.Body.orBool_true_iff,
                    Gabbro.Body.eval, Gabbro.Body.binop, Gabbro.Body.unop, Gabbro.Body.bindLocal, Gabbro.Body.bindAll] at $hn:ident))
                  evalTactic (← `(tactic| try gabbro_open $hn:ident))
                  -- the hole closes here or it does not; either way it keeps the fact
                  evalTactic (← `(tactic| all_goals (try (first
                    | assumption
                    | (gabbro_simp_hyps [$ts,*]; done)
                    | (simp_all; done)))))
                  progress := true
              catch _ =>
                saved.restore
          out := out ++ (← getGoals)
        else
          out := out ++ [g]
      setGoals out
    if !progress then break

open Lean.Parser.Tactic in
/-- `gabbro_simp_at h [lemmas]` -- the model's simp set, at a hypothesis: what turns an
    opened invariant or an instantiated contract into rewrites. -/
macro "gabbro_simp_at" h:ident "[" ts:simpLemma,* "]" : tactic =>
  `(tactic| ((try simp only [$ts,*] at $h:ident); try simp [Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, Gabbro.Body.unop,
                  Gabbro.Body.binop, Gabbro.Body.bits,
                  Gabbro.Body.finalState, Gabbro.Body.finalValue,
                  Gabbro.Body.bindLocal, Gabbro.Body.bindAll,
                  Gabbro.Body.evalAll, Gabbro.Body.allBelow_true_iff,
                  ↓Gabbro.Body.eval_and_true_iff, ↓Gabbro.Body.eval_hasShape_true_iff, Gabbro.Body.orBool_true_iff,
                  Gabbro.Body.Contract, Gabbro.Body.Frame, Gabbro.Body.ContractBelow,
                  Gabbro.Body.Below, Gabbro.Body.ContractBelowM, Gabbro.Body.BelowM,
                  Gabbro.Body.LoopRule, Gabbro.Body.Place.carrier,
                  Gabbro.Body.wrap, Gabbro.Body.pickArm, Gabbro.Body.pickTag, $ts,*] at $h:ident))

open Lean Elab Tactic Meta in
/-- Every `store σ p v q` in `e` with `p` and `q` closed and not syntactically equal --
    the reads the model could not decide, because whether two indices coincide is a
    fact about the program and not about the form. -/
partial def GabbroMeta.collectStores (e : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let acc ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  let rec go (e : Lean.Expr) : MetaM Unit := do
    match e with
    | .app .. =>
      if e.isAppOfArity ``Gabbro.Body.store 4 then
        let a := e.getAppArgs
        let p := a[1]!
        let q := a[3]!
        if !p.hasLooseBVars && !q.hasLooseBVars && p != q then
          acc.modify (·.push (q, p))
      for a in e.getAppArgs do go a
      go e.getAppFn
    | .lam _ _ b _ | .forallE _ _ b _ => go b
    | .letE _ _ v b _ => go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  acc.get

open Lean Elab Tactic Meta in
/-- **`gabbro_split` -- the case split on every undecided read.** For every `store σ p v q`
    the goal still holds, `q = p` or `q ≠ p`; in the first the read is the stored value, in
    the second the old one. Which of the two holds is the person's logic; that a split is
    what stands between the goal and it is not. -/
syntax "gabbro_split" : tactic
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| gabbro_split) => do
  let g ← getMainGoal
  let stores ← g.withContext do
    GabbroMeta.collectStores (← instantiateMVars (← g.getType))
  if stores.isEmpty then return
  let (q, p) := stores[0]!
  let qs ← g.withContext do Term.exprToSyntax q
  let ps ← g.withContext do Term.exprToSyntax p
  let hn := mkIdent (← mkFreshUserName `hq)
  -- **Two places that differ in carrier or field are different, and no split is needed**
  -- -- `slot "Faeden" x "gruende"` is never `slot "Endpunkte" e "wartet"`; the case split
  -- is for the same field at two indices.
  let lit (e : Lean.Expr) : Option String := match e with
    | .lit (.strVal x) => some x
    | _ => none
  let differ : Bool :=
    if q.isAppOfArity ``Gabbro.Body.Place.slot 3 && p.isAppOfArity ``Gabbro.Body.Place.slot 3 then
      let qa := q.getAppArgs; let pa := p.getAppArgs
      match lit qa[0]!, lit qa[2]!, lit pa[0]!, lit pa[2]! with
      | some c1, some f1, some c2, some f2 => c1 != c2 || f1 != f2
      | _, _, _, _ => false
    else if q.isAppOfArity ``Gabbro.Body.Place.global 1 && p.isAppOfArity ``Gabbro.Body.Place.global 1 then
      match lit q.getAppArgs[0]!, lit p.getAppArgs[0]! with
      | some a, some b => a != b
      | _, _ => false
    else
      -- a slot against a global, a field against a slot: different constructors
      (q.getAppFn.constName? != p.getAppFn.constName?) && q.getAppFn.isConst && p.getAppFn.isConst
  if differ then
    GabbroMeta.haveClosed (← `(tactic| have $hn : $qs ≠ $ps := ?_)) (← `(tactic| simp))
    evalTactic (← `(tactic| all_goals (try simp only [Gabbro.Body.store_elsewhere _ _ _ _ $hn:ident])))
    evalTactic (← `(tactic| all_goals (try gabbro_split)))
    return
  evalTactic (← `(tactic| by_cases $hn : $qs = $ps))
  evalTactic (← `(tactic| all_goals (try (first
    | (subst $hn; simp only [Gabbro.Body.store_here])
    | (simp only [$hn:ident, Gabbro.Body.store_here])
    | (simp only [Gabbro.Body.store_elsewhere _ _ _ _ $hn:ident])))))
  -- the split hypothesis, read as what it says about the INDICES: `slot T k f = slot T j f`
  -- is `k = j`, and that is the form the person's argument (and `omega`) reads
  evalTactic (← `(tactic| all_goals (try simp only [Gabbro.Body.Place.slot.injEq,
    Gabbro.Body.Place.field.injEq, Gabbro.Body.Place.global.injEq, eq_self_iff_true,
    and_true, true_and, not_and] at $hn:ident)))
  evalTactic (← `(tactic| all_goals (try gabbro_split)))

open Lean Elab Tactic Meta in
/-- Every `decide p` in `e` with `p` closed -- the conditions of the program's `if`s and
    comparisons, which `simp` cannot decide because they are about the values and not
    about the form. -/
partial def GabbroMeta.collectDecides (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let acc ← IO.mkRef (#[] : Array Lean.Expr)
  let rec go (e : Lean.Expr) : MetaM Unit := do
    match e with
    | .app .. =>
      if e.isAppOfArity ``Decidable.decide 2 then
        let p := e.getAppArgs[0]!
        if !p.hasLooseBVars && !p.hasMVar then
          acc.modify (·.push p)
      -- the condition of an `if` (a `bindLocal` on names, a `pickTag` on a case name)
      else if e.isAppOfArity ``ite 5 then
        let c := e.getAppArgs[1]!
        if !c.hasLooseBVars && !c.hasMVar && c.hasFVar then
          acc.modify (·.push c)
      -- a boolean READ (`Value.bool b`, `b` a variable the well-typed world gave) is a
      -- condition too: `b = true` or not
      else if e.isAppOfArity ``Gabbro.Body.Value.bool 1 then
        let b := e.getAppArgs[0]!
        -- a variable, or a term over one (`!b`, `b && c`) -- not a literal, and not a
        -- `decide`, which is collected as the proposition it decides
        if !b.hasLooseBVars && !b.hasMVar && !b.isConstOf ``Bool.true && !b.isConstOf ``Bool.false
            && !b.isAppOfArity ``Decidable.decide 2 && b.hasFVar then
          acc.modify (·.push (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) b (mkConst ``Bool.true)))
      for a in e.getAppArgs do go a
      go e.getAppFn
    -- a boolean variable on its own (`#returned`, a flag) is a condition too
    | .fvar _ =>
      if (← inferType e).isConstOf ``Bool then
        acc.modify (·.push (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) e (mkConst ``Bool.true)))
    | .lam _ _ b _ | .forallE _ _ b _ => go b
    | .letE _ _ v b _ => go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  acc.get

open Lean Elab Tactic Meta in
/-- **`gabbro_cases n [lemmas]` -- the program's control flow, as a case split.** For
    every condition the goal still holds as `decide p`, `p` or `¬ p`, and the branch is
    taken; at most `n` splits deep, because every split doubles the goals. This is the
    split a person would write by hand before every `if` of the body; which branch holds
    what is their logic, that the split stands before it is not. -/
syntax "gabbro_cases" num "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
open Lean Elab Tactic Meta in
