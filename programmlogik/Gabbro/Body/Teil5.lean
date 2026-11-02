module

public import Lean
public meta import Lean
public import Gabbro.Body.Teil4

@[expose] public section


namespace Gabbro.Body

/-- A read from a well-typed world has the declared shape. -/
theorem WF_read (Γ : Typing) (σ : World) (p : Place) (sh : Shape) (h : WF Γ σ)
    (hp : Γ p = some sh) : (σ p).hasShape sh = true := h p sh hp

/-- **A read outside the callee's frame reads the caller's world.** Written as a rewrite so
    that `simp` applies it; the side condition is a list membership over string literals,
    which `simp` decides. -/
theorem Frame_read (ρ : Env) (f : String) (w : List String) (fr : Frame ρ f w) (t : State)
    (p : Place) (h : p.carrier ∉ w) : (ρ f t).1.world p = t.world p := fr t p h

end Gabbro.Body

open Lean Elab Tactic Meta in
/-- **A `have` whose holes are closed HERE, by `tac`, or the `have` fails** -- never a
    nested `by`: that one is elaborated later, and where it does not close, its failure is
    LOGGED as an error of the theorem while the tactic that wrote it goes on believing it
    succeeded (measured 2026-09-07, `kapraum`). -/
meta def GabbroMeta.haveClosed (stx : TSyntax `tactic) (tac : TSyntax `tactic) : TacticM Unit := do
  let g ← getMainGoal
  let gty ← g.withContext (instantiateMVars (← g.getType))
  let before ← getGoals
  evalTactic stx
  let after ← getGoals
  let fresh := after.filter (fun m => !(before.contains m))
  let mut main? : Option MVarId := none
  let mut holes : List MVarId := []
  for m in fresh do
    let ty ← m.withContext (instantiateMVars (← m.getType))
    if main?.isNone && (← m.withContext (isDefEq ty gty)) then
      main? := some m
    else
      holes := holes ++ [m]
  let some main := main? | throwError "gabbro: the `have` left no main goal"
  for h in holes do
    setGoals [h]
    evalTactic tac
    unless (← getGoals).isEmpty do throwError "gabbro: a hole of the `have` stays open"
  setGoals ([main] ++ after.filter (fun m => !(fresh.contains m)))

open Lean Elab Tactic Meta in
/-- **`gabbro_assumption` -- `assumption`, and INTO the conjunctions.** A contract's
    instance is one hypothesis `wellFormed t' ∧ inv t' ∧ …`; the well-typed world the next
    call demands is its first half. This closes a goal that is a conjunct of a hypothesis,
    at any depth of a right-nested `∧`. -/
elab "gabbro_assumption" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let rec search (proof : Lean.Expr) (ty : Lean.Expr) : Nat → MetaM (Option Lean.Expr)
      | 0 => do if ← isDefEq ty target then return some proof else return none
      | depth + 1 => do
        if ← isDefEq ty target then return some proof
        let ty ← whnfR ty
        if ty.isAppOfArity ``And 2 then
          let a := ty.getAppArgs[0]!
          let b := ty.getAppArgs[1]!
          if let some p ← search (mkApp3 (mkConst ``And.left) a b proof) a depth then return some p
          if let some p ← search (mkApp3 (mkConst ``And.right) a b proof) b depth then return some p
        return none
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if let some p ← search d.toExpr (← instantiateMVars d.type) 8 then
        g.assign p
        replaceMainGoal []
        return
    throwError "gabbro_assumption: no hypothesis, or conjunct of one, matches the goal"

open Lean Elab Tactic Meta in
/-- **A hypothesis, opened**: a conjunction into its parts, an existential into witness and
    fact, a disjunction into two goals -- as far down as it goes. What a contract instance
    says about a call's answer (`∃ x, (ρ f t).2 = some (.int x)`) becomes the rewrite
    `simp` can use. -/
meta partial def GabbroMeta.openHyp (n : Name) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then return
  let g ← getMainGoal
  let some d ← g.withContext (return (← getLCtx).findFromUserName? n) | return
  let ty ← g.withContext (whnfR (← instantiateMVars d.type))
  -- the hypothesis itself STAYS -- it may be named in a simp set (`hall`, `c_m`); what is
  -- opened is a copy
  let h ← if n.hasMacroScopes then pure (mkIdent n) else do
    let c := mkIdent (← mkFreshUserName `hcopy)
    let orig := mkIdent n
    evalTactic (← `(tactic| have $c := $orig))
    pure c
  if ty.isAppOfArity ``And 2 then
    let a := mkIdent (← mkFreshUserName `ha)
    let b := mkIdent (← mkFreshUserName `hb)
    evalTactic (← `(tactic| obtain ⟨$a, $b⟩ := $h))
    openHyp a.getId (fuel - 1)
    openHyp b.getId (fuel - 1)
  else if ty.isAppOfArity ``Exists 2 then
    let x := mkIdent (← mkFreshUserName `x)
    let hx := mkIdent (← mkFreshUserName `hx)
    evalTactic (← `(tactic| obtain ⟨$x, $hx⟩ := $h))
    openHyp hx.getId (fuel - 1)
  -- a shape fact about a value becomes the witness it stands for
  else if ty.isAppOfArity ``Eq 3 && ty.getAppArgs[1]!.isAppOfArity ``Gabbro.Body.Value.hasShape 2
      && ty.getAppArgs[2]!.isConstOf ``Bool.true then
    let sh := ty.getAppArgs[1]!.getAppArgs[1]!
    let w := mkIdent (← mkFreshUserName `hw)
    let lemma : Option Name :=
      if sh.isConstOf ``Gabbro.Body.Shape.int then some ``Gabbro.Body.Value.hasShape_int_true
      else if sh.isConstOf ``Gabbro.Body.Shape.bool then some ``Gabbro.Body.Value.hasShape_bool_true
      else if sh.isAppOfArity ``Gabbro.Body.Shape.sum 1 then some ``Gabbro.Body.Value.hasShape_sum_true
      else if sh.isConstOf ``Gabbro.Body.Shape.opt then some ``Gabbro.Body.Value.hasShape_opt_true
      else if sh.isAppOfArity ``Gabbro.Body.Shape.intIn 2 then some ``Gabbro.Body.Value.hasShape_intIn_true
      else none
    if let some l := lemma then
      let ls := mkIdent l
      if sh.isAppOfArity ``Gabbro.Body.Shape.intIn 2 then
        evalTactic (← `(tactic| have $w := $ls _ _ _ $h))
      else if sh.isAppOfArity ``Gabbro.Body.Shape.sum 1 then
        evalTactic (← `(tactic| have $w := $ls _ _ $h))
      else
        evalTactic (← `(tactic| have $w := $ls _ $h))
      openHyp w.getId (fuel - 1)
  -- a case fact about a `tagged` value: computed against the case names in play, it is
  -- the disjunction of the possible cases (with their payloads), and that is opened
  else if ty.isAppOfArity ``Eq 3 && ty.getAppArgs[1]!.isAppOfArity ``Gabbro.Body.Shape.caseOk 3 then
    let c := mkIdent (← mkFreshUserName `hcase)
    evalTactic (← `(tactic| have $c := $h))
    evalTactic (← `(tactic| try simp [Gabbro.Body.Shape.caseOk_cons, Gabbro.Body.Shape.caseOk_nil, *] at $c:ident))
    -- (a `simp at` that turns the copy into `True` clears it; nothing to open then)
    let g' ← getMainGoal
    if (← g'.withContext (return (← getLCtx).findFromUserName? c.getId)).isSome then
      openHyp c.getId (fuel - 1)
  else if ty.isAppOfArity ``Or 2 then
    let a := mkIdent (← mkFreshUserName `ho)
    evalTactic (← `(tactic| rcases $h:ident with $a:ident | $a:ident))
    let gs ← getGoals
    let mut out : List MVarId := []
    for g' in gs do
      setGoals [g']
      openHyp a.getId (fuel - 1)
      out := out ++ (← getGoals)
    setGoals out

open Lean Elab Tactic Meta in
/-- `gabbro_open h` -- `GabbroMeta.openHyp`, as a tactic. -/
elab "gabbro_open " h:ident : tactic => do
  GabbroMeta.openHyp h.getId 16

open Lean Elab Tactic Meta in
/-- **`gabbro_open_hyps` -- every hypothesis opened** that is a conjunction, an existential,
    a disjunction or a shape fact: what the openings and the instances left folded. A
    disjunction splits the goal; that is the case analysis a `tagged` value's cases or a
    `return` inside a loop demand anyway. -/
elab "gabbro_open_hyps" : tactic => do
  let g ← getMainGoal
  let names ← g.withContext do
    let mut out : Array Name := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``Or 2
          || (ty.isAppOfArity ``Eq 3 && ty.getAppArgs[1]!.isAppOfArity ``Gabbro.Body.Value.hasShape 2)
          || (ty.isAppOfArity ``Eq 3 && ty.getAppArgs[1]!.isAppOfArity ``Gabbro.Body.Shape.caseOk 3) then
        out := out.push d.userName
    pure out
  for n in names do
    -- in every goal an earlier opening left
    let gs ← getGoals
    let mut out : List MVarId := []
    for g' in gs do
      setGoals [g']
      try GabbroMeta.openHyp n 16 catch _ => pure ()
      out := out ++ (← getGoals)
    setGoals out

open Lean Elab Tactic Meta in
/-- **`gabbro_instantiate` -- a quantified invariant, at the index in play.** For every
    hypothesis `∀ k, k < N → P k` (what a `forallSlots` becomes) and every `k : Nat` of the
    context that is known to be below a bound, `P k` is added -- the instance a person
    would `specialize` by hand before arguing about the slot the body touched. -/
elab "gabbro_instantiate" : tactic => do
  withMainContext do
    let lctx ← getLCtx
    -- the quantified facts: at the top of a hypothesis, or inside its conjunctions
    let mut quantified : Array Lean.Expr := #[]
    let mut indices : Array LocalDecl := #[]
    let rec collect (proof : Lean.Expr) (ty : Lean.Expr) : Nat → MetaM (Array Lean.Expr)
      | 0 => pure #[]
      | depth + 1 => do
        match ty with
        | .forallE _ (.const ``Nat []) (.forallE _ bound _ _) _ =>
          if bound.isAppOfArity ``LT.lt 4 then return #[proof] else return #[]
        | _ =>
          let ty ← whnfR ty
          if ty.isAppOfArity ``And 2 then
            let a := ty.getAppArgs[0]!
            let b := ty.getAppArgs[1]!
            let l ← collect (mkApp3 (mkConst ``And.left) a b proof) a depth
            let r ← collect (mkApp3 (mkConst ``And.right) a b proof) b depth
            return l ++ r
          return #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      quantified := quantified ++ (← collect d.toExpr ty 6)
      if ty.isConstOf ``Nat then indices := indices.push d
    let mut n := 0
    for q in quantified do
      for k in indices do
        if n ≥ 12 then break
        -- only where the bound is at hand: `k < N` by a hypothesis or by arithmetic
        let saved ← saveState
        try
          let hq ← Term.exprToSyntax q
          let hk := mkIdent k.userName
          let w := mkIdent (← mkFreshUserName `hq)
          GabbroMeta.haveClosed (← `(tactic| have $w := $hq $hk ?_)) (← `(tactic| first | assumption | omega))
          n := n + 1
        catch _ =>
          saved.restore

open Lean Elab Tactic Meta in
/-- Every closed `allBelow f n` in `e`. -/
meta partial def GabbroMeta.collectAllBelow (e : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let acc ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  let rec go (e : Lean.Expr) : MetaM Unit := do
    match e with
    | .app .. =>
      if e.isAppOfArity ``Gabbro.Body.allBelow 2 && !e.hasLooseBVars && !e.hasMVar then
        acc.modify (·.push (e.getAppArgs[0]!, e.getAppArgs[1]!))
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
/-- **`gabbro_forall [lemmas]` -- a quantified premise that the context already grants.**
    A `forallSlots` the goal is stuck on (a callee's `requires` over the whole table, an
    invariant demanded at a loop's entry) is `allBelow f n`; where every instance follows
    from the hypotheses, the whole is `some (.bool true)`, and the goal's `match` on it
    reduces. The instance is proved by `simp_all` after `gabbro_instantiate`; what does
    not go through this way stays. -/
syntax "gabbro_forall" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| gabbro_forall [$ts,*]) => do
    let g ← getMainGoal
    let terms ← g.withContext do GabbroMeta.collectAllBelow (← instantiateMVars (← g.getType))
    for (f, n) in terms do
      let saved ← saveState
      try
        let fs ← (← getMainGoal).withContext do Term.exprToSyntax f
        let ns ← (← getMainGoal).withContext do Term.exprToSyntax n
        let w := mkIdent (← mkFreshUserName `hall)
        GabbroMeta.haveClosed
          (← `(tactic| have $w : Gabbro.Body.allBelow $fs $ns = some (.bool true) := ?_))
          (← `(tactic| (refine (Gabbro.Body.allBelow_true_iff _ _).mpr ?_
                        intro k hk
                        gabbro_instantiate
                        simp_all [$ts,*])))
        evalTactic (← `(tactic| simp only [$w:ident]))
      catch _ =>
        saved.restore

/-- Every closed `a &&& b`, `a ^^^ b`, `a ||| b` over `Nat` in `e` -- `0`, `1`, `2` for the
    operator. -/
meta partial def GabbroMeta.collectAnd (e : Lean.Expr) (acc : Array (Nat × Lean.Expr × Lean.Expr)) :
    Array (Nat × Lean.Expr × Lean.Expr) :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let acc := args.foldl (fun a x => GabbroMeta.collectAnd x a) (GabbroMeta.collectAnd fn acc)
    if args.size == 6 && args[0]!.isConstOf ``Nat && !args[4]!.hasLooseBVars && !args[5]!.hasLooseBVars then
      if fn.isConstOf ``HAnd.hAnd then acc.push (0, args[4]!, args[5]!)
      else if fn.isConstOf ``HXor.hXor then acc.push (1, args[4]!, args[5]!)
      else if fn.isConstOf ``HOr.hOr then acc.push (2, args[4]!, args[5]!)
      else acc
    else acc
  | .lam _ _ b _ | .forallE _ _ b _ => GabbroMeta.collectAnd b acc
  | .letE _ _ v b _ => GabbroMeta.collectAnd b (GabbroMeta.collectAnd v acc)
  | .mdata _ b => GabbroMeta.collectAnd b acc
  | .proj _ _ b => GabbroMeta.collectAnd b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- **`gabbro_bits` -- the bounds of every bitwise `and` in the goal.** `x & 251` on a `u8`
    field is `↑(x.toNat &&& 251)` in the model, and `omega` cannot read `&&&`; the bounds
    `n &&& m ≤ m` and `n &&& m ≤ n` (`Nat.and_le_right/left`) are what the store into a
    ranged place needs, and the person never wrote them (2026-09-08, `planer`). -/
elab "gabbro_bits" : tactic => do
  let g ← getMainGoal
  let ands ← g.withContext do
    let mut acc := GabbroMeta.collectAnd (← instantiateMVars (← g.getType)) #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      acc := GabbroMeta.collectAnd (← instantiateMVars d.type) acc
    pure acc
  let ands := ands.foldl (fun acc t => if acc.any (fun u => u.1 == t.1 && u.2.1 == t.2.1 && u.2.2 == t.2.2) then acc else acc.push t) #[]
  let close ← `(tactic| first | assumption | omega)
  for (op, a, b) in ands do
    let as ← (← getMainGoal).withContext do Term.exprToSyntax a
    let bs ← (← getMainGoal).withContext do Term.exprToSyntax b
    if op == 0 then
      evalTactic (← `(tactic| try have := @Nat.and_le_right $as $bs))
      evalTactic (← `(tactic| try have := @Nat.and_le_left $as $bs))
    else
      -- `x ^^^ y < 2^n` and `x ||| y < 2^n` where both operands are below `2^n`: the
      -- width is tried from the narrowest up, and the first the context bounds is kept
      for w in [8, 16, 32, 64] do
        let ws := Syntax.mkNumLit (toString w)
        let saved ← saveState
        try
          if op == 1 then
            GabbroMeta.haveClosed (← `(tactic| have := @Nat.xor_lt_two_pow $as $bs $ws ?_ ?_)) close
          else
            GabbroMeta.haveClosed (← `(tactic| have := @Nat.or_lt_two_pow $as $bs $ws ?_ ?_)) close
          break
        catch _ => saved.restore

/-- **`gabbro_wf Γ` closes `WF Γ (store … (store σ p v) …)` from `WF Γ σ`**: every store
    is peeled with `WF_store`, and the side condition -- the stored value has the declared
    shape -- is decided by unfolding the typing, or read off a well-typed world where the
    value is a read (`WF_read`). Where neither applies the goal stays for the person. -/
syntax "gabbro_wf" ident : tactic
macro_rules
  | `(tactic| gabbro_wf $t:ident) =>
    `(tactic| first
        | assumption
        | gabbro_assumption
        | (apply Gabbro.Body.WF_store
           · gabbro_wf $t
           · (intro sh hsh; simp [$t:ident] at hsh;
              -- an undeclared place has no shape: `hsh` is `False`, and the goal is gone
              first
                | done
                | (subst hsh;
                   first
                     | (simp [Gabbro.Body.Value.hasShape]; done)
                     -- a ranged place: the bounds, by the arithmetic the context carries
                     | (simp [Gabbro.Body.Value.hasShape]; gabbro_bits; omega)
                     | (apply Gabbro.Body.WF_read <;> first | assumption | gabbro_assumption | rfl)
                     -- a value read from another ranged place: its witness, then the bounds
                     | (simp [Gabbro.Body.Value.hasShape, *]; gabbro_bits; omega)
                     | (simp_all [Gabbro.Body.Value.hasShape]; gabbro_bits; omega)
                     -- and what none of these closes is left reduced, for the person
                     | simp [Gabbro.Body.Value.hasShape]))))

/-- **`gabbro_shape Γ` closes `∃ n, σ p = .int n` (and the bool, sum and option forms)
    from a well-typed world** -- what a routine's answer read from a place owes to the
    promise's shape clause. The place's shape is decided by `rfl` over the typing. -/
syntax "gabbro_shape" ident : tactic
open Lean Elab Tactic Meta in
/-- Every read `σ p` of a world in `e` -- `State.world s` applied to a closed place. -/
meta partial def GabbroMeta.collectReads (e : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let acc ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  let rec go (e : Lean.Expr) : MetaM Unit := do
    match e with
    | .app fn p =>
      -- a state's world -- NOT a world with stores on it: a read through a store is first
      -- decided by `gabbro_split` (the same place, or another), and only what is left is a
      -- read of the state's world; a witness taken before the split would hide the store
      let isWorld := fn.isAppOfArity ``Gabbro.Body.State.world 1
        || (match fn with | .proj ``Gabbro.Body.State 0 _ => true | _ => false)
      if isWorld && !fn.hasLooseBVars && !p.hasLooseBVars then
        acc.modify (·.push (fn, p))
      go fn
      go p
    | .lam _ _ b _ | .forallE _ _ b _ => go b
    | .letE _ _ v b _ => go v; go b
    | .mdata _ b => go b
    | .proj _ _ b => go b
    | _ => pure ()
  go e
  acc.get
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| gabbro_shape $Γ:ident) => do
    let g ← getMainGoal
    -- the reads of the goal, and of the hypotheses: an instantiated invariant reads the
    -- slot the body touched, and its witness is what lets the two be compared
    let reads ← g.withContext do
      let mut all ← GabbroMeta.collectReads (← instantiateMVars (← g.getType))
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        all := all ++ (← GabbroMeta.collectReads (← instantiateMVars d.type))
      -- each read once, and not one that already has its witness (`σ p = .int n`)
      let lctx ← getLCtx
      let witnessed (σ p : Lean.Expr) : Bool := lctx.any fun d =>
        !d.isImplementationDetail && d.type.isAppOfArity ``Eq 3
          && d.type.getAppArgs[1]! == mkApp σ p
      let mut uniq : Array (Lean.Expr × Lean.Expr) := #[]
      for r in all do
        if uniq.size ≥ 16 then break
        if witnessed r.1 r.2 then continue
        unless uniq.any (fun u => u.1 == r.1 && u.2 == r.2) do uniq := uniq.push r
      pure uniq
    let mut opened := false
    for (σ, p) in reads do
      let σs ← (← getMainGoal).withContext do Term.exprToSyntax σ
      let ps ← (← getMainGoal).withContext do Term.exprToSyntax p
      for l in [``Gabbro.Body.WF_int, ``Gabbro.Body.WF_intIn, ``Gabbro.Body.WF_bool, ``Gabbro.Body.WF_sum, ``Gabbro.Body.WF_opt] do
        let saved ← saveState
        try
          let w := mkIdent (← mkFreshUserName `hw)
          let ls := mkIdent l
          -- `rfl` decides the shape: a wrong lemma fails to elaborate and is skipped
          if l == ``Gabbro.Body.WF_sum then
            GabbroMeta.haveClosed (← `(tactic| have $w := $ls $Γ $σs $ps _ ?_ rfl))
              (← `(tactic| first | assumption | gabbro_assumption | gabbro_wf $Γ))
          else if l == ``Gabbro.Body.WF_intIn then
            GabbroMeta.haveClosed (← `(tactic| have $w := $ls $Γ $σs $ps _ _ ?_ rfl))
              (← `(tactic| first | assumption | gabbro_assumption | gabbro_wf $Γ))
          else
            GabbroMeta.haveClosed (← `(tactic| have $w := $ls $Γ $σs $ps ?_ rfl))
              (← `(tactic| first | assumption | gabbro_assumption | gabbro_wf $Γ))
          GabbroMeta.openHyp w.getId 4
          opened := true
          break
        catch _ =>
          saved.restore
    if opened then
      evalTactic (← `(tactic| all_goals (try (simp [*]; done))))


