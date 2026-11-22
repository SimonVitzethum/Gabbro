module
public import Bruecke.Zertifikat.Fertig
public meta import Lean.Elab.Tactic
@[expose] public section

/-!
# Proof support: conditions over symbolic values as integer arithmetic

What symbolic execution leaves over parameters, call results and state are conditions
`wahr? (eval σ₀ e σ ρ) = true` over a lowered expression `e`. `gabbrov_arith` translates `e` into
integer arithmetic over its atoms (a parameter, a call result, a read of the state: `x.n`), checks
by the kernel's definitional equality that the translation IS the evaluation, replaces the condition
by it, adds the declared ranges of the atoms and tries `omega`. Nothing is trusted: a translation the
kernel does not accept is not used, and what `omega` does not close stays, readable, for the user.
-/

namespace Gabbro.Bruecke

open Lean Meta Elab Tactic

/-- The kernel's weak head normal form, or the term itself. -/
meta def kw (e : Lean.Expr) : MetaM Lean.Expr := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r => pure r
  | .error _ => pure e

/-- The integer of a kernel-normal `Int` literal. -/
meta def intWert? (e : Lean.Expr) : MetaM (Option Int) := do
  let e ← kw e
  if e.isAppOfArity ``Int.ofNat 1 then
    let n ← kw (e.getArg! 0)
    return n.rawNatLit?.map Int.ofNat
  if e.isAppOfArity ``Int.negSucc 1 then
    let n ← kw (e.getArg! 0)
    return n.rawNatLit?.map fun k => Int.negSucc k
  return none

/-- An integer atom: `v.n` of a value `v : Zahl lo hi`, remembered with its range. -/
meta def atomInt (v : Lean.Expr) : StateRefT (Array Lean.Expr) MetaM Lean.Expr := do
  let ty ← kw (← inferType v)
  unless ty.isAppOfArity `Gabbro.Grammatik.Zahl 2 do throwError "gabbrov_arith: not a number"
  modify fun as => if as.contains v then as else as.push v
  return mkAppN (mkConst `Gabbro.Grammatik.Zahl.n) #[ty.getArg! 0, ty.getArg! 1, v]

mutual
/-- The integer of a lowered expression `e` evaluated in `ρ`. -/
meta partial def tInt (s0 s : Lean.Expr) (e ρ : Lean.Expr) : StateRefT (Array Lean.Expr) MetaM Lean.Expr := do
  let e ← kw e
  let a := e.getAppArgs
  let n := a.size
  match e.getAppFn.constName? with
  | some `Gabbro.Grammatik.Expr.lit => do
      -- as a numeral (`omega` reads numerals, not `Int.ofNat` of a raw literal)
      match ← intWert? a[n-1]! with
      | some v => pure (toExpr v)
      | none => pure a[n-1]!
  | some `Gabbro.Grammatik.Expr.var => tVarInt ρ a[n-1]!
  | some `Gabbro.Grammatik.Expr.widen => tInt s0 s a[n-1]! ρ
  | some `Gabbro.Grammatik.Expr.add => do mkAppM ``HAdd.hAdd #[← tInt s0 s a[n-2]! ρ, ← tInt s0 s a[n-1]! ρ]
  | some `Gabbro.Grammatik.Expr.sub => do mkAppM ``HSub.hSub #[← tInt s0 s a[n-2]! ρ, ← tInt s0 s a[n-1]! ρ]
  | some `Gabbro.Grammatik.Expr.mul => do mkAppM ``HMul.hMul #[← tInt s0 s a[n-2]! ρ, ← tInt s0 s a[n-1]! ρ]
  | some `Gabbro.Grammatik.Expr.neg => do mkAppM ``Neg.neg #[← tInt s0 s a[n-1]! ρ]
  | some `Gabbro.Grammatik.Expr.div => do
      pure (mkApp2 (mkConst ``Int.tdiv) (← tInt s0 s a[n-2]! ρ) (← tInt s0 s a[n-1]! ρ))
  | some `Gabbro.Grammatik.Expr.rem => do
      pure (mkApp2 (mkConst ``Int.tmod) (← tInt s0 s a[n-2]! ρ) (← tInt s0 s a[n-1]! ρ))
  | _ => atomInt (← mkAppM `Gabbro.Grammatik.eval #[s0, e, s, ρ])

/-- The integer of variable `x` of the environment `ρ`. -/
meta partial def tVarInt (ρ x : Lean.Expr) : StateRefT (Array Lean.Expr) MetaM Lean.Expr := do
  let ρ' ← kw ρ
  let x' ← kw x
  if ρ'.isAppOf `Gabbro.Grammatik.Env.cons && ρ'.getAppNumArgs ≥ 2 then
    let ra := ρ'.getAppArgs
    if x'.isAppOf `Gabbro.Grammatik.Var.here then return ← tWertInt ra[ra.size - 2]!
    if x'.isAppOf `Gabbro.Grammatik.Var.there then return ← tVarInt ra[ra.size - 1]! x'.appArg!
  atomInt (← mkAppM `Gabbro.Grammatik.Env.get #[ρ, x])

/-- The integer of a value term. -/
meta partial def tWertInt (v : Lean.Expr) : StateRefT (Array Lean.Expr) MetaM Lean.Expr := do
  let v := v.headBeta
  let a := v.getAppArgs
  match v.getAppFn.constName? with
  | some `Gabbro.Grammatik.eval => if a.size ≥ 4 then tInt a[a.size-4]! a[a.size-2]! a[a.size-3]! a[a.size-1]! else atomInt v
  | some `Gabbro.Grammatik.evalErg =>
      let e ← kw a[a.size-3]!
      if e.isAppOf `Gabbro.Grammatik.ErgExpr.val then tInt a[a.size-4]! a[a.size-2]! e.appArg! a[a.size-1]!
      else atomInt v
  | some `Gabbro.Grammatik.Zahl.weiter => tWertInt a[a.size-1]!
  -- a callee's result at its declared type: the value itself
  | some `Gabbro.Grammatik.ergWert => tWertInt a[a.size-1]!
  | _ => atomInt v
end

/-- The Boolean of a lowered condition `e` evaluated in `ρ`. -/
meta partial def tBool (s0 s : Lean.Expr) (e ρ : Lean.Expr) : StateRefT (Array Lean.Expr) MetaM Lean.Expr := do
  let e ← kw e
  let a := e.getAppArgs
  let n := a.size
  let rel (op : Lean.Name) : StateRefT (Array Lean.Expr) MetaM Lean.Expr := do
    let x ← tInt s0 s a[n-2]! ρ
    let y ← tInt s0 s a[n-1]! ρ
    mkDecide (← mkAppM op #[x, y])
  match e.getAppFn.constName? with
  | some `Gabbro.Grammatik.Expr.tru => pure (mkConst ``Bool.true)
  | some `Gabbro.Grammatik.Expr.fls => pure (mkConst ``Bool.false)
  | some `Gabbro.Grammatik.Expr.lt => rel ``LT.lt
  | some `Gabbro.Grammatik.Expr.le => rel ``LE.le
  | some `Gabbro.Grammatik.Expr.eq => do
      let x ← tInt s0 s a[n-2]! ρ
      let y ← tInt s0 s a[n-1]! ρ
      mkDecide (← mkEq x y)
  | some `Gabbro.Grammatik.Expr.and => do
      pure (mkApp2 (mkConst ``and) (← tBool s0 s a[n-2]! ρ) (← tBool s0 s a[n-1]! ρ))
  | some `Gabbro.Grammatik.Expr.or => do
      pure (mkApp2 (mkConst ``or) (← tBool s0 s a[n-2]! ρ) (← tBool s0 s a[n-1]! ρ))
  | some `Gabbro.Grammatik.Expr.not => do pure (mkApp (mkConst ``not) (← tBool s0 s a[n-1]! ρ))
  -- a quantifier over a table of fixed size: one conjunct (disjunct) per index
  | some `Gabbro.Grammatik.Expr.forallSlots => quantor true a[n-3]! a[n-2]!
  | some `Gabbro.Grammatik.Expr.existsSlots => quantor false a[n-3]! a[n-2]!
  | _ => mkAppM `Gabbro.Grammatik.eval #[s0, e, s, ρ]
where
  quantor (alle : Bool) (t body : Lean.Expr) : StateRefT (Array Lean.Expr) MetaM Lean.Expr := do
    let wty ← kw (← inferType s)
    unless wty.isAppOfArity `Gabbro.Grammatik.World 1 do throwError "gabbrov_arith: no world"
    let d := wty.getArg! 0
    let idx ← kernNormal (← mkAppM `Gabbro.Grammatik.alleIndizes #[mkApp2 (mkConst `Gabbro.Grammatik.Deklaration.count) d t])
    let some ks := idx.listLit? | throwError "gabbrov_arith: the indices are not a list"
    let mut acc := mkConst (if alle then ``Bool.true else ``Bool.false)
    for k in ks.2.reverse do
      let b ← tBool s0 s body (← mkAppM `Gabbro.Grammatik.Env.cons #[k, ρ])
      acc := mkApp2 (mkConst (if alle then ``and else ``or)) b acc
    return acc

/-- The Boolean a term `wahr? (eval σ₀ e σ ρ)` (or `eval σ₀ e σ ρ`) stands for, if it is one. -/
meta def tBedingung? (b : Lean.Expr) : StateRefT (Array Lean.Expr) MetaM (Option Lean.Expr) := do
  let b := b.headBeta
  let b := if b.isAppOf `Gabbro.Grammatik.wahr? then b.appArg!.headBeta else b
  unless b.isAppOf `Gabbro.Grammatik.eval && b.getAppNumArgs ≥ 4 do return none
  let a := b.getAppArgs
  let n := a.size
  try
    let t ← tBool a[n-4]! a[n-2]! a[n-3]! a[n-1]!
    return some t
  catch _ => return none

/-- A condition `c = true` / `c = false` / `¬ c = true` over a lowered expression, translated:
    the new proposition and whether the kernel accepts it as the old one. -/
meta partial def tAussage? (p : Lean.Expr) : StateRefT (Array Lean.Expr) MetaM (Option Lean.Expr) := do
  let p ← instantiateMVars p
  -- an implication between conditions (a callee's contract): both sides translated
  if p.isForall && !p.bindingBody!.hasLooseBVars && !(p.isAppOfArity ``Not 1) then
    let a := p.bindingDomain!
    let b := p.bindingBody!
    let a' := (← tAussage? a).getD a
    let b' := (← tAussage? b).getD b
    if a' == a && b' == b then return none
    let p' ← mkArrow a' b'
    match Kernel.isDefEq (← getEnv) (← getLCtx) p p' with
    | .ok true => return some p'
    | _ => return none
  let (neg, q) := if p.isAppOfArity ``Not 1 then (true, p.appArg!) else (false, p)
  let some (_, l, r) := q.eq? | return none
  let some t ← tBedingung? l | return none
  let q' := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) t r
  let p' := if neg then mkNot q' else q'
  match Kernel.isDefEq (← getEnv) (← getLCtx) p p' with
  | .ok true => return some p'
  | _ => return none

/-- **Translate the conditions over symbolic values into integer arithmetic and try `omega`.** -/
syntax (name := gabbrovArith) "gabbrov_arith" : tactic

/-- A contract proposition `ReqAmEintritt P f σ ρ` or `EnsAmRueck P f s σ ρ v` with `P`'s precondition or
    postcondition replaced by that of `f`'s own lowering (`requires_eq`, `ensures_eq`): the new proposition
    and the equation `t = t'`. -/
meta def vertragOffen? (hlow t : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let n := t.getAppNumArgs
  let (satz, pos) ←
    if t.isAppOf ``Gabbro.Grammatik.ReqAmEintritt && n ≥ 4 then pure (``Gabbro.Bruecke.requires_eq, 3)
    else if t.isAppOf ``Gabbro.Grammatik.EnsAmRueck && n ≥ 6 then pure (``Gabbro.Bruecke.ensures_eq, 5)
    else return none
  let f := t.getAppArgs[n - pos]!
  let some body ← delta? t | return none
  let some (_, lhs, _) := body.eq? | return none
  let ev := lhs.appArg!
  unless ev.isAppOf ``Gabbro.Grammatik.eval && ev.getAppNumArgs ≥ 4 do return none
  let X := ev.getAppArgs[ev.getAppNumArgs - 3]!
  let some eqX ← (try some <$> mkAppM satz #[hlow, f] catch _ => pure none) | return none
  let some (_, _, rhs) := (← inferType eqX).eq? | return none
  let motivRumpf := body.replace fun e => if e == X then some (mkBVar 0) else none
  let motiv := mkLambda `r .default (← inferType X) motivRumpf
  return some ((mkApp motiv rhs).headBeta, ← mkCongrArg motiv eqX)

/-- Every contract hypothesis (`ReqAmEintritt`, `EnsAmRueck`, and an implication between them, as the
    callee's contract `hvertrag`) read at the functions' own lowering, as a further hypothesis. -/
meta def reqLesen (goal : MVarId) : MetaM MVarId := goal.withContext do
  let some hlow ← findeLow? | return goal
  let mut g := goal
  for d in ← getLCtx do
    if LocalDecl.isImplementationDetail d then continue
    let ty ← instantiateMVars (LocalDecl.type d)
    if let some (neu, eq) ← vertragOffen? hlow ty then
      g ← g.assert `hreq neu (← mkEqMP eq d.toExpr)
      let (_, g') ← g.intro1
      g := g'
    else if ty.isForall && !ty.bindingBody!.hasLooseBVars then
      let a := ty.bindingDomain!
      let b := ty.bindingBody!
      let oa ← vertragOffen? hlow a
      let ob ← vertragOffen? hlow b
      if oa.isNone && ob.isNone then continue
      let a' := (oa.map (·.1)).getD a
      let b' := (ob.map (·.1)).getD b
      let pf ← withLocalDeclD `x a' fun x => do
        let arg ← match oa with
          | some (_, eqA) => mkEqMPR eqA x
          | none => pure x
        let res := mkApp d.toExpr arg
        let res ← match ob with
          | some (_, eqB) => mkEqMP eqB res
          | none => pure res
        mkLambdaFVars #[x] res
      g ← g.assert `hvertrag' (← mkArrow a' b') pf
      let (_, g') ← g.intro1
      g := g'
  return g

@[tactic gabbrovArith] meta def evalGabbrovArith : Tactic := fun _ => withMainContext do
  replaceMainGoal [← reqLesen (← getMainGoal)]
  withMainContext do
  let goal ← getMainGoal
  let (r, atome) ← (do
    let mut goal := goal
    let mut namen : Array Name := #[]
    -- the hypotheses
    let lctx ← getLCtx
    for d in lctx do
      if LocalDecl.isImplementationDetail d then continue
      if let some p' ← tAussage? (LocalDecl.type d) then
        goal ← goal.replaceLocalDeclDefEq d.fvarId p'
        let nm := Name.mkSimple s!"hw{namen.size}"
        goal ← goal.rename d.fvarId nm
        namen := namen.push nm
    -- the goal
    let zielNeu ← goal.withContext do tAussage? (← goal.getType)
    if let some p' := zielNeu then goal ← goal.replaceTargetDefEq p'
    return (goal, namen, zielNeu.isSome)).run #[]
  let (goal, namen, imZiel) := r
  replaceMainGoal [goal]
  if namen.isEmpty && !imZiel then throwError "gabbrov_arith: no condition over a lowered expression"
  -- the declared ranges of the atoms
  withMainContext do
    let mut g ← getMainGoal
    for v in atome do
      let ty ← kw (← inferType v)
      let lo := ty.getArg! 0
      let hi := ty.getArg! 1
      let n := mkAppN (mkConst `Gabbro.Grammatik.Zahl.n) #[lo, hi, v]
      if let some l ← intWert? lo then
        g ← g.assert `hlo (← mkAppM ``LE.le #[toExpr l, n]) (mkProj `Gabbro.Grammatik.Zahl 1 v)
      if let some h ← intWert? hi then
        g ← g.assert `hhi (← mkAppM ``LE.le #[n, toExpr h]) (mkProj `Gabbro.Grammatik.Zahl 2 v)
    replaceMainGoal [g]
  for _ in atome do
    evalTactic (← `(tactic| intro))
    evalTactic (← `(tactic| intro))
  for nm in namen do
    evalTactic (← `(tactic| try simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
      true_implies, implies_true]
      at $(mkIdent nm):ident))
  if imZiel then
    evalTactic (← `(tactic| try simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
      true_implies, implies_true]))
  -- the language's division and remainder round towards zero (`tdiv`/`tmod`); on non-negative operands
  -- they are `omega`'s `/`/`%`
  for nm in namen do
    evalTactic (← `(tactic| try simp (disch := omega) only [Int.tmod_eq_emod_of_nonneg, Int.tdiv_eq_ediv_of_nonneg]
      at $(mkIdent nm):ident))
  if imZiel then
    evalTactic (← `(tactic| try simp (disch := omega) only [Int.tmod_eq_emod_of_nonneg, Int.tdiv_eq_ediv_of_nonneg]))
  evalTactic (← `(tactic| first | omega | (exfalso; omega) | skip))

end Gabbro.Bruecke
