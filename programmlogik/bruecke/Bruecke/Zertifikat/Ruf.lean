module
public import Bruecke.Zertifikat.Abgleich
@[expose] public section

/-!
# Proof support: straight statements and calls

`gerade?` executes a statement with one outcome by the kernel's reduction of `execStmtHA`;
`rufSchritt?` reads a call: the gated call at the callee's precondition, a branch decided or split,
the handler's outcome split into its four cases.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.WP
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

/-- The statements whose execution is one outcome without a case split and without a sub-block:
    their weakest precondition is the postcondition at that outcome, read off `execStmtHA` by the
    kernel. -/
meta def geradeStmts : List Lean.Name :=
  [``Gabbro.Grammatik.Stmt.assignVar, ``Gabbro.Grammatik.Stmt.assignSlot, ``Gabbro.Grammatik.Stmt.assignThru,
   ``Gabbro.Grammatik.Stmt.assignThruOwn, ``Gabbro.Grammatik.Stmt.assignSlotRef, ``Gabbro.Grammatik.Stmt.assignGlob,
   ``Gabbro.Grammatik.Stmt.putBytes, ``Gabbro.Grammatik.Stmt.publish, ``Gabbro.Grammatik.Stmt.advances,
   ``Gabbro.Grammatik.Stmt.retires, ``Gabbro.Grammatik.Stmt.regWrite, ``Gabbro.Grammatik.Stmt.transition,
   ``Gabbro.Grammatik.Stmt.retWhy, ``Gabbro.Grammatik.Stmt.leave, ``Gabbro.Grammatik.Stmt.next]

/-- The end blocks that end in one outcome without a case split. -/
meta def geradeEnden : List Lean.Name :=
  [``Gabbro.Grammatik.Endblock.retWhy, ``Gabbro.Grammatik.Endblock.leave, ``Gabbro.Grammatik.Endblock.next]

open Lean Meta in
/-- A straight statement (`geradeStmts`): `wpSA s Q σ ρ` is by definition `Q (execStmtHA s σ ρ)`;
    the execution is put into the kernel's weak head normal form, which must be an outcome. -/
meta def gerade? (goal : MVarId) (t : Lean.Expr) : MetaM (Option MVarId) := do
  unless (t.isAppOf ``Gabbro.Grammatik.WP.wpSA || t.isAppOf ``Gabbro.Grammatik.WP.wpEA) && t.getAppNumArgs ≥ 4 do
    return none
  let args := t.getAppArgs
  let some k := args[args.size - 4]!.getAppFn.constName? | return none
  unless geradeStmts.contains k || geradeEnden.contains k do return none
  let some e ← delta? t | return none
  unless e.isApp do return none
  match Kernel.whnf (← getEnv) (← getLCtx) e.appArg! with
  | .ok x =>
    unless x.getAppFn.constName?.any (fun c => c.getPrefix == ``Gabbro.Grammatik.Ausgang ||
        c.getPrefix == ``Gabbro.Grammatik.EndAusgang) do return none
    return some (← goal.replaceTargetDefEq (mkApp e.appFn! x).headBeta)
  | .error _ => return none

open Lean Meta in
/-- The callee's outcome a goal depends on, with the goal as a function of it: the last argument of
    the goal, or the outcome inside a last argument `rufZuAusgang hr ρ out`. -/
meta def rufStelle? (t : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let t := t.headBeta
  let args := t.getAppArgs
  if args.isEmpty then return none
  let last := args.back!
  let heads := [``Gabbro.Bruecke.bindRufEA, ``Gabbro.Grammatik.WP.bindRufBA, ``Gabbro.Bruecke.bindRufSonstEA,
    ``Gabbro.Bruecke.bindRufSonstBA, ``Gabbro.Bruecke.retryWeiter, ``Gabbro.Bruecke.travWeiter,
    ``Gabbro.Bruecke.axRufSA, ``Gabbro.Bruecke.axBindBA, ``Gabbro.Bruecke.axBindEA,
    ``Gabbro.Bruecke.axSonstEA, ``Gabbro.Bruecke.axSonstBA, ``Gabbro.Bruecke.indRufEA, ``Gabbro.Bruecke.indZielEA]
  let (x, bau) : Lean.Expr × (Lean.Expr → Lean.Expr) ←
    if heads.any t.isAppOf then pure (last, fun y => mkAppN t.getAppFn (args.set! (args.size - 1) y))
    else if last.isAppOf ``Gabbro.Grammatik.WP.rufZuAusgang && last.getAppNumArgs ≥ 1 then
      let largs := last.getAppArgs
      pure (largs.back!, fun y => mkAppN t.getAppFn
        (args.set! (args.size - 1) (mkAppN last.getAppFn (largs.set! (largs.size - 1) y))))
    else return none
  let ty ← inferType x
  let G ← withLocalDeclD `aus ty fun y => mkLambdaFVars #[y] (bau y)
  return some (G, x)

open Lean Meta in
/-- A hypothesis whose type has the head `n` (and whose last argument is `R`, when given). -/
meta def findeHyp? (n : Lean.Name) (R? : Option Lean.Expr := none) : MetaM (Option Lean.Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf n then
      match R? with
      | some R => if ty.getAppArgs.back? == some R then return some d.toExpr
      | none => return some d.toExpr
  return none

open Lean Meta in
/-- After a call `R g σ ρ = .ok σ' v` (`hruf`): the hypothesis
    `hvertrag : ReqAmEintritt P g σ ρ → EnsAmRueck P g σ σ' ρ v` from the certificate's
    `RespektiertRahmen P R`. Without that hypothesis in context the goal stays as it is. -/
meta def vertragsHyp (goal : MVarId) (R x hruf σ' v : Lean.Expr) : MetaM MVarId := goal.withContext do
  let some hRR ← findeHyp? ``Gabbro.Grammatik.RespektiertRahmen (some R) | return goal
  let ty ← instantiateMVars (← inferType hRR)
  let P := ty.getAppArgs[ty.getAppNumArgs - 2]!
  let xa := x.getAppArgs
  let g := xa[0]!
  let σ := xa[1]!
  let ρ := xa[2]!
  let req ← mkAppM ``Gabbro.Grammatik.ReqAmEintritt #[P, g, σ, ρ]
  let ens ← mkAppM ``Gabbro.Grammatik.EnsAmRueck #[P, g, σ, σ', ρ, v]
  let hty ← mkArrow req ens
  let pf ← withLocalDeclD `hq req fun hq => do
    mkLambdaFVars #[hq] (mkAppN (mkProj ``And 0 hRR) #[g, σ, ρ, hq, σ', v, hruf])
  let g' ← goal.assert `hvertrag hty pf
  let (_, g'') ← g'.intro1P
  return g''

open Lean Meta in
/-- The hypothesis `lowerAllg u = .ok (P, fs)` of the opened duty. -/
meta def findeLow? : MetaM (Option Lean.Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, l, _) := ty.eq? then
      if l.isAppOf ``Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg then return some d.toExpr
  return none

open Lean Meta in
/-- **A call**: the gated call is read at the callee's own precondition (`torRuf_von`), a branch the
    kernel decides is taken, an undecided branch is split (`ite_faelle`), and the handler's outcome is
    split into its four cases (`ruf_faelle`). A `why` of a callee without reasons is impossible, a
    `logik` of a handler without `logik` outcomes too. -/
meta def rufSchritt? (goal : MVarId) (t : Lean.Expr) : MetaM (Option (List MVarId)) := do
  let some (G, x) ← rufStelle? t | return none
  let x := x.headBeta
  -- the value of a function pointer: its normal form shows the callee
  let x ← if t.headBeta.isAppOf ``Gabbro.Bruecke.indZielEA then
      match Kernel.whnf (← getEnv) (← getLCtx) x with
      | .ok x' => pure x'
      | .error _ => pure x
    else pure x
  if t.headBeta.isAppOf ``Gabbro.Bruecke.indZielEA && x.getAppFn.constName?.any (fun c =>
      c == ``Subtype.mk || c == ``Sigma.mk || c == ``PSigma.mk) then
    let some t' ← delta? (mkApp G x).headBeta | return none
    return some [← goal.replaceTargetDefEq (← whnfCore t'.headBeta)]
  -- a known outcome: read the continuation off its definition (delta, then the match)
  let antwortBekannt := x.isAppOfArity ``Prod.mk 4 &&
    ((x.getArg! 3).isAppOf ``Option.some || (x.getArg! 3).isAppOf ``Option.none)
  if antwortBekannt || x.getAppFn.constName?.any (fun c => c.getPrefix == ``Gabbro.Grammatik.RufAusgang ||
      c.getPrefix == ``Gabbro.Grammatik.Ausgang || c.getPrefix == ``Gabbro.Grammatik.EndAusgang) then
    let t := t.headBeta
    let heads := [``Gabbro.Bruecke.bindRufEA, ``Gabbro.Grammatik.WP.bindRufBA, ``Gabbro.Bruecke.bindRufSonstEA,
      ``Gabbro.Bruecke.bindRufSonstBA, ``Gabbro.Bruecke.retryWeiter, ``Gabbro.Bruecke.travWeiter,
    ``Gabbro.Bruecke.axRufSA, ``Gabbro.Bruecke.axBindBA, ``Gabbro.Bruecke.axBindEA,
    ``Gabbro.Bruecke.axSonstEA, ``Gabbro.Bruecke.axSonstBA, ``Gabbro.Bruecke.indRufEA, ``Gabbro.Bruecke.indZielEA]
    if heads.any t.isAppOf then
      let some t' ← delta? t | return none
      return some [← goal.replaceTargetDefEq (← whnfCore t'.headBeta)]
    else
      let args := t.getAppArgs
      let some l' ← delta? args.back! | return none
      return some [← goal.replaceTargetDefEq (mkAppN t.getAppFn (args.set! (args.size - 1) (← whnfCore l'.headBeta)))]
  let neu (ty : Lean.Expr) : MetaM Lean.Expr := do
    mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (ty.headBeta)) (← goal.getTag)
  -- the gated call: its precondition from the function's own lowering
  if x.isAppOf ``Gabbro.Grammatik.torRuf && x.getAppNumArgs ≥ 6 then
    let xa := x.getAppArgs
    let some hlow ← findeLow? | return none
    let eq ← mkAppM ``Gabbro.Bruecke.torRuf_von #[hlow, xa[2]!, xa[3]!, xa[4]!, xa[5]!]
    let some (_, _, rhs) := (← inferType eq).eq? | return none
    let g' ← neu (mkApp G rhs)
    goal.assign (← mkEqMPR (← mkCongrArg G eq) g')
    return some [g'.mvarId!]
  -- a branch: taken when the kernel decides it, split otherwise
  if x.isAppOfArity ``ite 5 then
    let xa := x.getAppArgs
    let b? : Option Bool ← match Kernel.whnf (← getEnv) (← getLCtx) xa[2]! with
      | .ok inst =>
        if inst.isAppOf ``Decidable.isTrue then pure (some true)
        else if inst.isAppOf ``Decidable.isFalse then pure (some false)
        else if inst.isAppOf ``Decidable.intro && inst.getAppNumArgs ≥ 2 then
          match Kernel.whnf (← getEnv) (← getLCtx) (inst.getArg! 1) with
          | .ok b => pure (if b.isConstOf ``Bool.true then some true
              else if b.isConstOf ``Bool.false then some false else none)
          | .error _ => pure none
        else pure none
      | .error _ => pure none
    match b? with
    | some true => return some [← goal.replaceTargetDefEq (mkApp G xa[3]!).headBeta]
    | some false => return some [← goal.replaceTargetDefEq (mkApp G xa[4]!).headBeta]
    | none =>
      let u ← getLevel xa[0]!
      let pf0 := mkAppN (mkConst ``Gabbro.Bruecke.ite_faelle [u]) #[xa[0]!, G, xa[1]!, xa[2]!, xa[3]!, xa[4]!]
      let (ms, _, _) ← forallMetaTelescopeReducing (← inferType pf0) (some 2)
      goal.assign (mkAppN pf0 ms)
      let mut out := []
      for m in ms do
        m.mvarId!.setKind .syntheticOpaque
        let (_, m') ← m.mvarId!.intro `hbed
        out := out ++ [m']
      return some out
  -- the answer of a fallible foreign call
  if x.isAppOf ``Gabbro.Grammatik.axiomAntwortSonst then
    let ty ← whnfR (← inferType x)
    unless ty.isAppOfArity ``Prod 2 do return none
    let wty ← whnfR (ty.getArg! 0)
    let oty ← whnfR (ty.getArg! 1)
    unless wty.isAppOfArity ``Gabbro.Grammatik.World 1 && oty.isAppOfArity ``Option 1 do return none
    let sty ← whnfR (oty.getArg! 0)
    unless sty.isAppOfArity ``Sum 2 do return none
    let pf0 := mkAppN (mkConst ``Gabbro.Bruecke.antwortSonst_faelle)
      #[wty.getArg! 0, sty.getArg! 0, sty.getArg! 1, G, x]
    let (ms, _, _) ← forallMetaTelescopeReducing (← inferType pf0) (some 3)
    goal.assign (mkAppN pf0 ms)
    let mut out := []
    for (m, k) in ms.toList.zip [0, 1, 2] do
      m.mvarId!.setKind .syntheticOpaque
      let namen := if k == 0 then [`σ', `v, `hax] else if k == 1 then [`σ', `r, `hax] else [`σ', `hax]
      let (_, m') ← m.mvarId!.introN namen.length namen
      out := out ++ [m']
    return some out
  -- the oracle's answer to a foreign call
  if x.isAppOf ``Gabbro.Grammatik.axiomAntwort then
    let ty ← whnfR (← inferType x)
    unless ty.isAppOfArity ``Prod 2 do return none
    let wty ← whnfR (ty.getArg! 0)
    let oty ← whnfR (ty.getArg! 1)
    unless wty.isAppOfArity ``Gabbro.Grammatik.World 1 && oty.isAppOfArity ``Option 1 do return none
    let pf0 := mkAppN (mkConst ``Gabbro.Bruecke.antwort_faelle) #[wty.getArg! 0, oty.getArg! 0, G, x]
    let (ms, _, _) ← forallMetaTelescopeReducing (← inferType pf0) (some 2)
    goal.assign (mkAppN pf0 ms)
    let mut out := []
    for (m, k) in ms.toList.zip [0, 1] do
      m.mvarId!.setKind .syntheticOpaque
      let namen := if k == 0 then [`σ', `v, `hax] else [`σ', `hax]
      let (_, m') ← m.mvarId!.introN namen.length namen
      out := out ++ [m']
    return some out
  -- the handler's outcome
  if x.getAppFn.isFVar && x.getAppNumArgs == 3 then
    let ty ← whnfR (← inferType x)
    unless ty.isAppOf ``Gabbro.Grammatik.RufAusgang do return none
    let ta := ty.getAppArgs
    let pf0 := mkAppN (mkConst ``Gabbro.Bruecke.ruf_faelle) #[ta[0]!, ta[1]!, G, x]
    let (ms, _, _) ← forallMetaTelescopeReducing (← inferType pf0) (some 4)
    goal.assign (mkAppN pf0 ms)
    let R := x.getAppFn
    let mut out := []
    for (m, k) in ms.toList.zip [0, 1, 2, 3] do
      m.mvarId!.setKind .syntheticOpaque
      let namen := if k < 2 then [`σ', (if k == 0 then `v else `r), `hruf] else [`e, `hruf]
      let (fs, m') ← m.mvarId!.introN namen.length namen
      let zu ← m'.withContext do
        -- a reason of a callee without reasons: impossible
        if k == 1 then
          let r := mkFVar fs[1]!
          let rty ← whnfR (← inferType r)
          if rty.isAppOfArity ``Fin 1 then
            if let .ok n := Kernel.whnf (← getEnv) (← getLCtx) (rty.getArg! 0) then
              if n.rawNatLit? == some 0 || n.nat? == some 0 || n.isConstOf ``Nat.zero then
                let gty ← m'.getType
                m'.assign (mkApp2 (mkConst ``Fin.elim0 [Level.zero]) gty r)
                return true
        -- a `logik` outcome of a handler without `logik` outcomes: impossible
        if k == 2 then
          if let some hR ← findeHyp? ``Gabbro.Grammatik.OhneLogik (some R) then
            m'.assign (← mkAppOptM ``Gabbro.Bruecke.logik_ohne
              #[none, none, hR, none, none, none, none, mkFVar fs[1]!, (← m'.getType)])
            return true
        return false
      if zu then continue
      -- an answer: the callee's contract as a hypothesis (`RespektiertVertraege`, part of the certificate's
      -- `RespektiertRahmen`): where its precondition held, its postcondition holds of the result
      let m' ← if k == 0 then vertragsHyp m' R x (mkFVar fs[2]!) (mkFVar fs[0]!) (mkFVar fs[1]!) else pure m'
      out := out ++ [m']
    return some out
  return none

end Gabbro.Bruecke
