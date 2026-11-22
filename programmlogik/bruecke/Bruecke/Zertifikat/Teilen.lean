module
public import Bruecke.Zertifikat.Wert
public meta import Lean.Elab.Tactic
@[expose] public section

/-!
# Proof support: branches and case splits

A branch whose condition the kernel decides is taken; otherwise it is split into both branches
under their conditions (`ite_faelle`, `dite_faelle`), also where the branch sits inside the goal
(`iteHeben`). A symbolic tagged value or reason is split into its finitely many cases
(`sigma_faelle`, `fin_faelle`). A lock release at a known outcome is read off `freiH`.
Every proof built here is checked by the kernel.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.WP
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

open Lean Meta in
/-- A branch the kernel does not decide: both branches, each under its condition (`ite_faelle`). -/
meta def iteTeilen (goal : MVarId) (t : Lean.Expr) : MetaM (List MVarId) := do
  let xa := t.getAppArgs
  let G ← withLocalDeclD `p xa[0]! fun p => mkLambdaFVars #[p] p
  let u ← getLevel xa[0]!
  let pf0 := mkAppN (mkConst ``Gabbro.Bruecke.ite_faelle [u]) #[xa[0]!, G, xa[1]!, xa[2]!, xa[3]!, xa[4]!]
  let (ms, _, _) ← forallMetaTelescopeReducing (← inferType pf0) (some 2)
  goal.assign (mkAppN pf0 ms)
  let mut out := []
  for m in ms do
    m.mvarId!.setKind .syntheticOpaque
    let (_, m') ← m.mvarId!.intro `hbed
    out := out ++ [← m'.replaceTargetDefEq (← instantiateMVars (← m'.getType)).headBeta]
  return out

open Lean Meta in
/-- The value of a `Decidable` instance, if the kernel computes it. -/
meta def entschieden? (inst : Lean.Expr) : MetaM (Option Bool) := do
  match Kernel.whnf (← getEnv) (← getLCtx) inst with
  | .ok i =>
    if i.isAppOf ``Decidable.isTrue then return some true
    if i.isAppOf ``Decidable.isFalse then return some false
    if i.isAppOf ``Decidable.intro && i.getAppNumArgs ≥ 2 then
      match Kernel.whnf (← getEnv) (← getLCtx) (i.getArg! 1) with
      | .ok b =>
        if b.isConstOf ``Bool.true then return some true
        if b.isConstOf ``Bool.false then return some false
        return none
      | .error _ => return none
    return none
  | .error _ => return none

open Lean Meta in
/-- **A branch** `ite`/`dite` at the top of a goal: taken when the kernel decides its condition (a
    `dite` branch gets the proof `of_decide_eq_true rfl`, checked by the kernel), otherwise split into
    both branches, each under its condition (`ite_faelle`, `dite_faelle`). -/
meta def verzweigung (goal : MVarId) (t : Lean.Expr) : MetaM (List MVarId) := do
  let xa := t.getAppArgs
  let abh := t.isAppOf ``dite
  match ← entschieden? xa[2]! with
  | some b =>
    let zweig := if b then xa[3]! else xa[4]!
    if abh then
      let rT ← mkEqRefl (mkConst ``Bool.true)
      let rF ← mkEqRefl (mkConst ``Bool.false)
      let pc := if b then mkApp3 (mkConst ``of_decide_eq_true) xa[1]! xa[2]! rT
        else mkApp3 (mkConst ``of_decide_eq_false) xa[1]! xa[2]! rF
      return [← goal.replaceTargetDefEq (mkApp zweig pc).headBeta]
    return [← goal.replaceTargetDefEq zweig]
  | none =>
    if abh then
      let G ← withLocalDeclD `p xa[0]! fun p => mkLambdaFVars #[p] p
      let u ← getLevel xa[0]!
      let pf0 := mkAppN (mkConst ``Gabbro.Bruecke.dite_faelle [u]) #[xa[0]!, G, xa[1]!, xa[2]!, xa[3]!, xa[4]!]
      let (ms, _, _) ← forallMetaTelescopeReducing (← inferType pf0) (some 2)
      goal.assign (mkAppN pf0 ms)
      let mut out := []
      for m in ms do
        m.mvarId!.setKind .syntheticOpaque
        let (_, m') ← m.mvarId!.intro `hbed
        out := out ++ [← m'.replaceTargetDefEq (← instantiateMVars (← m'.getType)).headBeta]
      return out
    iteTeilen goal t


open Lean Meta in
/-- The goal as a function of one of its subterms `x` (every occurrence, by the kernel-free keyed
    abstraction), and the subterm's type. -/
meta def motivVon (goal : MVarId) (x : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let t ← instantiateMVars (← goal.getType)
  let ty ← inferType x
  -- syntactic abstraction through a fresh local (no definitional unification over the goal)
  let G ← withLocalDeclD `y ty fun y => do
    mkLambdaFVars #[y] (t.replace fun e => if e == x then some y else none)
  return (G, ty)

open Lean Meta in
/-- **A branch inside the goal** (not under a binder): taken when the kernel decides it, split
    otherwise, with the goal as the function of the branch. -/
meta def iteHeben? (goal : MVarId) : MetaM (Option (List MVarId)) := do
  let t ← instantiateMVars (← goal.getType)
  let some x := t.find? fun e => (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) && !e.hasLooseBVars
    | return none
  if x == t then return none
  let (G, _) ← motivVon goal x
  let xa := x.getAppArgs
  match ← entschieden? xa[2]! with
  | some b =>
    let zweig := if b then xa[3]! else xa[4]!
    let zweig ← if x.isAppOf ``dite then do
        let rT ← mkEqRefl (mkConst ``Bool.true)
        let rF ← mkEqRefl (mkConst ``Bool.false)
        pure (mkApp zweig (if b then mkApp3 (mkConst ``of_decide_eq_true) xa[1]! xa[2]! rT
          else mkApp3 (mkConst ``of_decide_eq_false) xa[1]! xa[2]! rF)).headBeta
      else pure zweig
    return some [← goal.replaceTargetDefEq (mkApp G zweig).headBeta]
  | none =>
    let u ← getLevel xa[0]!
    let satz := if x.isAppOf ``dite then ``Gabbro.Bruecke.dite_faelle else ``Gabbro.Bruecke.ite_faelle
    let pf0 := mkAppN (mkConst satz [u]) #[xa[0]!, G, xa[1]!, xa[2]!, xa[3]!, xa[4]!]
    let (ms, _, _) ← forallMetaTelescopeReducing (← inferType pf0) (some 2)
    goal.assign (mkAppN pf0 ms)
    let mut out := []
    for m in ms do
      m.mvarId!.setKind .syntheticOpaque
      let (_, m') ← m.mvarId!.intro `hbed
      out := out ++ [← m'.replaceTargetDefEq (← instantiateMVars (← m'.getType)).headBeta]
    return some out

open Lean Meta in
/-- **Split a symbolic case number** `r : Fin m` (`m` a number) into its `m` values. -/
meta partial def finTeilen (goal : MVarId) (r : Lean.Expr) : MetaM (List MVarId) := do
  let ty ← kw (← inferType r)
  unless ty.isAppOfArity ``Fin 1 do throwError "gabbrov: not a case number"
  let m ← kw (ty.getArg! 0)
  let some k := m.rawNatLit? | throwError "gabbrov: the number of cases is not a number"
  let (G, _) ← motivVon goal r
  if k == 0 then
    goal.assign (mkApp2 (mkConst ``Fin.elim0 [Level.zero]) (← goal.getType) r)
    return []
  let pf0 := mkAppN (mkConst ``Gabbro.Bruecke.fin_faelle) #[mkRawNatLit (k - 1), G, r]
  let (ms, _, _) ← forallMetaTelescopeReducing (← inferType pf0) (some 2)
  goal.assign (mkAppN pf0 ms)
  ms[0]!.mvarId!.setKind .syntheticOpaque
  ms[1]!.mvarId!.setKind .syntheticOpaque
  let (_, g0) ← ms[0]!.mvarId!.intro `hfall
  let g0 ← g0.replaceTargetDefEq (← instantiateMVars (← g0.getType)).headBeta
  let (fs, g1) ← ms[1]!.mvarId!.introN 2 [`i, `hfall]
  let g1 ← g1.replaceTargetDefEq (← instantiateMVars (← g1.getType)).headBeta
  let rest ← g1.withContext (finTeilen g1 (mkFVar fs[0]!))
  return g0 :: rest

open Lean Meta in
/-- **Split a symbolic tagged value** `w : Σ i : Fin m, β i` into its `m` cases, each with its
    payload (`sum_faelle`); the goal is `G w`. -/
meta partial def summeTeilenMit (goal : MVarId) (G w β : Lean.Expr) (m : Nat) : MetaM (List MVarId) := do
  if m == 0 then
    let gty ← goal.getType
    let fall := mkProj ``Sigma 0 w
    goal.assign (mkApp2 (mkConst ``Fin.elim0 [Level.zero]) gty fall)
    return []
  let n := m - 1
  let pf0 := mkAppN (mkConst ``Gabbro.Bruecke.sum_faelle) #[mkRawNatLit n, β, G, w]
  let (ms, _, _) ← forallMetaTelescopeReducing (← inferType pf0) (some 2)
  goal.assign (mkAppN pf0 ms)
  ms[0]!.mvarId!.setKind .syntheticOpaque
  ms[1]!.mvarId!.setKind .syntheticOpaque
  let (_, g0) ← ms[0]!.mvarId!.introN 2 [`nutz, `hwert]
  let g0 ← g0.replaceTargetDefEq (← instantiateMVars (← g0.getType)).headBeta
  if n == 0 then
    let (fs, g1) ← ms[1]!.mvarId!.introN 1 [`i]
    g1.assign (mkApp2 (mkConst ``Fin.elim0 [Level.zero]) (← g1.getType) (mkFVar fs[0]!))
    return [g0]
  let (fs, g1) ← ms[1]!.mvarId!.introN 3 [`i, `nutz, `hwert]
  g1.withContext do
    let i := mkFVar fs[0]!
    let b := mkFVar fs[1]!
    let finN := mkApp (mkConst ``Fin) (mkRawNatLit n)
    let β' ← withLocalDeclD `j finN fun j => do
      mkLambdaFVars #[j] (mkApp β (mkApp2 (mkConst ``Fin.succ) (mkRawNatLit n) j)).headBeta
    let sty := mkApp2 (mkConst ``Sigma [Level.zero, Level.zero]) finN β'
    let G' ← withLocalDeclD `s sty fun s => do
      let fst := mkProj ``Sigma 0 s
      let snd := mkProj ``Sigma 1 s
      mkLambdaFVars #[s] (mkApp G (mkApp4 (mkConst ``Sigma.mk [Level.zero, Level.zero])
        (mkApp (mkConst ``Fin) (mkRawNatLit m)) β (mkApp2 (mkConst ``Fin.succ) (mkRawNatLit n) fst) snd))
    let w' := mkApp4 (mkConst ``Sigma.mk [Level.zero, Level.zero]) finN β' i b
    let g1 ← g1.replaceTargetDefEq (mkApp G' w')
    let rest ← summeTeilenMit g1 G' w' β' n
    return g0 :: rest

open Lean Meta in
/-- **Split a symbolic tagged value** of the goal into its cases. -/
meta def summeTeilen (goal : MVarId) (w : Lean.Expr) : MetaM (List MVarId) := do
  let ty ← whnf (← inferType w)
  unless ty.isAppOfArity ``Sigma 2 do throwError "gabbrov: not a tagged value"
  let fin ← whnf (ty.getArg! 0)
  unless fin.isAppOfArity ``Fin 1 do throwError "gabbrov: not a tagged value"
  let some m := (← kw (fin.getArg! 0)).rawNatLit? | throwError "gabbrov: the number of cases is not a number"
  let (G, _) ← motivVon goal w
  -- the type over the literal number of cases
  let β := ty.getArg! 1
  summeTeilenMit goal G w β m

open Lean Meta in
/-- **A lock release at a known outcome**: `freiH S L o` read off its definition. -/
meta def freiLesen? (goal : MVarId) : MetaM (Option MVarId) := do
  let t ← instantiateMVars (← goal.getType)
  let some x := t.find? fun e => e.isAppOf ``Gabbro.Grammatik.freiH && !e.hasLooseBVars &&
      e.getAppNumArgs ≥ 1 && (e.getAppArgs.back!.getAppFn.constName?.any
        (·.getPrefix == ``Gabbro.Grammatik.Ausgang))
    | return none
  let some x' ← delta? x | return none
  let x' ← whnfCore x'.headBeta
  let (G, _) ← motivVon goal x
  return some (← goal.replaceTargetDefEq (mkApp G x').headBeta)

end Gabbro.Bruecke
