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
/-- Take the branch `b` of the `ite`/`dite` with arguments `xa` under the proof `pc` of its condition (or of
    its negation), by the equation `if_pos`/`if_neg` (`dif_pos`/`dif_neg`), never by a definitional
    replacement: the kernel would compare `ite c t e` with `t` by unfolding the higher of the two first,
    which is the branch, i.e. the rest of the program. -/
meta def nimmZweig (goal : MVarId) (xa : Array Lean.Expr) (abh b : Bool) (pc : Lean.Expr) :
    MetaM (List MVarId) := do
  let zweig := if b then xa[3]! else xa[4]!
  let u ← getLevel xa[0]!
  let regel := match abh, b with
    | true, true => ``dif_pos | true, false => ``dif_neg
    | false, true => ``if_pos | false, false => ``if_neg
  let gl := mkAppN (mkConst regel [u]) #[xa[1]!, xa[2]!, pc, xa[0]!, xa[3]!, xa[4]!]
  let neu := if abh then (mkApp zweig pc).headBeta else zweig
  return [← goal.replaceTargetEq neu gl]

open Lean Meta in
/-- The key of a condition `b = r` over a lowered expression: its integer translation (`tBedingung?`)
    with every read replaced by the kernel's head normal form of the read, and `r`. A value written once
    is the same term wherever a later state reads it, so a condition on an unchanged value has the same key
    in every later state. -/
meta def bedingungsSchluessel? (c : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let some (_, l, r) := c.eq? | return none
  let some t ← (tBedingung? l).run' #[] | return none
  let t ← Meta.transform t (post := fun e => do
    if e.isAppOfArity `Gabbro.Grammatik.Zahl.n 3 then
      let v ← kw (e.getArg! 2)
      if v.isAppOfArity `Gabbro.Grammatik.Zahl.mk 5 then return .done (v.getArg! 2)
      return .done (mkApp3 e.getAppFn (e.getArg! 0) (e.getArg! 1) v)
    return .continue)
  return some (t, r)

open Lean Meta in
/-- **A condition an earlier branch already settled**: a branch hypothesis (`hbed`) states the condition
    `c` or its negation, syntactically or with the same key (`bedingungsSchluessel?`) and accepted by the
    kernel as the same proposition. Returns which branch and the hypothesis. -/
meta def ausBedingung? (goal : MVarId) (c : Lean.Expr) : MetaM (Option (Bool × Lean.Expr)) :=
  goal.withContext do
    let mut kandidaten := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail || d.userName.eraseMacroScopes != `hbed then continue
      let ty ← instantiateMVars d.type
      if ty == c then return some (true, d.toExpr)
      if ty.not? == some c then return some (false, d.toExpr)
      kandidaten := kandidaten.push (d.toExpr, ty)
    if kandidaten.isEmpty then return none
    let some k ← bedingungsSchluessel? c | return none
    for (h, ty) in kandidaten do
      let (neg, q) := match ty.not? with | some q => (true, q) | none => (false, ty)
      let some k' ← bedingungsSchluessel? q | continue
      unless k' == k do continue
      match Kernel.isDefEq (← getEnv) (← getLCtx) q c with
      | .ok true => return some (!neg, h)
      | _ => continue
    return none

open Lean Meta in
/-- **A branch** `ite`/`dite` at the top of a goal: taken when the kernel decides its condition (a
    `dite` branch gets the proof `of_decide_eq_true rfl`, checked by the kernel), otherwise split into
    both branches, each under its condition (`ite_faelle`, `dite_faelle`). -/
meta def verzweigung (goal : MVarId) (t : Lean.Expr) : MetaM (List MVarId) := do
  let xa := t.getAppArgs
  let abh := t.isAppOf ``dite
  match ← entschieden? xa[2]! with
  | some b =>
    let rT ← mkEqRefl (mkConst ``Bool.true)
    let rF ← mkEqRefl (mkConst ``Bool.false)
    let pc := if b then mkApp3 (mkConst ``of_decide_eq_true) xa[1]! xa[2]! rT
      else mkApp3 (mkConst ``of_decide_eq_false) xa[1]! xa[2]! rF
    nimmZweig goal xa abh b pc
  | none =>
    if let some (b, pc) ← ausBedingung? goal xa[1]! then
      return ← nimmZweig goal xa abh b pc
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
  let abh := x.isAppOf ``dite
  -- the branch under the proof `pc` of its condition (or its negation), by the equation of `nimmZweig`
  -- carried through the goal (`congrArg`), never by a definitional replacement
  let nimm (b : Bool) (pc : Lean.Expr) : MetaM (List MVarId) := do
    let zweig := if b then xa[3]! else xa[4]!
    let u ← getLevel xa[0]!
    let regel := match abh, b with
      | true, true => ``dif_pos | true, false => ``dif_neg
      | false, true => ``if_pos | false, false => ``if_neg
    let gl := mkAppN (mkConst regel [u]) #[xa[1]!, xa[2]!, pc, xa[0]!, xa[3]!, xa[4]!]
    let neu := if abh then (mkApp zweig pc).headBeta else zweig
    return [← goal.replaceTargetEq (mkApp G neu).headBeta (← mkCongrArg G gl)]
  match ← entschieden? xa[2]! with
  | some b =>
    let rT ← mkEqRefl (mkConst ``Bool.true)
    let rF ← mkEqRefl (mkConst ``Bool.false)
    return some (← nimm b (if b then mkApp3 (mkConst ``of_decide_eq_true) xa[1]! xa[2]! rT
      else mkApp3 (mkConst ``of_decide_eq_false) xa[1]! xa[2]! rF))
  | none =>
    if let some (b, pc) ← ausBedingung? goal xa[1]! then
      return some (← nimm b pc)
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
