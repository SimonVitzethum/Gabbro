module
public import Bruecke.Zertifikat.Ruf
@[expose] public section

/-!
# Proof support: closing the return obligation

`gabbrov_fertig` closes what the language carries at a return: conjunctions, inequalities between
different outcomes, the caller-blame case, invariants when none are declared, and the
postcondition when the kernel decides it.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.WP
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

/-- **Close the return obligation** left by `gabbrov_wp`, without elaborator unification over the large
    terms (the kernel checks every step): conjunctions are split; a return or reason exit is not a logic
    stop (`zurueck_ne_logik`, `why_ne_logik`); without declared invariants nothing is owed
    (`invAmRueck_leer`, the kernel decides `D.invs = []`); the return check is read over the function's
    own postcondition `hens : P.ensures f = e` (`ensAmRueck_von`) and closed when the kernel decides it.
    What is left is the program's logic. -/
syntax (name := gabbrovFertig) "gabbrov_fertig " term : tactic

open Lean Meta in
meta def fertigSchritt (hens : Lean.Expr) (goal : MVarId) : MetaM (Option (List MVarId)) := goal.withContext do
  let t := (← instantiateMVars (← goal.getType)).cleanupAnnotations
  let kern (a b : Lean.Expr) : MetaM Bool := do
    match Kernel.isDefEq (← getEnv) (← getLCtx) a b with
    | .ok r => pure r
    | .error _ => pure false
  -- True
  if t.isConstOf ``True then
    goal.assign (mkConst ``True.intro)
    return some []
  -- a ∧ b
  if t.isAppOfArity ``And 2 then
    let a ← mkFreshExprSyntheticOpaqueMVar (t.getArg! 0) (← goal.getTag)
    let b ← mkFreshExprSyntheticOpaqueMVar (t.getArg! 1) (← goal.getTag)
    goal.assign (mkApp4 (mkConst ``And.intro) (t.getArg! 0) (t.getArg! 1) a b)
    return some [a.mvarId!, b.mvarId!]
  -- ∀ x, …: introduce
  if t.isForall && !(t.isArrow && t.bindingBody!.isConstOf ``False) then
    let (_, g) ← goal.intro1
    return some [g]
  -- a ≠ b, a = b → False: an exit is not a logic stop
  let ne? : Option (Lean.Expr × Lean.Expr) :=
    if t.isAppOfArity ``Ne 3 then some (t.getArg! 1, t.getArg! 2)
    else if t.isAppOfArity ``Not 1 && (t.getArg! 0).isAppOfArity ``Eq 3 then
      some ((t.getArg! 0).getArg! 1, (t.getArg! 0).getArg! 2)
    else none
  if let some (a, b) := ne? then
    let a := a.cleanupAnnotations
    let b := b.cleanupAnnotations
    -- different constructors
    if let (some ca, some cb) := (a.getAppFn.constName?, b.getAppFn.constName?) then
      if ca != cb then
        if let some (.ctorInfo _) := (← getEnv).find? ca then
          if let some (.ctorInfo _) := (← getEnv).find? cb then
            let (h, g) ← goal.intro1
            g.withContext do
              g.assign (← mkNoConfusion (← g.getType) (mkFVar h))
            return some []
      -- the same constructor around different constructors (`.logik vorzustand ≠ .logik (vorbedingung g)`)
      if ca == cb && a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs ≥ 1 then
        let x := a.getAppArgs.back!
        let y := b.getAppArgs.back!
        if let (some cx, some cy) := (x.getAppFn.constName?, y.getAppFn.constName?) then
          if cx != cy then
            if let some (.ctorInfo _) := (← getEnv).find? cx then
              if let some (.ctorInfo _) := (← getEnv).find? cy then
                -- `.logik x ≠ .logik y` from `x ≠ y` (different stops), by `logik_ne_logik`
                if ca == ``Gabbro.Grammatik.EndAusgang.logik && a.getAppNumArgs = 5 then
                  if (← try (do
                      let k ← withLocalDeclD `hxy (← mkEq x y) fun hxy => do
                        mkLambdaFVars #[hxy] (← mkNoConfusion (mkConst ``False) hxy)
                      let aa := a.getAppArgs
                      goal.assign (← mkAppOptM ``Gabbro.Bruecke.logik_ne_logik
                        #[aa[0]!, aa[1]!, aa[2]!, aa[3]!, x, y, k])
                      pure true) catch _ => pure false) then
                    return some []
      -- a `logik` outcome of a handler that never blames a caller is no precondition stop
      if ca == ``Gabbro.Grammatik.EndAusgang.logik && cb == ca && a.getAppNumArgs = 5 then
        let e := a.getArg! 4
        let b4 := b.getArg! 4
        if b4.isAppOf ``Gabbro.Grammatik.Logik.vorbedingung then
          for d in ← getLCtx do
            if d.isImplementationDetail then continue
            let ty ← instantiateMVars d.type
            if let some (_, l, r) := ty.eq? then
              if r.isAppOf ``Gabbro.Grammatik.RufAusgang.logik && r.getAppArgs.back? == some e && l.getAppFn.isFVar then
                if let some hR ← findeHyp? ``Gabbro.Grammatik.OhneVorbedingung (some l.getAppFn) then
                  let aa := a.getAppArgs
                  let pf ← mkAppOptM ``Gabbro.Bruecke.logik_nicht_vor
                    #[aa[0]!, aa[1]!, aa[2]!, aa[3]!, none, hR, none, none, none, none, d.toExpr]
                  goal.assign (mkApp pf b4.getAppArgs.back!)
                  return some []
    if b.isAppOf ``Gabbro.Grammatik.EndAusgang.logik && b.getAppNumArgs = 5 && a.getAppNumArgs = 6 then
      let satz? := if a.isAppOf ``Gabbro.Grammatik.EndAusgang.zurueck then some ``Gabbro.Bruecke.zurueck_ne_logik
        else if a.isAppOf ``Gabbro.Grammatik.EndAusgang.why then some ``Gabbro.Bruecke.why_ne_logik else none
      if let some l := satz? then
        goal.assign (mkAppN (mkConst l) (a.getAppArgs ++ #[b.getArg! 4]))
        return some []
  -- InvAmRueck without declared invariants
  if t.isAppOf ``Gabbro.Grammatik.InvAmRueck && t.getAppNumArgs = 4 then
    let d := t.getArg! 0
    let invs := mkApp (mkConst ``Gabbro.Grammatik.Deklaration.invs) d
    let ty ← inferType invs
    if ty.isAppOfArity ``List 1 then
      let nil := mkApp (mkConst ``List.nil [Level.zero]) (ty.getArg! 0)
      if ← kern invs nil then
        let h ← mkExpectedTypeHint (← mkEqRefl invs) (← mkEq invs nil)
        goal.assign (mkAppN (mkConst ``Gabbro.Bruecke.invAmRueck_leer) (t.getAppArgs ++ #[h]))
        return some []
  -- EnsAmRueck over the function's own postcondition
  if t.isAppOf ``Gabbro.Grammatik.EnsAmRueck && t.getAppNumArgs = 7 then
    let hty ← instantiateMVars (← inferType hens)
    if let some (_, lhs, e) := hty.eq? then
      let lhs := lhs.cleanupAnnotations
      if lhs.isAppOf ``Gabbro.Grammatik.Programm.ensures && lhs.getAppNumArgs = 3 then
        let args := t.getAppArgs
        let h := mkAppN (mkConst ``Gabbro.Bruecke.ensAmRueck_von)
          #[lhs.getArg! 0, lhs.getArg! 1, lhs.getArg! 2, e, hens, args[3]!, args[4]!, args[5]!, args[6]!]
        let some (_, rhs) := (← instantiateMVars (← inferType h)).iff? | return none
        if (← kern (rhs.getArg! 1) (rhs.getArg! 2)) then
          let prf ← mkExpectedTypeHint (← mkEqRefl (rhs.getArg! 1)) rhs
          goal.assign (mkApp4 (mkConst ``Iff.mpr) t rhs h prf)
          return some []
        let neu ← mkFreshExprSyntheticOpaqueMVar rhs (← goal.getTag)
        goal.assign (mkApp4 (mkConst ``Iff.mpr) t rhs h neu)
        return some [neu.mvarId!]
  return none

open Lean Elab Tactic Meta in
@[tactic gabbrovFertig] meta def evalGabbrovFertig : Tactic := fun stx => withMainContext do
  let hens ← elabTerm stx[1] none
  let mut offen := [← getMainGoal]
  let mut rest : List MVarId := []
  let mut fuel := 10000
  while !offen.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let g := offen.head!
    offen := offen.tail!
    match ← fertigSchritt hens g with
    | some gs => offen := gs ++ offen
    | none => rest := rest ++ [g]
  replaceMainGoal rest

end Gabbro.Bruecke
