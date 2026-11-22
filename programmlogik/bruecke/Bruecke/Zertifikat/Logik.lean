module
public import Bruecke.Zertifikat.WP
public meta import Lean.Elab.Command
@[expose] public section

/-!
# The program's logic, as a statement

`gabbrov_logik L : Z` runs `gabbrov_beweis` on the duty `Z` of one function and states what it leaves:
every remaining goal, closed over the variables and hypotheses it depends on, becomes one conjunct of
the definition `L : Prop` (`True` when nothing remains), and `L_genuegt : L → Z` is proved -- by the
automation's own proof, with each remaining goal taken from `L`, checked by the kernel. The user proves
`L`, the program's logic and nothing else.
-/

namespace Gabbro.Bruecke

open Lean Meta Elab Tactic Command

/-- The local variables and hypotheses a goal depends on: its free variables, those of their types, and
    every hypothesis about them (ranges, the precondition, branch conditions). -/
meta def abhaengige (t : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let lctx ← getLCtx
  let mut menge : FVarIdSet := (t |> Lean.collectFVars {} ).fvarSet
  -- close under the types of the variables
  let mut weiter := true
  while weiter do
    weiter := false
    for d in lctx do
      if menge.contains d.fvarId then
        for f in ((← instantiateMVars d.type) |> Lean.collectFVars {} ).fvarSet do
          unless menge.contains f do
            menge := menge.insert f
            weiter := true
  -- the hypotheses about them
  for d in lctx do
    if d.isImplementationDetail || menge.contains d.fvarId then continue
    let ty ← instantiateMVars d.type
    if ← isProp ty then
      let fs := (ty |> Lean.collectFVars {} ).fvarSet
      if !fs.isEmpty && fs.toList.all (menge.contains ·) then menge := menge.insert d.fvarId
  let mut out := #[]
  let mut gesehen : Array Lean.Expr := #[]
  for d in lctx do
    if !d.isImplementationDetail && menge.contains d.fvarId then
      let ty ← instantiateMVars d.type
      -- a hypothesis stated twice is kept once (its other copy is not used by the goal)
      if (← isProp ty) && !(t.containsFVar d.fvarId) && gesehen.contains ty then continue
      if ← isProp ty then gesehen := gesehen.push ty
      out := out.push d.toExpr
  return out

/-- The remaining goals of the automation on `ziel`, each closed over what it depends on. -/
meta def reste (g : MVarId) : TermElabM (List MVarId) := do
  Term.withoutErrToSorry do
    Tactic.run g (evalTactic (← `(tactic| gabbrov_beweis)))

meta def geschlossen (r : MVarId) : MetaM Lean.Expr := r.withContext do
  let t ← instantiateMVars (← r.getType)
  mkForallFVars (← abhaengige t) t

/-- `True`, or the conjunction of the statements. -/
meta def konjunktion : List Lean.Expr → Lean.Expr
  | [] => mkConst ``True
  | [p] => p
  | p :: ps => mkApp2 (mkConst ``And) p (konjunktion ps)

/-- The `i`-th conjunct of `h : konjunktion ps`. -/
meta def teil (h : Lean.Expr) : List Lean.Expr → Nat → Lean.Expr
  | [_], _ => h
  | p :: ps, 0 => mkApp3 (mkConst ``And.left) p (konjunktion ps) h
  | p :: ps, i + 1 => teil (mkApp3 (mkConst ``And.right) p (konjunktion ps) h) ps i
  | [], _ => h

syntax (name := gabbrovLogikCmd) "gabbrov_logik " ident " : " ident : command

@[command_elab gabbrovLogikCmd] meta def elabGabbrovLogik : CommandElab := fun stx => do
  let name := stx[1].getId
  let zielStx := stx[3]
  liftTermElabM do
    let ziel ← realizeGlobalConstNoOverloadWithInfo zielStx
    let ns ← getCurrNamespace
    let logikName := ns ++ name
    let zielTy := mkConst ziel
    -- first run: what remains
    let g1 ← mkFreshExprSyntheticOpaqueMVar zielTy
    let rs ← reste g1.mvarId!
    let props ← rs.mapM fun r => (geschlossen r : MetaM Lean.Expr)
    let logik := konjunktion props
    let dv : DefinitionVal := {
      name := logikName, levelParams := [], type := mkSort Level.zero, value := logik,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
    -- exported with its body: the user's proof file imports it and must see the statement
    withExporting (addDecl (Declaration.defnDecl dv))
    -- second run: the same automation, each remaining goal taken from the hypothesis
    let pf ← withLocalDeclD `h (mkConst logikName) fun h => do
      let g2 ← mkFreshExprSyntheticOpaqueMVar zielTy
      let rs2 ← reste g2.mvarId!
      unless rs2.length == props.length do
        throwError "gabbrov_logik: the automation left {rs2.length} goals, then {props.length}"
      for (r, i) in rs2.zipIdx do
        r.withContext do
          let t ← instantiateMVars (← r.getType)
          let deps ← abhaengige t
          r.assign (mkAppN (teil h props i) deps)
      mkLambdaFVars #[h] (← instantiateMVars g2)
    if pf.hasExprMVar then throwError "gabbrov_logik: the proof is not closed"
    let ty ← mkArrow (mkConst logikName) zielTy
    let tv : TheoremVal := { name := logikName ++ `genuegt, levelParams := [], type := ty, value := pf }
    addDecl (Declaration.thmDecl tv)
    let ax ← collectAxioms (logikName ++ `genuegt)
    logInfo m!"{logikName}: {props.length} statement(s) of the program's logic remain; axioms {ax.toList}"

end Gabbro.Bruecke
