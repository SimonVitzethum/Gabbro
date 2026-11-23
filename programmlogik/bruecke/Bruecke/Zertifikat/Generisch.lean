module
public import Bruecke.Zertifikat.Teilen
public meta import Lean.Elab.Tactic
@[expose] public section

/-!
# Proof support for every form: one step of the semantics, generic splits, refolding

A form without its own rule is executed by the semantics' own equation lemmas (`execStmtHA`,
`execBlockHA`, `execEndHA`): `entfalten?` rewrites one execution step by the equation the
definition generates (the proof is that equation, checked by the kernel). What the step leaves is a
`match` on a value; `matchTeilen?` splits a symbolic discriminant into its constructors (`Option`,
`Bool`, `Sum`, a pair, a subtype, a callee's outcome, a case number, a tagged value) and reduces the
`match` once the discriminant is a constructor; `zurueckfalten?` reads a remaining execution of a
sub-block as its weakest precondition again. No form needs a rule of its own; a rule only makes a
step faster or the residual more readable.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.WP
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

theorem opt_faelle {α : Type} {G : Option α → Prop} (x : Option α)
    (hs : ∀ v, x = some v → G (some v)) (hn : x = none → G none) : G x := by
  cases x with
  | none => exact hn rfl
  | some v => exact hs v rfl

theorem bool_faelle {G : Bool → Prop} (x : Bool) (ht : x = true → G true) (hf : x = false → G false) : G x := by
  cases x with
  | true => exact ht rfl
  | false => exact hf rfl

theorem summe2_faelle {α β : Type} {G : α ⊕ β → Prop} (x : α ⊕ β)
    (hl : ∀ a, x = .inl a → G (.inl a)) (hr : ∀ b, x = .inr b → G (.inr b)) : G x := by
  cases x with
  | inl a => exact hl a rfl
  | inr b => exact hr b rfl

theorem subtype_faelle {α : Type} {p : α → Prop} {G : Subtype p → Prop} (x : Subtype p)
    (h : ∀ a (ha : p a), x = ⟨a, ha⟩ → G ⟨a, ha⟩) : G x := by
  cases x with
  | mk a ha => exact h a ha rfl

open Lean Meta in
/-- The executions and their weakest preconditions. -/
meta def execNamen : List (Lean.Name × Lean.Name) :=
  [(``Gabbro.Grammatik.execStmtHA, ``Gabbro.Grammatik.WP.wpSA),
   (``Gabbro.Grammatik.execBlockHA, ``Gabbro.Grammatik.WP.wpBA),
   (``Gabbro.Grammatik.execEndHA, ``Gabbro.Grammatik.WP.wpEA)]

open Lean Meta in
/-- **One step of the semantics**: `wpX … s Q σ ρ` is `Q (execX … s σ ρ)`; the execution is
    rewritten by the equation lemma of `execX` for the constructor of `s`. -/
meta def entfalten? (goal : MVarId) (t : Lean.Expr) : MetaM (Option MVarId) := do
  let some (ex, _) := execNamen.find? (fun (_, w) => t.isAppOf w) | return none
  let some e ← delta? t | return none
  unless e.isApp do return none
  let Q := e.appFn!
  let x := e.appArg!
  let some eqns ← getEqnsFor? ex | return none
  -- the constructor of the form: only the equation for that constructor is tried (a mismatch would
  -- otherwise send the matcher into the kernel's reduction of the whole execution)
  let xa := x.getAppArgs
  let istForm (e : Lean.Expr) : Bool := e.getAppFn.constName?.any fun c =>
    c.getPrefix == ``Gabbro.Grammatik.Stmt || c.getPrefix == ``Gabbro.Grammatik.Block ||
    c.getPrefix == ``Gabbro.Grammatik.Endblock
  let some pos := xa.findIdx? istForm | return none
  let form := xa[pos]!.getAppFn.constName?
  for eqn in eqns do
    let c ← mkConstWithFreshMVarLevels eqn
    let (ms, _, typ) ← forallMetaTelescopeReducing (← inferType c)
    let some (_, lhs, rhs) := typ.eq? | continue
    let la := lhs.getAppArgs
    unless la.size == xa.size && (la[pos]!.getAppFn.constName? == form) do continue
    let ok ← try passe lhs x catch _ => pure false
    unless ok do continue
    let rhs ← instantiateMVars rhs
    let pf ← instantiateMVars (mkAppN c ms)
    if rhs.hasExprMVar || pf.hasExprMVar then continue
    let rhs' ← zetaReduce rhs
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp Q rhs').headBeta (← goal.getTag)
    goal.assign (← mkEqMPR (← mkCongrArg Q pf) g')
    return some g'.mvarId!
  return none

open Lean Meta in
/-- A value whose type a split lemma covers. -/
meta def teilbar (ty : Lean.Expr) : MetaM Bool := do
  let ty ← whnf ty
  return ty.isAppOf ``Option || ty.isConstOf ``Bool || ty.isAppOf ``Sum || ty.isAppOf ``Prod ||
    ty.isAppOf ``Subtype || ty.isAppOf ``Gabbro.Grammatik.RufAusgang || ty.isAppOf ``Fin ||
    ty.isAppOf ``Sigma

open Lean Meta in
/-- The first part of a discriminant that is not yet a constructor (inside constructors too). -/
meta partial def ersteOffene (d : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if let some c := d.getAppFn.constName? then
    if let some (.ctorInfo ci) := (← getEnv).find? c then
      for a in d.getAppArgs[ci.numParams:] do
        if let some o ← ersteOffene a then return some o
      return none
  if d.hasLooseBVars then return none
  if (← teilbar (← inferType d)) then return some d
  return none

open Lean Meta in
/-- Split `x` (all its occurrences in the goal) by the lemma for its type. -/
meta def wertTeilen (goal : MVarId) (x : Lean.Expr) : MetaM (Option (List MVarId)) := do
  -- the gated call: read at the callee's own precondition first (`torRuf_von`)
  if x.isAppOf ``Gabbro.Grammatik.torRuf && x.getAppNumArgs ≥ 6 then
    let xa := x.getAppArgs
    let some hlow ← findeLow? | return none
    let _ := hlow
    let some hreq ← vertragsGleichung? xa[3]! false | return none
    let eq ← mkAppM ``Gabbro.Bruecke.torRuf_gleich #[hreq, xa[2]!, xa[4]!, xa[5]!]
    let some (_, _, rhs) := (← inferType eq).eq? | return none
    let (G, _) ← motivVon goal x
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp G rhs).headBeta (← goal.getTag)
    goal.assign (← mkEqMPR (← mkCongrArg G eq) g')
    return some [g'.mvarId!]
  let ty ← whnf (← inferType x)
  -- a split must change the goal: the value occurs in it as it is
  let (G0, _) ← motivVon goal x
  unless G0.bindingBody!.hasLooseBVars do return none
  if ty.isAppOf ``Fin then return some (← finTeilen goal x)
  if ty.isAppOf ``Sigma then return some (← summeTeilen goal x)
  let (G, _) ← motivVon goal x
  if ty.isAppOf ``Prod then
    let a := ty.getArg! 0
    let b := ty.getArg! 1
    let la := ((← getLevel a).dec).getD Level.zero
    let lb := ((← getLevel b).dec).getD Level.zero
    let paar := mkApp4 (mkConst ``Prod.mk [la, lb]) a b (mkProj ``Prod 0 x) (mkProj ``Prod 1 x)
    return some [← goal.replaceTargetDefEq (mkApp G paar).headBeta]
  let (satz, args, n) :=
    if ty.isAppOf ``Option then (``Gabbro.Bruecke.opt_faelle, #[ty.getArg! 0], 2)
    else if ty.isConstOf ``Bool then (``Gabbro.Bruecke.bool_faelle, #[], 2)
    else if ty.isAppOf ``Sum then (``Gabbro.Bruecke.summe2_faelle, #[ty.getArg! 0, ty.getArg! 1], 2)
    else if ty.isAppOf ``Subtype then (``Gabbro.Bruecke.subtype_faelle, #[ty.getArg! 0, ty.getArg! 1], 1)
    else (``Gabbro.Bruecke.ruf_faelle, ty.getAppArgs, 4)
  let pf0 := mkAppN (mkConst satz) (args ++ #[G, x])
  let (ms, _, _) ← forallMetaTelescopeReducing (← inferType pf0) (some n)
  goal.assign (mkAppN pf0 ms)
  let mut out := []
  for m in ms do
    m.mvarId!.setKind .syntheticOpaque
    let (_, m') ← m.mvarId!.intros
    out := out ++ [← m'.withContext do m'.replaceTargetDefEq (← instantiateMVars (← m'.getType)).headBeta]
  return some out

open Lean Meta in
/-- **A `match` in the goal**: reduce it where its discriminants are constructors; otherwise split the
    first part that is not. -/
meta def matchTeilen? (goal : MVarId) : MetaM (Option (List MVarId)) := do
  let t ← instantiateMVars (← goal.getType)
  let env ← getEnv
  let some m := t.find? fun e => !e.hasLooseBVars &&
      (match e.getAppFn.constName? with
       | some n => isMatcherCore env n
       | none => false)
    | return none
  let some app ← matchMatcherApp? m | return none
  -- a discriminant the kernel computes to a constructor is computed, not split
  for d in app.discrs do
    if d.hasLooseBVars then continue
    let istCtor (x : Lean.Expr) : MetaM Bool := do
      match x.getAppFn.constName? with
      | some c => return ((← getEnv).find? c).any (·.isCtor)
      | none => return false
    unless ← istCtor d do
      if let .ok d' := Kernel.whnf (← getEnv) (← getLCtx) d then
        if ← istCtor d' then
          let (G, _) ← motivVon goal d
          return some [← goal.replaceTargetDefEq (mkApp G d').headBeta]
  for d in app.discrs do
    if let some o ← ersteOffene d then
      return ← wertTeilen goal o
  -- every discriminant is a constructor: reduce the match
  let m' ← whnfCore m
  if m' == m then return none
  let (G, _) ← motivVon goal m
  return some [← goal.replaceTargetDefEq (mkApp G m').headBeta]

open Lean Meta in
/-- **Refold**: an execution of a sub-block left in the goal is read as its weakest precondition. -/
meta def zurueckfalten? (goal : MVarId) : MetaM (Option MVarId) := do
  let t ← instantiateMVars (← goal.getType)
  let some x := t.find? fun e => !e.hasLooseBVars && execNamen.any (fun (ex, _) => e.isAppOf ex)
    | return none
  let some (ex, wp) := execNamen.find? (fun (ex, _) => x.isAppOf ex) | return none
  let info ← getFunInfo (← mkConstWithFreshMVarLevels ex)
  let xa := x.getAppArgs
  let expl := (xa.zipIdx.filter fun (_, i) => i < info.paramInfo.size && info.paramInfo[i]!.isExplicit).map (·.1)
  unless expl.size == 9 do return none
  let (G, _) ← motivVon goal x
  let w ← mkAppM wp (expl[0:7].toArray ++ #[G] ++ expl[7:9].toArray)
  return some (← goal.replaceTargetDefEq w)

open Lean Meta in
/-- The helper definitions of the semantics that only dispatch (indirect calls, outcome shapes): unfolded
    once, so their `match` and their continuations show. -/
meta def hilfsNamen : List Lean.Name :=
  [``Gabbro.Grammatik.indSonst, ``Gabbro.Grammatik.indSonstE, ``Gabbro.Grammatik.EndAusgang.weiterOpt,
   ``Gabbro.Grammatik.Ausgang.weiterOpt]

open Lean Meta in
/-- **Unfold a helper** of `hilfsNamen` occurring in the goal (not under a binder). -/
meta def hilfeEntfalten? (goal : MVarId) : MetaM (Option MVarId) := do
  let t ← instantiateMVars (← goal.getType)
  let some x := t.find? fun e => !e.hasLooseBVars && hilfsNamen.any (e.isAppOf ·) | return none
  let some x' ← delta? x | return none
  let x' ← zetaReduce (← whnfCore x'.headBeta)
  if x' == x then return none
  let (G, _) ← motivVon goal x
  return some (← goal.replaceTargetDefEq (mkApp G x').headBeta)

end Gabbro.Bruecke
