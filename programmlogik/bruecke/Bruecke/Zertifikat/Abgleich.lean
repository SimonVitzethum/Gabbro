module
public import Bruecke.Zertifikat.Satz
public import Bruecke.Zertifikat.Programm
public import Bruecke.Zertifikat.Regeln
public import Bruecke.Zertifikat.Aufrufe
public import Bruecke.Zertifikat.Schleifen
public import Bruecke.Zertifikat.Formen
public meta import Lean.Elab.Tactic
@[expose] public section

/-!
# Proof support: the kernel's normal form, the rule table and syntactic matching

`kernNormal` computes normal forms by the kernel's reduction; `wpRegel?` names the model's exact rule
for the outermost constructor of a goal; `passe`/`wendeAn` apply a rule by syntactic first-order
matching. None of this is trusted: every proof built with it is checked by the kernel.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.WP
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

open Lean Meta in
/-- The normal form of `e` computed by the KERNEL's reduction (fast where the elaborator's is slow):
    weak head normal form, then the same in every explicit argument of a constructor that is neither a
    proof nor a type. Implicit arguments, types and proofs are kept as they are. -/
meta partial def kernNormal (e : Lean.Expr) : MetaM Lean.Expr := do
  let e' ← match Kernel.whnf (← getEnv) (← getLCtx) (← instantiateMVars e) with
    | .ok r => pure r
    | .error err => do
      logInfo m!"gabbrov: kernel whnf failed: {err.toMessageData (← getOptions)}"
      pure e
  let f := e'.getAppFn
  match f with
  | .const n _ =>
    match (← getEnv).find? n with
    | some (.ctorInfo _) =>
      let args := e'.getAppArgs
      let info ← getFunInfoNArgs f args.size
      let mut args' := args
      for i in [:args.size] do
        if h : i < info.paramInfo.size then
          if info.paramInfo[i].isExplicit then
            let a := args[i]!
            unless (← isProof a) || (← isType a) do
              args' := args'.set! i (← kernNormal a)
      return mkAppN f args'
    | _ => return e'
  | _ => return e'

open Lean in
/-- The rule of the model for the outermost constructor of the body in a `wpEA`/`wpBA`/`wpSA` goal. -/
meta def wpRegel? (t0 : Lean.Expr) : Option Name :=
  let t := t0.headBeta.cleanupAnnotations
  let args := t.getAppArgs.map (·.headBeta.cleanupAnnotations)
  if args.size < 5 then none else
  -- the index of a value `⟨⟨k, h⟩, _⟩` or `⟨k, h⟩` as a literal, if it is one
  let index? (w : Lean.Expr) : Option Nat :=
    let fin := if w.isAppOfArity ``Sigma.mk 4 then w.getArg! 2 else w
    if fin.isAppOfArity ``Fin.mk 3 then
      let k := fin.getArg! 1
      k.rawNatLit? <|> k.nat? <|>
        (if k.isAppOfArity ``Nat.succ 1 then some 1 else none)
    else none
  match t.getAppFn.constName?, args[args.size - 5]!.getAppFn.constName?, index? args[args.size - 4]! with
  | some ``Gabbro.Bruecke.wpArmsA, some ``Gabbro.Grammatik.Arms.cons, some 0 => some ``Gabbro.Bruecke.wpArmsA_null
  | some ``Gabbro.Bruecke.wpArmsA, some ``Gabbro.Grammatik.Arms.cons, some (_ + 1) => some ``Gabbro.Bruecke.wpArmsA_succ
  | some ``Gabbro.Bruecke.wpGrundA, some ``Gabbro.Grammatik.GrundArms.cons, some 0 => some ``Gabbro.Bruecke.wpGrundA_null
  | some ``Gabbro.Bruecke.wpGrundA, some ``Gabbro.Grammatik.GrundArms.cons, some (_ + 1) => some ``Gabbro.Bruecke.wpGrundA_succ
  | _, _, _ =>
  if t.isAppOf ``Gabbro.Bruecke.wpRetryA then
    match args[args.size - 4]!.rawNatLit? with
    | some 0 => some ``Gabbro.Bruecke.wpRetryA_null
    | some _ => some ``Gabbro.Bruecke.wpRetryA_succ
    | none => none
  else
  match t.getAppFn.constName?, args[args.size - 1]!.getAppFn.constName? with
  | some ``Gabbro.Grammatik.WP.RueckPost, some ``Gabbro.Grammatik.EndAusgang.zurueck => some ``Gabbro.Bruecke.rueckPost_zurueck
  | some ``Gabbro.Grammatik.WP.RueckPost, some ``Gabbro.Grammatik.EndAusgang.why => some ``Gabbro.Bruecke.rueckPost_why
  | some ``Gabbro.Grammatik.WP.RueckPost, some ``Gabbro.Grammatik.EndAusgang.logik => some ``Gabbro.Bruecke.rueckPost_logik
  | some ``Gabbro.Grammatik.WP.RueckPost, some ``Gabbro.Grammatik.EndAusgang.hardware => some ``Gabbro.Bruecke.rueckPost_hardware
  | _, _ =>
  match t.getAppFn.constName?, args[args.size - 4]!.getAppFn.constName? with
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.ret => some ``Gabbro.Grammatik.WP.wpEA_ret
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.cons => some ``Gabbro.Grammatik.WP.wpEA_cons
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.bind => some ``Gabbro.Grammatik.WP.wpEA_bind
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.cons => some ``Gabbro.Grammatik.WP.wpBA_cons
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.bind => some ``Gabbro.Grammatik.WP.wpBA_bind
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.nil => some ``Gabbro.Grammatik.WP.wpBA_nil
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.narrow => some ``Gabbro.Grammatik.WP.wpBA_narrow
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.check => some ``Gabbro.Grammatik.WP.wpBA_check
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.ite => some ``Gabbro.Grammatik.WP.wpSA_ite
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.ret => some ``Gabbro.Grammatik.WP.wpSA_ret
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.locks => some ``Gabbro.Grammatik.WP.wpSA_locks
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.call => some ``Gabbro.Grammatik.WP.wpSA_call
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.onTag => some ``Gabbro.Bruecke.wpSA_onTag
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.onWhy => some ``Gabbro.Bruecke.wpSA_onWhy
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.onOption => some ``Gabbro.Bruecke.wpSA_onOption
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.bindCall => some ``Gabbro.Grammatik.WP.wpBA_bindCall
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.breaking => some ``Gabbro.Bruecke.wpSA_breaking
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.retry => some ``Gabbro.Bruecke.wpSA_retry_lauf
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.retScoped => some ``Gabbro.Bruecke.wpSA_retScoped
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.retWhyScoped => some ``Gabbro.Bruecke.wpSA_retWhyScoped
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.retScoped => some ``Gabbro.Bruecke.wpEA_retScoped
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.retWhyScoped => some ``Gabbro.Bruecke.wpEA_retWhyScoped
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.exchange => some ``Gabbro.Bruecke.wpEA_exchange
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.exchange => some ``Gabbro.Bruecke.wpBA_exchange
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.bindAxiomElse => some ``Gabbro.Bruecke.wpEA_bindAxiomElse
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.bindAxiomElse => some ``Gabbro.Bruecke.wpBA_bindAxiomElse
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.bindCallInd => some ``Gabbro.Bruecke.wpEA_bindCallInd
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.awaits => some ``Gabbro.Bruecke.wpEA_awaits
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.awaits => some ``Gabbro.Bruecke.wpBA_awaits
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.axiomCall => some ``Gabbro.Bruecke.wpSA_axiomCall
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.bindAxiom => some ``Gabbro.Bruecke.wpBA_bindAxiom
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.bindAxiom => some ``Gabbro.Bruecke.wpEA_bindAxiom
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.narrowRequired => some ``Gabbro.Bruecke.wpBA_narrowRequired
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.narrow => some ``Gabbro.Bruecke.wpEA_narrow
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.narrowRequired => some ``Gabbro.Bruecke.wpEA_narrowRequired
  | some ``Gabbro.Grammatik.WP.wpSA, some ``Gabbro.Grammatik.Stmt.traverse => some ``Gabbro.Bruecke.wpSA_traverse_lauf
  | some ``Gabbro.Bruecke.wpTravA, some ``List.nil => some ``Gabbro.Bruecke.wpTravA_nil
  | some ``Gabbro.Bruecke.wpTravA, some ``List.cons => some ``Gabbro.Bruecke.wpTravA_cons
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.bindCall => some ``Gabbro.Bruecke.wpEA_bindCall
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.bindCallElse => some ``Gabbro.Bruecke.wpEA_bindCallElse
  | some ``Gabbro.Grammatik.WP.wpBA, some ``Gabbro.Grammatik.Block.bindCallElse => some ``Gabbro.Bruecke.wpBA_bindCallElse
  | some ``Gabbro.Grammatik.WP.wpEA, some ``Gabbro.Grammatik.Endblock.ite => some ``Gabbro.Bruecke.wpEA_ite
  | _, _ => none

open Lean Meta in
/-- Syntactic first-order matching of a rule's pattern against a goal: a metavariable of the pattern
    takes the goal's subterm as it is; every other node must agree. No definitional unfolding: the
    kernel checks the assembled proof. -/
meta partial def passe (p e : Lean.Expr) : MetaM Bool := do
  let p ← instantiateMVars p
  -- a closed subterm: equal as it is, or by the kernel's definitional equality (fast where the
  -- elaborator's is slow: index terms in two normal forms)
  if !p.hasMVar && !e.hasMVar then
    if p == e then return true
    match Kernel.isDefEq (← getEnv) (← getLCtx) p e with
    | .ok b => return b
    | .error _ => return false
  match p, e with
  | .mvar m, _ =>
    if ← m.isAssigned then passe (← instantiateMVars p) e
    else m.assign e; return true
  | .app (.app (.app (.app (.app (.app (.const ``HAdd.hAdd _) _) _) _) _) a) b, _ =>
    -- `?i + 1` against a numeral `n + 1`
    let zahl? (x : Lean.Expr) : Option Nat :=
      x.nat? <|> x.rawNatLit? <|>
        (if x.isAppOfArity ``Nat.succ 1 then (x.getArg! 0).nat?.map (· + 1) <|> (x.getArg! 0).rawNatLit?.map (· + 1) else none)
    match zahl? b, zahl? e with
    | some 1, some (n + 1) => passe a (mkNatLit n)
    | _, _ =>
      match e with
      | .app (.app (.app (.app (.app (.app (.const ``HAdd.hAdd _) _) _) _) _) a') b' =>
        return (← passe a a') && (← passe b b')
      | _ =>
        -- a number the kernel computes (`D.gruende f`): its normal form, then again
        match Kernel.whnf (← getEnv) (← getLCtx) e with
        | .ok e' => if e' == e then return false else passe p e'
        | .error _ => return false
  | .mdata _ p', _ => passe p' e
  | _, .mdata _ e' => passe p e'
  | .app _ _, _ =>
    let pf := p.getAppFn
    let ef := e.getAppFn
    let gleich := match pf, ef with
      | .const n _, .const m _ => n == m && p.getAppNumArgs == e.getAppNumArgs
      | .mvar _, _ => false
      | _, _ => false
    if gleich then
      unless ← passe pf ef do return false
      for (x, y) in p.getAppArgs.zip e.getAppArgs do
        unless ← passe x y do return false
      return true
    else
      -- different heads: the goal's side in the kernel's weak head normal form, then again
      match Kernel.whnf (← getEnv) (← getLCtx) e with
      | .ok e' => if e' == e then return false else passe p e'
      | .error _ => return false
  | .const n ls, .const m ms =>
    if n != m || ls.length != ms.length then return false
    for (x, y) in ls.zip ms do
      unless ← isLevelDefEq x y do return false
    return true
  | .sort u, .sort v => isLevelDefEq u v
  | .proj s i a, .proj t j b => if s == t && i == j then passe a b else return false
  | _, _ => return p == e

open Lean Meta in
/-- Apply the equivalence `regel` (`lhs ↔ rhs`) backwards to the goal by syntactic matching; the
    new goal is the instantiated `rhs`. -/
meta def wendeAn (goal : MVarId) (regel : Name) : MetaM MVarId := do
  let c ← mkConstWithFreshMVarLevels regel
  let (xs, _, typ) ← forallMetaTelescopeReducing (← inferType c)
  let some (lhs, rhs) := typ.iff? | throwError "gabbrov: {regel} is not an equivalence"
  unless ← passe lhs (← instantiateMVars (← goal.getType)) do
    throwError "gabbrov: {regel} does not match the goal"
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  let h ← instantiateMVars (mkAppN c xs)
  if rhs.hasExprMVar || h.hasExprMVar then throwError "gabbrov: {regel} leaves arguments open"
  let neu ← mkFreshExprSyntheticOpaqueMVar rhs (← goal.getTag)
  goal.assign (mkApp4 (mkConst ``Iff.mpr) lhs rhs h neu)
  return neu.mvarId!

end Gabbro.Bruecke
