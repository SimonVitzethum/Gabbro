module
public import Bruecke.Zertifikat.Satz
public import Bruecke.Zertifikat.Programm
public import Bruecke.Zertifikat.Regeln
public meta import Lean.Elab.Tactic
@[expose] public section

/-!
# Proof support for the duties: opening a function's duty, the weakest-precondition rules

`pflicht_oeffnen` opens the duty `ZielF u f` of one function at its own lowering: the program's body and
postcondition of `f` are those of `lowerFnAt u f` (`programm_von`), so a proof works on the
function's lowered body `v.2.1` and postcondition `v.1`. The tactic `gabbrov_wp` applies the exact
weakest-precondition rules of the model (`Logik/WP/HA/Kern.lean`) to the body: sequences, bindings,
branches, returns, `locks`, `narrow`, checks. Every rule is an equivalence, so no case is lost;
what remains are the logical conditions of the program.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.WP
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.Parser.Cover.Differenz

/-- **Open the duty of one function at its own lowering.** -/
theorem pflicht_oeffnen {u : UProg} {f : Fin u.fns.length}
    (h : ∀ (P : Programm (declOf u)) (v : EnsTy u f × RumpTy u f × ReqTy u f), lowerFnAt u f = .ok v →
      P.ensures f = v.1 → P.rumpf f = v.2.1 →
      ∀ (Q : AxEns (declOf u)) (sp : Speicher (declOf u)) (main : (declOf u).Fn)
        (args : Env (declOf u) ((declOf u).params main))
        (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
        (checks : List (CheckDecl (declOf u))),
        LogikFn (Gabbro.Stage0.OldSource.einheitDer u P Q sp main args roots gestartet checks) f) :
    ZielF u f := fun P fs hlow Q sp main args roots gestartet checks => by
  obtain ⟨v, hv, he, hb, _⟩ := programm_von hlow f
  exact h P v hv he hb Q sp main args roots gestartet checks

/-- The three duties of a function from one statement per duty over its lowered body. -/
theorem logikFn_aus {D : Deklaration} [DecidableEq D.Fn] {E : Einheit D} {f : D.Fn}
    (h1 : ∀ passes, PflichtRueck E.P passes E.Q E.S (GeteiltA E.P E.ws) f)
    (h2 : ∀ passes, PflichtKeineVor E.P passes E.Q E.S (GeteiltA E.P E.ws) f)
    (h3 : ∀ passes, PflichtKeinHalt E.P passes E.Q E.S (GeteiltA E.P E.ws) f) : LogikFn E f :=
  fun passes => ⟨h1 passes, h2 passes, h3 passes⟩

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
meta def wpRegel? (t : Lean.Expr) : Option Name :=
  let args := t.getAppArgs
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
      | _ => return false
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

/-- One step: the rule of the outermost constructor of the body (`wpRegel?`), applied by its
    equivalence. Fails when no rule applies. -/
syntax (name := gabbrovSchritt) "gabbrov_schritt" : tactic

open Lean Elab Tactic Meta in
@[tactic gabbrovSchritt] meta def evalGabbrovSchritt : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  -- a match's arms at a value: put the value into the kernel's normal form, so that its index shows
  let (goal, t) ← do
    let args := t.getAppArgs
    if (t.isAppOf ``Gabbro.Bruecke.wpArmsA || t.isAppOf ``Gabbro.Bruecke.wpGrundA) && args.size ≥ 4 then
      let w' ← kernNormal args[args.size - 4]!
      let t' := mkAppN t.getAppFn (args.set! (args.size - 4) w')
      pure (← goal.replaceTargetDefEq t', t')
    else pure (goal, t)
  match wpRegel? t with
  | some regel => replaceMainGoal [← wendeAn goal regel]
  | none =>
    -- a branch whose condition the kernel decides: its weak head normal form is the branch taken
    if t.isAppOf ``ite || t.isAppOf ``dite then
      match Kernel.whnf (← getEnv) (← getLCtx) t with
      | .ok t' =>
        if t'.isAppOf ``ite || t'.isAppOf ``dite || t' == t then
          throwError "gabbrov_schritt: the condition is not decided"
        replaceMainGoal [← goal.replaceTargetDefEq t']
      | .error _ => throwError "gabbrov_schritt: the condition is not decided"
    else throwError "gabbrov_schritt: no rule for this goal"


/-- Close an equation `a = b` that the kernel's definitional equality decides (fast where the
    elaborator's is slow); the proof is `Eq.refl a`, checked by the kernel. -/
syntax (name := gabbrovRfl) "gabbrov_rfl" : tactic

open Lean Elab Tactic Meta in
@[tactic gabbrovRfl] meta def evalGabbrovRfl : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, a, b) := t.eq? | throwError "gabbrov_rfl: not an equation"
  match Kernel.isDefEq (← getEnv) (← getLCtx) a b with
  | .ok true =>
    goal.assign (← mkExpectedTypeHint (← mkEqRefl a) t)
    replaceMainGoal []
  | _ => throwError "gabbrov_rfl: the kernel does not decide the equation"

/-- Apply the exact weakest-precondition rules of the model, outermost first, as long as one applies,
    and reduce the continuations `weiterEA`/`weiterBA` at a known outcome: symbolic execution of a
    lowered body in constructor form by the model's own rules. Every rule is an equivalence, so the
    remaining goals say exactly what the program owes. -/
macro "gabbrov_wp" : tactic => `(tactic| repeat (first
  | gabbrov_schritt
  | (simp only [Gabbro.Grammatik.WP.weiterEA, Gabbro.Grammatik.WP.weiterBA])))

/-- **Compute a term and put its normal form into the goal**: `gabbrov_senke t` reduces `t` (all
    definitions unfolded, proofs and types kept) and rewrites `t` to the result. The rewrite is `rfl`, checked
    by the kernel, so nothing is trusted: typically `t` is a function's lowered body
    `(lowerAtPair u f w).2.1`, which then stands in constructor form for `gabbrov_wp`. A module that uses it
    on source names needs the string definitions (`import all Init.Data.String.*`, as the generated proof
    files have). -/
syntax (name := gabbrovSenke) "gabbrov_senke " term : tactic

open Lean Elab Tactic Meta in
@[tactic gabbrovSenke] meta def evalGabbrovSenke : Tactic := fun stx => withMainContext do
  let e ← elabTerm stx[1] none
  let e' ← kernNormal e
  let goal ← getMainGoal
  let eq ← mkEq e e'
  let prf ← mkExpectedTypeHint (← mkEqRefl e) eq
  let r ← goal.rewrite (← goal.getType) prf
  let g' ← goal.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g' :: r.mvarIds)


#print axioms pflicht_oeffnen

end Gabbro.Bruecke
