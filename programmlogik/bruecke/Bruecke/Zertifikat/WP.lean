module
public import Bruecke.Zertifikat.Satz
public import Bruecke.Zertifikat.Programm
public import Bruecke.Zertifikat.Regeln
public import Bruecke.Zertifikat.Aufrufe
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
    (h : ∀ (P : Programm (declOf u)) (fs : List (declOf u).Fn), lowerAllg u = .ok (P, fs) →
      ∀ (v : EnsTy u f × RumpTy u f × ReqTy u f), lowerFnAt u f = .ok v →
      P.ensures f = v.1 → P.rumpf f = v.2.1 →
      ∀ (Q : AxEns (declOf u)) (sp : Speicher (declOf u)) (main : (declOf u).Fn)
        (args : Env (declOf u) ((declOf u).params main))
        (roots gestartet : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)))
        (checks : List (CheckDecl (declOf u))),
        LogikFn (Gabbro.Stage0.OldSource.einheitDer u P Q sp main args roots gestartet checks) f) :
    ZielF u f := fun P fs hlow Q sp main args roots gestartet checks => by
  obtain ⟨v, hv, he, hb, _⟩ := programm_von hlow f
  exact h P fs hlow v hv he hb Q sp main args roots gestartet checks

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

/-- The statements whose execution is one outcome without a case split and without a sub-block:
    their weakest precondition is the postcondition at that outcome, read off `execStmtHA` by the
    kernel. -/
meta def geradeStmts : List Lean.Name :=
  [``Gabbro.Grammatik.Stmt.assignVar, ``Gabbro.Grammatik.Stmt.assignSlot, ``Gabbro.Grammatik.Stmt.assignThru,
   ``Gabbro.Grammatik.Stmt.assignThruOwn, ``Gabbro.Grammatik.Stmt.assignSlotRef, ``Gabbro.Grammatik.Stmt.assignGlob,
   ``Gabbro.Grammatik.Stmt.putBytes, ``Gabbro.Grammatik.Stmt.publish, ``Gabbro.Grammatik.Stmt.advances,
   ``Gabbro.Grammatik.Stmt.retires, ``Gabbro.Grammatik.Stmt.regWrite, ``Gabbro.Grammatik.Stmt.transition,
   ``Gabbro.Grammatik.Stmt.retWhy, ``Gabbro.Grammatik.Stmt.leave, ``Gabbro.Grammatik.Stmt.next]

open Lean Meta in
/-- A straight statement (`geradeStmts`): `wpSA s Q σ ρ` is by definition `Q (execStmtHA s σ ρ)`;
    the execution is put into the kernel's weak head normal form, which must be an outcome. -/
meta def gerade? (goal : MVarId) (t : Lean.Expr) : MetaM (Option MVarId) := do
  unless t.isAppOf ``Gabbro.Grammatik.WP.wpSA && t.getAppNumArgs ≥ 4 do return none
  let args := t.getAppArgs
  let some k := args[args.size - 4]!.getAppFn.constName? | return none
  unless geradeStmts.contains k do return none
  let some e ← delta? t | return none
  let e := e.headBeta
  unless e.isApp do return none
  match Kernel.whnf (← getEnv) (← getLCtx) e.appArg! with
  | .ok x =>
    unless x.getAppFn.constName?.any (·.getPrefix == ``Gabbro.Grammatik.Ausgang) do return none
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
    ``Gabbro.Bruecke.bindRufSonstBA]
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
  -- a known outcome: read the continuation off its definition (delta, then the match)
  if x.getAppFn.constName?.any (·.getPrefix == ``Gabbro.Grammatik.RufAusgang) then
    let t := t.headBeta
    let heads := [``Gabbro.Bruecke.bindRufEA, ``Gabbro.Grammatik.WP.bindRufBA, ``Gabbro.Bruecke.bindRufSonstEA,
      ``Gabbro.Bruecke.bindRufSonstBA]
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
      out := out ++ [m']
    return some out
  return none

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
  if let some g ← gerade? goal t then replaceMainGoal [g] else
  if let some gs ← rufSchritt? goal t then replaceMainGoal gs else
  match wpRegel? t with
  | some regel => replaceMainGoal [← wendeAn goal regel]
  | none =>
    -- a branch whose condition the kernel decides: its weak head normal form is the branch taken
    if t.isAppOfArity ``ite 5 then
      -- decide the condition by its `Decidable` instance only; the goal becomes the branch taken
      match Kernel.whnf (← getEnv) (← getLCtx) (t.getArg! 2) with
      | .ok inst =>
        -- `Decidable` is a structure over its Boolean: read that Boolean
        let b? : Option Bool ←
          if inst.isAppOf ``Decidable.isTrue then pure (some true)
          else if inst.isAppOf ``Decidable.isFalse then pure (some false)
          else if inst.isAppOf ``Decidable.intro && inst.getAppNumArgs ≥ 2 then
            match Kernel.whnf (← getEnv) (← getLCtx) (inst.getArg! 1) with
            | .ok b => pure (if b.isConstOf ``Bool.true then some true
                else if b.isConstOf ``Bool.false then some false else none)
            | .error _ => pure none
          else pure none
        match b? with
        | some true => replaceMainGoal [← goal.replaceTargetDefEq (t.getArg! 3)]
        | some false => replaceMainGoal [← goal.replaceTargetDefEq (t.getArg! 4)]
        | none => throwError "gabbrov_schritt: the condition is not decided"
      | .error _ => throwError "gabbrov_schritt: the condition is not decided"
    else
      let t2 := t.headBeta.cleanupAnnotations
      throwError m!"gabbrov_schritt: no rule for this goal: {t2.getAppFn} / {t2.getAppNumArgs} / {(t2.getAppArgs.back?.map (·.getAppFn))}"


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

/-- Put the body of a `wpEA` goal into the kernel's normal form (as `gabbrov_senke` on that body). -/
syntax (name := gabbrovRumpf) "gabbrov_rumpf" : tactic

open Lean Elab Tactic Meta in
@[tactic gabbrovRumpf] meta def evalGabbrovRumpf : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  unless t.isAppOf ``Gabbro.Grammatik.WP.wpEA && t.getAppNumArgs ≥ 4 do
    throwError "gabbrov_rumpf: not a weakest-precondition goal of a body"
  let args := t.getAppArgs
  let b' ← kernNormal args[args.size - 4]!
  replaceMainGoal [← goal.replaceTargetDefEq (mkAppN t.getAppFn (args.set! (args.size - 4) b'))]

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

/-- Apply the exact weakest-precondition rules of the model, outermost first, as long as one applies,
    and reduce the continuations `weiterEA`/`weiterBA` at a known outcome: symbolic execution of a
    lowered body in constructor form by the model's own rules. Every rule is an equivalence, so the
    remaining goals say exactly what the program owes. -/
macro "gabbrov_wp" : tactic => `(tactic| repeat' (first
  | gabbrov_schritt
  | (simp only [Gabbro.Grammatik.WP.weiterEA, Gabbro.Grammatik.WP.weiterBA])
  | (dsimp only [Gabbro.Grammatik.EndAusgang.schrumpf, Gabbro.Grammatik.Ausgang.schrumpf,
      Gabbro.Grammatik.Ausgang.schrumpfArm, Gabbro.Grammatik.EndAusgang.zuAusgang])))

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


/-- **The duty of one function, as far as the language carries it**: open the duty at the function's
    own lowering (`pflicht_oeffnen`), put the lowered body into normal form, execute it symbolically by
    the model's exact rules (`gabbrov_wp`) and close the return obligation (`gabbrov_fertig`). Every
    step is checked by the kernel. What remains is the program's own logic. -/
macro "gabbrov_beweis" : tactic => `(tactic| (
  apply Gabbro.Bruecke.pflicht_oeffnen
  intro P fs hlow v hv hens hrumpf Q sp main args roots gestartet checks
  rw [← Gabbro.Bruecke.lowerAtPair_von _ ⟨v, hv⟩ hv] at hens hrumpf
  refine Gabbro.Bruecke.logikFn_aus (fun passes => ?_) (fun passes => ?_) (fun passes => ?_) <;>
    intro O' _ _ _ U _ A _ R _ _ σ ρ _ <;>
    show Gabbro.Grammatik.WP.wpEA _ _ _ _ _ _ (P.rumpf _) _ σ ρ <;>
    rw [hrumpf] <;> gabbrov_rumpf <;> gabbrov_wp
  all_goals gabbrov_fertig hens))

end Gabbro.Bruecke
