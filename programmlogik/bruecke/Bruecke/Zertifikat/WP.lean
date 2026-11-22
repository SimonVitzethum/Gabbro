module
public import Bruecke.Zertifikat.Satz
public import Bruecke.Zertifikat.Programm
public import Bruecke.Zertifikat.Wert
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
    else if (t.isAppOf ``Gabbro.Bruecke.wpRetryA || t.isAppOf ``Gabbro.Bruecke.wpTravA) && args.size ≥ 4 then
      let w := args[args.size - 4]!
      let fertig := w.rawNatLit?.isSome || w.isAppOf ``List.nil || w.isAppOf ``List.cons
      if fertig then pure (goal, t) else
      let w' ← kernNormal w
      let t' := mkAppN t.getAppFn (args.set! (args.size - 4) w')
      pure (← goal.replaceTargetDefEq t', t')
    else pure (goal, t)
  if let some g ← gerade? goal t then replaceMainGoal [g] else
  if let some gs ← rufSchritt? goal t then replaceMainGoal gs else
  match wpRegel? t with
  | some regel => replaceMainGoal [← wendeAn goal regel]
  | none =>
    -- a branch whose condition the kernel decides: its weak head normal form is the branch taken
    if t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5 then
      replaceMainGoal (← verzweigung goal t)
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
  all_goals gabbrov_fertig hens
  all_goals try gabbrov_arith))

end Gabbro.Bruecke
