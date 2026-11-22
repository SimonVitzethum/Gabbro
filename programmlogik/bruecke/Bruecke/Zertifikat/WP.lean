module
public import Bruecke.Zertifikat.Satz
public import Bruecke.Zertifikat.Programm
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

open Lean in
/-- The rule of the model for the outermost constructor of the body in a `wpEA`/`wpBA`/`wpSA` goal. -/
meta def wpRegel? (t : Lean.Expr) : Option Name :=
  let args := t.getAppArgs
  if args.size < 4 then none else
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
  | _, _ => none

/-- One step: the rule of the outermost constructor of the body (`wpRegel?`), applied by its
    equivalence. Fails when no rule applies. -/
syntax (name := gabbrovSchritt) "gabbrov_schritt" : tactic

open Lean Elab Tactic Meta in
@[tactic gabbrovSchritt] meta def evalGabbrovSchritt : Tactic := fun _ => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  match wpRegel? t with
  | some regel => evalTactic (← `(tactic| refine ($(mkIdent regel) ..).mpr ?_))
  | none => throwError "gabbrov_schritt: no rule for this goal"


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

open Lean Meta in
/-- The normal form of `e` computed by the KERNEL's reduction (fast where the elaborator's is slow):
    weak head normal form, then the same in every explicit argument of a constructor that is neither a
    proof nor a type. Implicit arguments, types and proofs are kept as they are. -/
meta partial def kernNormal (e : Lean.Expr) : MetaM Lean.Expr := do
  let e' ← match Kernel.whnf (← getEnv) (← getLCtx) e with
    | .ok r => pure r
    | .error _ => pure e
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
