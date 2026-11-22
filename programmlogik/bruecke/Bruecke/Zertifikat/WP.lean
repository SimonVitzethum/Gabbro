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

/-- Apply the exact weakest-precondition rules of the model to the goal, outermost first, until none
    applies: symbolic execution of a lowered body in constructor form by the model's own rules. Every rule
    is an equivalence, so the remaining goal says exactly what the program owes. -/
macro "gabbrov_wp" : tactic => `(tactic| repeat (first
  | refine (Gabbro.Grammatik.WP.wpEA_ret ..).mpr ?_
  | refine (Gabbro.Grammatik.WP.wpEA_cons ..).mpr ?_
  | refine (Gabbro.Grammatik.WP.wpEA_bind ..).mpr ?_
  | refine (Gabbro.Grammatik.WP.wpBA_cons ..).mpr ?_
  | refine (Gabbro.Grammatik.WP.wpBA_bind ..).mpr ?_
  | refine (Gabbro.Grammatik.WP.wpBA_nil ..).mpr ?_
  | refine (Gabbro.Grammatik.WP.wpSA_ite ..).mpr ?_
  | refine (Gabbro.Grammatik.WP.wpSA_ret ..).mpr ?_
  | refine (Gabbro.Grammatik.WP.wpSA_locks ..).mpr ?_
  | refine (Gabbro.Grammatik.WP.wpBA_narrow ..).mpr ?_
  | refine (Gabbro.Grammatik.WP.wpBA_check ..).mpr ?_))

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
  let e' ← withTransparency .all <| Meta.reduce e (explicitOnly := true) (skipTypes := true) (skipProofs := true)
  let goal ← getMainGoal
  let eq ← mkEq e e'
  let prf ← mkExpectedTypeHint (← mkEqRefl e) eq
  let r ← goal.rewrite (← goal.getType) prf
  let g' ← goal.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g' :: r.mvarIds)

/-- **Run the model's semantics on a body in constructor form**: every application of `execEndHA`,
    `execBlockHA`, `execStmtHA` in the goal is put into weak head normal form (all definitions unfolded).
    The goal changes only up to definitional equality, which the kernel checks. -/
syntax (name := gabbrovLauf) "gabbrov_lauf" : tactic

open Lean Elab Tactic Meta in
@[tactic gabbrovLauf] meta def evalGabbrovLauf : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let namen := [``Gabbro.Grammatik.execEndHA, ``Gabbro.Grammatik.execBlockHA, ``Gabbro.Grammatik.execStmtHA]
  let t' ← Meta.transform t (post := fun e => do
    if namen.any e.isAppOf then
      return .done (← withTransparency .all <| whnf e)
    else return .continue)
  replaceMainGoal [← goal.replaceTargetDefEq t']

#print axioms pflicht_oeffnen

end Gabbro.Bruecke
