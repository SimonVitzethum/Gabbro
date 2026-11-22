module
public import Bruecke.Zertifikat.Satz
public import Bruecke.Zertifikat.Programm
@[expose] public section

/-!
# Proof support for the duties: opening a function's duty, the weakest-precondition rules

`zielF_aus` opens the duty `ZielF u f` of one function at its own lowering: the program's body and
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
theorem zielF_aus {u : UProg} {f : Fin u.fns.length}
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

/-- Apply the exact weakest-precondition rules of the model to the goal. -/
macro "gabbrov_wp" : tactic => `(tactic| simp only [Gabbro.Grammatik.WP.wpEA_cons,
  Gabbro.Grammatik.WP.wpEA_bind, Gabbro.Grammatik.WP.wpEA_ret, Gabbro.Grammatik.WP.wpBA_cons,
  Gabbro.Grammatik.WP.wpBA_bind, Gabbro.Grammatik.WP.wpBA_nil, Gabbro.Grammatik.WP.wpSA_ite,
  Gabbro.Grammatik.WP.wpSA_ret, Gabbro.Grammatik.WP.wpSA_locks, Gabbro.Grammatik.WP.wpBA_narrow,
  Gabbro.Grammatik.WP.wpBA_check, Gabbro.Grammatik.WP.weiterEA, Gabbro.Grammatik.WP.weiterBA])

#print axioms zielF_aus

end Gabbro.Bruecke
