module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil1
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil4

@[expose] public section

namespace Gabbro.Grammatik

-- Shared frame-proof steps; local names are supplied by the calling case.
set_option hygiene false in
macro "frame_value" ex:ident world:term:max : tactic => `(tactic| (
  simp only [$ex, $world, Option.some.injEq] at h; subst h))

-- Shared frame-proof steps; local names are supplied by the calling case.
set_option hygiene false in
macro "frame_read_split" ex:ident os:term:max good:term:max bad:term:max : tactic => `(tactic| (
  simp only [$ex] at h
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ $os
  split at h
  · exact $good
  · exact $bad))

-- Discharge a `ScopesOk` side goal from the ambient `hscope` (mirrors `scopes_gut`).
-- Unfold scope-premise abbreviations before simplifying their Boolean checks.
set_option hygiene false in
macro "scopes_treu" : tactic => `(tactic| first
  | exact hscope
  | (have hsc := hscope
     dsimp only [Stmt.ScopesOk, Block.ScopesOk, Endblock.ScopesOk, Arms.ScopesOk, GrundArms.ScopesOk] at hsc
     simp only [Stmt.scopesOk, Block.scopesOk, Endblock.scopesOk, Arms.scopesOk, GrundArms.scopesOk, Bool.and_eq_true] at hsc
     first | exact hsc | exact hsc.1 | exact hsc.2 | exact hsc.2.1 | exact hsc.2.2 | exact hsc.1.1 | exact hsc.1.2))

-- Shared frame-proof steps; local names are supplied by the calling case.
-- (Call arms are explicit: the ok exit takes `Treu` from `TreuR` under the
-- transported entry discipline, a propagated reason collapses via
-- `TreuRet.toTreu_entry`; both then run the continuation with `vorCall`.)
set_option hygiene false in
macro "frame_call_ok" s0:term : tactic => `(tactic| (
  have hentry : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) ($s0).haelt :=
    heldB_ruf hp hbV (hl.heldB hh)
  have h2 := hR f $s0 _ hentry σ1 (by rw [hR1]; rfl)
  rw [hR1] at h2
  have g1 := hl.trans (Treu.weiter hp.hw hp.hg h2)))

-- Shared frame-proof steps; local names are supplied by the calling case.
set_option hygiene false in
macro "frame_call_why" s0:term : tactic => `(tactic| (
  have hentry : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) ($s0).haelt :=
    heldB_ruf hp hbV (hl.heldB hh)
  have h2 := hR f $s0 _ hentry σ1 (by rw [hR1]; rfl)
  rw [hR1] at h2
  have gcall : Treu V.schreibt V.gschreibt $s0 σ1 :=
    (Treu.weiter hp.hw hp.hg h2).toTreu_entry hentry
  have g1 := hl.trans gcall))

-- Shared frame-proof steps; local names are supplied by the calling case.
set_option hygiene false in
macro "frame_axiom_next" hw:term:max hg:term:max next:term:max : tactic => `(tactic| (
  have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
  rw [ha] at h1
  have g1 := hl.trans (Treu.weiter $hw $hg h1)
  exact $next))

-- Shared frame-proof steps; local names are supplied by the calling case.
set_option hygiene false in
macro "frame_axiom_else" : tactic => `(tactic| (
  have h1 := axiomAntwort_treu O hO a (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
  rw [← axiomAntwortSonst_fst] at h1))

-- Shared frame-proof steps; local names are supplied by the calling case.
set_option hygiene false in
macro "frame_axiom_advance" hw:term:max hg:term:max next:term:max : tactic => `(tactic| (
  rw [ha] at h1
  have g1 := hl.trans (Treu.weiter $hw $hg h1)
  exact $next))

-- Shared frame-proof steps; local names are supplied by the calling case.
set_option hygiene false in
macro "frame_optional" out:ident recurse:term:max : tactic => `(tactic| (
  have ihr := fun ρ' => $recurse rest σ1 ρ'
  cases e with
  | none =>
      simp only [$out] at h
      exact g1.trans ((ihr _) σ' h)
  | some τ =>
      simp only [$out] at h
      exact g1.trans ((ihr _).schrumpf σ' h)))

-- Open a continuation after recording its expression reads.
set_option hygiene false in
macro "frame_read_cases" ex:ident os:term:max : tactic => `(tactic| (
  simp only [$ex] at h
  have hl := treu_lese (W := V.schreibt) (G := V.gschreibt) σ Λ $os
  split at h))

end Gabbro.Grammatik
