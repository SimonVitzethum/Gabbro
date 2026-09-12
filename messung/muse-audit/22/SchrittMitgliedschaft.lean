import Grammatik.Maschine

open Gabbro.Grammatik

/-! ## Step-membership wrappers (pattern a: conclusion restates a cased premise)

`zaehler_zeigt_atom_lauf`: both branches of the `SchrittImLauf` case split close
with the identical call `zaehler_zeigt_atom ... hpc hΛa hcs`. The membership proof
`hmem` is cased on but no branch extracts anything from it: the conclusion does
not mention `M`, `pc`, `h`, or anything `hmem` determines. The `frueher` branch
in particular discards the membership content and replays the same identity.

`zaehler_routing_fremd` / `zaehler_routing_gen`: same shape -- case on `hmem`,
apply `pcSchritt_fremd` / `pcSchritt_gen` to `hs` in both branches.
-/

-- Demonstration A: zaehler_zeigt_atom_lauf with the membership proof replaced.
-- If `hmem` contributed content, swapping `letzter` for a `frueher` proof (or
-- vice versa) would change the conclusion; it does not, because both branches
-- ignore the case data.
example (prog : PCProg D) (M0 Mmid : GenMaschine D) (pcmid : PCStand) (f : Faden)
    (M' : GenMaschine D) (pc' : PCStand)
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc')
    (Λ : List (Res D)) (cs₀ : List (D.Tab ⊕ D.Glob))
    (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
    (hpc : (prog f)[pcmid f]? = some (PCAtom.leaf Λa cs))
    (hΛa : Λa = Λ) (hcs : cs = cs₀)
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc)
    (_hmem : SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs h) :
    (prog f)[pcmid f]? = some (PCAtom.leaf Λ cs₀) :=
  -- The whole run context (M, pc, h, hmem) is dead weight: the per-step
  -- identity closes the goal alone. (Lean's unused-variable linter fires on
  -- `_hmem`'s non-underscore original, confirming the premise is never used.)
  zaehler_zeigt_atom prog f pcmid Λ cs₀ Λa cs hpc hΛa hcs

-- Demonstration B: zaehler_routing_gen ignores membership the same way.
example (prog : PCProg D) (M0 Mmid : GenMaschine D) (pcmid : PCStand) (f : Faden)
    (M' : GenMaschine D) (pc' : PCStand)
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc')
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc)
    (_hmem : SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs h) :
    GenSchritt P O passes Mmid f M' :=
  -- Membership unused: the projection holds for the step alone.
  pcSchritt_gen P O passes prog Mmid M' pcmid pc' f hs

-- Demonstration C: zaehler_routing_fremd likewise.
example (prog : PCProg D) (M0 Mmid : GenMaschine D) (pcmid : PCStand) (f : Faden)
    (M' : GenMaschine D) (pc' : PCStand)
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc')
    (g : Faden) (hne : g ≠ f)
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc)
    (_hmem : SchrittImLauf P O passes prog M0 Mmid pcmid f M' pc' hs h) :
    pc' g = pcmid g :=
  pcSchritt_fremd P O passes prog Mmid M' pcmid pc' f g hs hne

-- Demonstration D: zaehler_aus_konstruktion_voll restates the step's own slots.
-- The conclusion's three disjuncts are exactly the `hpc`/`hpcT`/`hpcR` fields of
-- the three PCSchritt constructors plus the `pcSchritt_eigen` advance; the run
-- membership `hmem` contributes nothing beyond selecting the branch.
-- (`M0` unused on purpose: the whole per-run context is dead weight here, as
-- Lean's unused-variable linter confirms.)
example (prog : PCProg D) (M0 Mmid : GenMaschine D) (pcmid : PCStand) (f : Faden)
    (M' : GenMaschine D) (pc' : PCStand)
    (P : Programm D) (O : Orakel D) (passes : Nat)
    (hs : PCSchritt P O passes prog Mmid pcmid f M' pc') :
    (∃ Λa : List (Res D), ∃ cs : List (D.Tab ⊕ D.Glob),
      (prog f)[pcmid f]? = some (PCAtom.leaf Λa cs) ∧ pc' f = pcmid f + 1) ∨
    (∃ L : D.Lock, (prog f)[pcmid f]? = some (PCAtom.take L) ∧ pc' f = pcmid f + 1) ∨
    (∃ L : D.Lock, (prog f)[pcmid f]? = some (PCAtom.rel L) ∧ pc' f = pcmid f + 1) := by
  have hadv : pc' f = pcmid f + 1 :=
    pcSchritt_eigen P O passes prog Mmid M' pcmid pc' f hs
  rcases hs with
      ⟨_V, _l, _Γ, _Λs, _Λs', _s, _ρ, _hleaf, _hΛ, _σ', _neu, _hstep, _hneu,
        _hkn, Λa, cs, hpc, _hΛa, _hmark, _hcar⟩
    | ⟨L, _hself, _hrang, _hfrei, hpcT⟩
    | ⟨L, _hhaelt, hpcR⟩
  · exact Or.inl ⟨Λa, cs, hpc, hadv⟩
  · exact Or.inr (Or.inl ⟨L, hpcT, hadv⟩)
  · exact Or.inr (Or.inr ⟨L, hpcR, hadv⟩)

#print axioms zaehler_zeigt_atom_lauf
#print axioms zaehler_routing_gen
#print axioms zaehler_aus_konstruktion_voll

/-!
CUTS:
- Demonstration D replays the proof of `zaehler_aus_konstruktion_voll` without
  the `h`/`hmem` premises; it does not show the premises are useless in every
  use site, only that the conclusion is already forced by `hs` alone.
- No claim is made that the routing facts are false; the finding is pattern (a):
  per-run packaging of a per-step fact.
-/
