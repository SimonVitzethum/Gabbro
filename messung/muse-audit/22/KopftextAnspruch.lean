import Grammatik.Maschine

open Gabbro.Grammatik

/-! ## Docstring overclaim check (pattern d): what the headers promise

Two checked header-vs-statement comparisons (no new theorems needed; the
evidence is the quoted statement shape, verified by the `#print axioms`
lines and by the demonstrations in the sibling files):

1. §15 header says `zaehler_zeigt_atom_lauf` gives "the per-run form -- any
   leaf step occurring anywhere in a generated run derivation satisfies the
   same identity". Checked: the conclusion
   `(prog f)[pcmid f]? = some (PCAtom.leaf Λ cs₀)` mentions neither the run
   `h`, nor the membership `hmem`, nor `M`/`pc`. Files
   `SchrittMitgliedschaft.lean` demonstrations A/B/C prove the same
   conclusions without `hmem`. The "per-run" packaging adds no per-run
   content: the theorem is the per-step identity with dead run parameters.

2. §17 header says `zaehler_aus_konstruktion_voll` closes "the positional
   routing (the atom the counter points at fires)". Checked: the proof reads
   the fired atom off the step's OWN `hpc` field (each `rcases hs` branch
   returns the constructor's `hpc`/`hpcT`/`hpcR` unchanged) and the advance
   off `pcSchritt_eigen`. File `SchrittMitgliedschaft.lean` demonstration D
   replays the conclusion from `hs` alone. Nothing is routed FROM the counter
   TO the firing: the direction is reversed -- the counter slot travels inside
   the step evidence, and the theorem unpacks it. "The atom the counter points
   at fires" is therefore a gloss on an unpacking: the step cannot fire a
   different atom than its own `hpc` slot by construction of the inductive.

The one genuine derivation in §§15-17 (NOT flagged): `pc_zero_without_prior_step`
and `pc_ne_zero_with_prior_step` prove counter facts (zero / nonzero) FROM the
threading (`pcSchritt_fremd`/`pcSchritt_eigen`) by induction -- the conclusion
`pc f = 0` / `pc f ≠ 0` is not present in any premise. Likewise
`zaehler_aus_konstruktion_erstschritt` computes the atom from `HeadAtom`
rather than from the step's `hpc` slot. These are real, if narrow, results.
-/

-- Minimal witness that the §17 conclusion is an unpacking of `hs`:
-- casing the step already yields all three disjuncts' witnesses.
example (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
    (hs : PCSchritt P O passes prog M pc f M' pc') :
    (∃ Λa : List (Res D), ∃ cs : List (D.Tab ⊕ D.Glob),
      (prog f)[pc f]? = some (PCAtom.leaf Λa cs)) ∨
    (∃ L : D.Lock, (prog f)[pc f]? = some (PCAtom.take L)) ∨
    (∃ L : D.Lock, (prog f)[pc f]? = some (PCAtom.rel L)) := by
  cases hs with
  | leaf _ _ _ _ _ _ _ _ _ _ _ _ _ _ Λa cs hpc _ _ _ =>
      exact Or.inl ⟨Λa, cs, hpc⟩
  | take L _ _ _ hpcT =>
      exact Or.inr (Or.inl ⟨L, hpcT⟩)
  | rel L _ hpcR =>
      exact Or.inr (Or.inr ⟨L, hpcR⟩)

#print axioms pc_zero_without_prior_step
#print axioms pc_ne_zero_with_prior_step
#print axioms zaehler_aus_konstruktion_erstschritt

/-!
CUTS:
- Pattern (d) findings are header-vs-statement comparisons; the Lean
  demonstration proves the unpacking direction, the "overclaim" judgment
  itself is prose in MUSE-REPORT-22.md.
- The §16 singleton impossibility argument (second step by `f` contradicts
  the text shape) genuinely uses `hprog` against `hpc` and is NOT flagged.
-/
