import Grammatik.Maschine

open Gabbro.Grammatik

/-! ## Trivially-true guards and degenerate obligations (patterns c and e)

Two checked observations about the slice's guard shapes:

1. (pattern c) The `SerialLink` conclusion guard
   `TraegerSchreibt (J.code f) (.inl t₀) = false → SerialLink Nb J' M'.lauf t₀`
   is discharged at every NEW step by deriving `False` from the guard plus the
   step's own writer hypothesis: `rw [hnw] at hwrF; simp at hwrF` (lines
   2152-2154, 3051-3053). That is: at the new step the theorem proves
   `¬(guard ∧ writer)` by contradiction inside the `by_cases heq` branch, so
   the new step never contributes a non-vacuous witness. The `SerialLink`
   conclusion is therefore inherited-only: every witness comes from `hLink`
   (old indices), never from the step itself.

2. (pattern e) `spec_aus_lauf_voll`'s seed case (`PCSpur.leer`): both eigen
   obligations close by `simp at hkg` after `rw [hJsf] at hkg`, i.e. from
   `J.schrittFaden = []` no index can satisfy `schrittFaden[k]? = some f`.
   A zero-step chain satisfies `SpecTriple` for ARBITRARY `Pre`/`Post` --
   including `Pre := fun _ _ => False` -- because `requiresHead`/`ensuresHead`
   quantify over `J.welten[0]? = some σ₀` and the eigen fields quantify over
   an empty index set. The seed triple is thus vacuous, not verified: any
   caller-supplied `hSeedPre`/`hSeedPost` does the real work, and the induction
   base contributes nothing.
-/

-- Demonstration 1: the new-step guard case is vacuous by construction.
-- For ANY boolean test `w` (standing for `TraegerSchreibt (J.code f) (.inl t₀)`)
-- and ANY proposition `Q` (standing for `SerialLink ...`), the shape used at the
-- new step is: from `guard = false` hypothesis `hnw` and writer hypothesis
-- `hwr`, derive anything. This replays lines 2151-2154 / 3050-3053 in minimal
-- form: the branch closes because the two hypotheses contradict, not because
-- a witness is built.
example (w : Bool)
    (hnw : w = false)
    (hwr : w = true)
    (Q : Prop) : Q := by
  rw [hnw] at hwr
  simp at hwr

-- Demonstration 2: a SpecTriple over an empty chain holds for arbitrary
-- (even False) contracts. This is the exact seed situation: `schrittFaden = []`
-- makes both eigen fields vacuous, and heads quantify over whatever world the
-- (singleton) world list holds at index 0.
example (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (hempty : J.schrittFaden = [])
    (f : Faden)
    (hHeadPre : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → False)
    (hHeadPost : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → False) :
    SpecTriple (fun _ _ => False) (fun _ _ => False) Nb J f := by
  -- NOTE: Lean's unused-variable linter fires on `hempty` below: the empty
  -- step list makes both eigen goals `(False ↔ False)`, closed by `rfl`
  -- without ever using the emptiness hypothesis. The eigen fields over an
  -- empty chain constrain nothing -- not even their own index hypothesis.
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ₀ h0
    exact hHeadPre σ₀ h0
  · intro σ₀ h0
    exact hHeadPost σ₀ h0
  · intro k vor nach hkg _ _
    rw [hempty] at hkg
    -- NOTE: no further tactic: the `rw` above rewrites `hkg` and its automatic
    -- closing `rfl` discharges the goal, which is `(False ↔ False)`. The eigen
    -- obligation over an empty step list is rfl-trivial -- it constrains nothing.
  · intro k vor nach hkg _ _
    rw [hempty] at hkg
    -- Same: goal is `(False ↔ False)`, closed by the `rw`'s trailing `rfl`.

-- Demonstration 3: `hBeyond`/`hNew` in spec_aus_fuehrung_fremd (lines 3697-3713)
-- has the same vacuous shape: at and beyond the frontier, `schrittFaden[k]? =
-- some f` is impossible, so the eigen obligation closes by contradiction and
-- the foreign step contributes no contract content for `f`.
example (sf : List Faden) (g f : Faden) (hne : g ≠ f)
    (k : Nat) (hle : sf.length ≤ k)
    (hkg : (sf ++ [g])[k]? = some f) : False := by
  by_cases heq : k = sf.length
  · subst heq
    have eNew : (sf ++ [g])[sf.length]? = some g := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    rw [eNew] at hkg
    exact hne (Option.some_inj.mp hkg)
  · have hlt : sf.length < k := by omega
    have eNone : (sf ++ [g])[k]? = none := by
      rw [List.getElem?_append_right (by omega : sf.length ≤ k),
        List.getElem?_eq_none_iff, List.length_singleton]
      omega
    rw [eNone] at hkg
    simp at hkg

#print axioms spec_aus_fuehrung_fremd
#print axioms spec_aus_lauf_voll

/-!
CUTS:
- Demonstration 1 abstracts `SerialLink` to `Q : Prop`; it shows the LOGICAL
  shape of the new-step branch (contradiction from guard + writer), not that
  `SerialLink` itself is trivially true -- old-index witnesses still come from
  `hLink`.
- Demonstration 2 uses `False` contracts to exhibit vacuity of the seed; it
  does not claim `spec_aus_lauf_voll` is wrong -- the induction step is real.
  The audit point is that the base case verifies nothing (pattern e: the
  "seed triple" premise `hSeedPre`/`hSeedPost` is doing all head work).
-/
