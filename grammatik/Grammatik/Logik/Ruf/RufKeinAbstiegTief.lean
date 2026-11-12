/-
  File:      Grammatik/RufKeinAbstiegTief.lean
  Subject:   **`abstieg` IS UNREACHABLE AT SUFFICIENT DEPTH FOR A FINITE CALL
              TREE** -- the plan item S5, first half of B9.

  `rufTief P (n + 1) g = true` says the call tree of `g` is finite: every
  direct callee is admitted at depth `n`, and the body makes no indirect
  call (`rufeE` with `ZS = fun _ => false`, so indirect calls can NOT be
  bounded this way -- the theorem is restricted to programs without them by
  its premise). A function without calls is admitted at depth `1`, so depth
  `1` already excludes its `abstieg`.

  The proof is induction on the depth: at depth `n + 1` the body runs
  against the handler `rufAt n`, which never answers `abstieg` on admitted
  callees by the induction hypothesis, so the body run never ends in an
  `abstieg` (`RufKeinAbstieg.lean`), and the entry, exit and invariant
  checks of `rufSchritt` only add non-`abstieg` `logik` outcomes.

  Monotonicity in the other direction -- a non-`abstieg` outcome at depth
  `n` is the outcome at every larger depth -- is already proved as
  `rufAt_stabil` / `rufAt_stabil_ab` (`RufTiefe.lean`) and not restated here.
-/
module
public import Grammatik.Logik.Ruf.RufKeinAbstieg
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil2
public import Grammatik.Logik.Fortschritt.KostenG.T2.Teil2
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **One unfolding adds no `abstieg` of its own.** If the handler never
    answers `abstieg` on admitted callees and the body admits no indirect
    call, `rufSchritt` over that handler never answers `abstieg`: the
    requires failure is a `vorbedingung`, the exit and invariant failures a
    `nachbedingung` respectively an `invariante`, and the body run itself is
    covered by the preservation induction. -/
theorem rufSchritt_keinAbstieg (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (Z : D.Fn → Bool) (ZS : Nat → Bool)
    (hR : ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (hh : D.Fn),
      Z g = true → R g σ ρ ≠ .logik (.abstieg hh))
    (hZS : ∀ n, ZS n = false) (g : D.Fn) (σ : World D) (ρ : Env D (D.params g))
    (hh : D.Fn) (hBody : rufeE Z ZS true (P.rumpf g) = true) :
    rufSchritt P O passes R g σ ρ ≠ .logik (.abstieg hh) := by
  simp only [rufSchritt]
  by_cases hq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte)
      (P.requires g) (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ) = false
  · rw [if_pos hq]; intro hc; cases hc
  · rw [if_neg hq]
    cases hx : execEnd (V := vertragVon D g) O passes R (P.rumpf g)
        (σ.lese (Signatur.anfang D (D.signatur g)) (P.requires g).orte) ρ with
    | zurueck σ' v =>
        -- The `match` on the constructor reduces; what is left is the exit
        -- test (`ite`) and the invariant search (`match` on `find?`), whose
        -- every branch is a `nachbedingung`, an `invariante` or an `ok`.
        dsimp only
        split <;> (try split) <;> (intro hc; cases hc)
    -- The other arms keep the `match` and let `cases hc` reduce it by `whnf`.
    | why σ' r => intro hc; cases hc
    | leave h _ _ => exact absurd h (by decide)
    | next h _ _ => exact absurd h (by decide)
    | logik e =>
        intro hc
        cases hc
        exact endKeinAbstieg O passes R Z ZS true hR hZS (P.rumpf g) _ _ hh hBody hx
    | hardware e => intro hc; cases hc

/-- **Sufficient depth makes `abstieg` unreachable.** If the call tree of
    `g` is finite with admission depth `n + 1` -- every direct callee
    admitted one level down, no indirect call -- then the call at depth
    `n + 1` never ends in `logik (abstieg _)`, on every world, environment
    and oracle. In particular a call-free function needs depth `1`. -/
theorem rufAt_keinAbstieg (P : Programm D) (O : Orakel D) (passes : Nat) :
    ∀ (n : Nat) (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (hh : D.Fn),
      rufTief P n g = true → rufAt P O passes n g σ ρ ≠ .logik (.abstieg hh)
  | 0, _, _, _, _, h => by simp only [rufTief, Bool.false_eq_true] at h
  | n + 1, g, σ, ρ, hh, h => by
      simp only [rufTief] at h
      rw [rufAt_succ_eq P O passes n]
      exact rufSchritt_keinAbstieg P O passes (rufAt P O passes n) (rufTief P n)
        (fun _ => false)
        (fun g' σ' ρ' hh' hZ => rufAt_keinAbstieg P O passes n g' σ' ρ' hh' hZ)
        (fun _ => rfl) g σ ρ hh h

#print axioms Gabbro.Grammatik.rufSchritt_keinAbstieg
#print axioms Gabbro.Grammatik.rufAt_keinAbstieg

end Gabbro.Grammatik
