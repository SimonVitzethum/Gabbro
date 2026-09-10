/-
  File:     Grammatik/Zeugnis.lean
  Subject:  The certificate side of the S4/V5 witness pair (Lean side only).

  SOURCE SENTENCES
    dokumente/PLAN-UMSETZUNG.md §1.3 -- the derivation printed as Lean; Lean
      accepting the print is the statement that the program is a sentence of
      the grammar. A `Zeugnis` the Rust side gets wrong is a Lean error at the
      line of the constructor.
    dokumente/PLAN-SICHERHEIT.md S4 (`checker_agrees` witness pairs per unit)
      + dokumente/PLAN-VERIFIKATION.md §3/V5 -- `gabbro lean` writes, per unit,
      `theorem checker_agrees : ... := by decide`; disagreement fails LOUDLY.
    messung/ZIEL-BEWERTUNG-2026-09-10.md, "S4 scope" -- the W16 seam fails loudly
      per routine per run instead of silently.

  WHAT STANDS HERE
    `CertExpr` -- the printed certificate format: derivation terms as PLAIN DATA
      (ranges as numbers, side conditions NOT as proofs). This is what the Rust
      printer writes; it carries no evidence by itself.
    `certRange` -- the range table (M104/M102), recomputed on the Lean side.
    `GueltigAbleitung c lo hi` -- the validity predicate: the printed claim
      `(lo, hi)` is EXACTLY what the table recomputes. A forged or mismatched
      print is not "rejected with a message"; it is PROVABLY invalid
      (`¬ GueltigAbleitung ...`, closed by `decide` below), and no acceptance
      proof can be built from it -- failure by construction, not by diagnostic.
    `zeugnis_sound` -- soundness: a valid certificate IMPLIES the judgment,
      i.e. elaborates to a real `Expr` term (an accepted derivation). This is
      the direction this file owns.

  TRUST BASE (explicit)
    The Rust printer (`gabbro lean` / `gabbro-ableitung`, PLAN-UMSETZUNG.md §1.3)
    is TRUST BASE here and stays trust base: this file proves
    valid-print-implies-judgment, NOT printer-prints-what-checker-derived.
    A printer that prints a different derivation than the one it checked is
    outside this file -- exactly as §1.3 books it (the print, not the printer,
    is what Lean checks).

  CUTS (shrunk, not faked -- each booked cut is a constructor this file does NOT cover)
    CUT-1 signed division and remainder (`sdiv`/`srem`): COVERED below
      (certificate rows, validity side conditions, soundness cases, probes).
    CUT-2 bitwise and shifts (`band`/`bor`/`bxor`/`shl`/`shr`, width proofs):
      COVERED below (same shape as CUT-1).
    CUT-3 floats, options, sums, grounds, quantifiers, `reaches`: STILL BOOKED.
    CUT-4 variables and every carrier access (globals, slots, pointers:
      needs `D`, guards, `Λ`).
    CUT-5 everything with a resource context: statements, blocks, programs,
      `RufPasst`, linear balance (`Λ.Perm V.ende`), ranks, marks.
    The fragment is closed arithmetic: every certificate elaborates in ANY
    context `Γ Λ` by construction (no context is ever consulted).

  CHECK
    cd grammatik && lake env lean Grammatik/Zeugnis.lean
    Finished proofs only: the build log carries no unfinished-proof warning,
    and `#print axioms zeugnis_sound` at the end names every axiom the
    soundness proof rests on.
-/
import Grammatik.Syntax

namespace Gabbro.Grammatik

/-- The printed certificate: a derivation term as plain data.

    Each constructor mirrors the `Expr` constructor of the same shape, but the
    hypothesis fields are ABSENT: the claimed result range `(lo, hi)` travels
    beside the term (as the argument of `GueltigAbleitung`), and every side
    condition (`0 ≤ l1`, `1 ≤ l2`, `lo' ≤ l1`, ...) is recomputed by
    `certRange`, never trusted from the print. -/
inductive CertExpr where
  | lit (n : Int)
  | add (a b : CertExpr)
  | sub (a b : CertExpr)
  | neg (a : CertExpr)
  | mul (a b : CertExpr)
  | div (a b : CertExpr)
  | rem (a b : CertExpr)
  | sdiv (a b : CertExpr)
  | srem (a b : CertExpr)
  | band (a b : CertExpr)
  | bor (w : Nat) (a b : CertExpr)
  | bxor (w : Nat) (a b : CertExpr)
  | shl (a b : CertExpr)
  | shr (a b : CertExpr)
  | wide (lo' hi' : Int) (a : CertExpr)
  deriving DecidableEq, Repr

/-- The range table, recomputed on the Lean side: M104 for the shapes,
    M102 (`0 ≤ l1`, `1 ≤ l2`) for `/` and `%`, the second sentence of SG-3
    (`1 ≤ l2 ∨ h2 ≤ -1`) for `sdiv`/`srem`, M137 (`0 ≤ l1`, `0 ≤ l2`, and the
    width `h < 2 ^ w` for `bor`/`bxor`) for bitwise and shifts. `none` means
    the print has no range at all -- a forged side condition lands here,
    not in a diagnostic.

    The bounds are written EXACTLY as in `Expr` (`Syntax.lean` §3): whatever
    `certRange` computes for a valid certificate is definitionally the index
    of the `Expr` term `zeugnis_sound` builds. -/
def certRange : CertExpr → Option (Int × Int)
  | .lit n => some (n, n)
  | .add a b =>
    match certRange a, certRange b with
    | some (l1, h1), some (l2, h2) => some (l1 + l2, h1 + h2)
    | _, _ => none
  | .sub a b =>
    match certRange a, certRange b with
    | some (l1, h1), some (l2, h2) => some (l1 - h2, h1 - l2)
    | _, _ => none
  | .neg a =>
    match certRange a with
    | some (l1, h1) => some (-h1, -l1)
    | none => none
  | .mul a b =>
    match certRange a, certRange b with
    | some (l1, h1), some (l2, h2) =>
      some (imin (imin (l1 * l2) (l1 * h2)) (imin (h1 * l2) (h1 * h2)),
            imax (imax (l1 * l2) (l1 * h2)) (imax (h1 * l2) (h1 * h2)))
    | _, _ => none
  | .div a b =>
    match certRange a, certRange b with
    | some (l1, h1), some (l2, _h2) =>
      if 0 ≤ l1 ∧ 1 ≤ l2 then some (0, h1) else none
    | _, _ => none
  | .rem a b =>
    match certRange a, certRange b with
    | some (l1, _h1), some (l2, h2) =>
      if 0 ≤ l1 ∧ 1 ≤ l2 then some (0, h2 - 1) else none
    | _, _ => none
  | .sdiv a b =>
    match certRange a, certRange b with
    | some (l1, h1), some (l2, h2) =>
      if 1 ≤ l2 ∨ h2 ≤ -1 then some (-(betragMax l1 h1), betragMax l1 h1) else none
    | _, _ => none
  | .srem a b =>
    match certRange a, certRange b with
    | some (_, _), some (l2, h2) =>
      if 1 ≤ l2 ∨ h2 ≤ -1 then some (-(betragMax l2 h2 - 1), betragMax l2 h2 - 1) else none
    | _, _ => none
  | .band a b =>
    match certRange a, certRange b with
    | some (l1, h1), some (l2, _h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 then some (0, h1) else none
    | _, _ => none
  | .bor w a b =>
    match certRange a, certRange b with
    | some (l1, h1), some (l2, h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w then some (0, 2 ^ w - 1) else none
    | _, _ => none
  | .bxor w a b =>
    match certRange a, certRange b with
    | some (l1, h1), some (l2, h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w then some (0, 2 ^ w - 1) else none
    | _, _ => none
  | .shl a b =>
    match certRange a, certRange b with
    | some (l1, h1), some (l2, h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 then some (0, h1 * 2 ^ h2.toNat) else none
    | _, _ => none
  | .shr a b =>
    match certRange a, certRange b with
    | some (l1, h1), some (l2, _h2) =>
      if 0 ≤ l1 ∧ 0 ≤ l2 then some (0, h1) else none
    | _, _ => none
  | .wide lo' hi' a =>
    match certRange a with
    | some (l1, h1) =>
      if lo' ≤ l1 ∧ h1 ≤ hi' then some (lo', hi') else none
    | none => none

/-- Certificate validity: the printed claim `(lo, hi)` is exactly what the
    table recomputes. Decidable by construction, so both acceptance and
    rejection of a print close by `decide`. -/
abbrev GueltigAbleitung (c : CertExpr) (lo hi : Int) : Prop :=
  certRange c = some (lo, hi)

/-- Soundness: a valid certificate IMPLIES the judgment -- there EXISTS an
    accepted derivation, the `Expr` term the grammar admits. The induction is
    over the certificate; each case hands the recomputed side conditions to
    the corresponding `Expr` constructor. (An `∃`, not the term itself: the
    judgment is the proposition that the derivation exists -- the witness-pair
    shape of S4/V5.) -/
theorem zeugnis_sound {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (c : CertExpr) (lo hi : Int) (h : GueltigAbleitung c lo hi) :
    ∃ _ : Expr D Γ Λ (.int lo hi), True := by
  induction c generalizing lo hi with
  | lit n =>
    simp only [GueltigAbleitung, certRange, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Expr.lit n, trivial⟩
  | add a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        obtain ⟨eb, _⟩ := ihb _ _ hb
        exact ⟨Expr.add ea eb, trivial⟩
  | sub a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        obtain ⟨eb, _⟩ := ihb _ _ hb
        exact ⟨Expr.sub ea eb, trivial⟩
  | neg a iha =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ea, _⟩ := iha _ _ ha
      exact ⟨Expr.neg ea, trivial⟩
  | mul a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        obtain ⟨eb, _⟩ := ihb _ _ hb
        exact ⟨Expr.mul ea eb, trivial⟩
  | div a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, _⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 1 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.div hc.1 hc.2 ea eb, trivial⟩
        · simp [hc] at h
  | rem a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, _⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 1 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.rem hc.1 hc.2 ea eb, trivial⟩
        · simp [hc] at h
  | sdiv a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 1 ≤ l2 ∨ h2 ≤ -1
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.sdiv hc ea eb, trivial⟩
        · simp [hc] at h
  | srem a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨_, _⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 1 ≤ l2 ∨ h2 ≤ -1
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.srem hc ea eb, trivial⟩
        · simp [hc] at h
  | band a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, _⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.band hc.1 hc.2 ea eb, trivial⟩
        · simp [hc] at h
  | bor w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          obtain ⟨h0, h0', hw1, hw2⟩ := hc
          exact ⟨Expr.bor w h0 h0' hw1 hw2 ea eb, trivial⟩
        · simp [hc] at h
  | bxor w a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2 ∧ h1 < 2 ^ w ∧ h2 < 2 ^ w
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          obtain ⟨h0, h0', hw1, hw2⟩ := hc
          exact ⟨Expr.bxor w h0 h0' hw1 hw2 ea eb, trivial⟩
        · simp [hc] at h
  | shl a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, h2⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.shl hc.1 hc.2 ea eb, trivial⟩
        · simp [hc] at h
  | shr a b iha ihb =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      cases hb : certRange b with
      | none => simp [ha, hb] at h
      | some q =>
        obtain ⟨l2, _⟩ := q
        simp only [ha, hb] at h
        by_cases hc : 0 ≤ l1 ∧ 0 ≤ l2
        · rw [if_pos hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ea, _⟩ := iha _ _ ha
          obtain ⟨eb, _⟩ := ihb _ _ hb
          exact ⟨Expr.shr hc.1 hc.2 ea eb, trivial⟩
        · simp [hc] at h
  | wide lo' hi' a iha =>
    simp only [GueltigAbleitung, certRange] at h
    cases ha : certRange a with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨l1, h1⟩ := p
      simp only [ha] at h
      by_cases hc : lo' ≤ l1 ∧ h1 ≤ hi'
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ea, _⟩ := iha _ _ ha
        exact ⟨Expr.weiter hc.1 hc.2 ea, trivial⟩
      · simp [hc] at h

/-! ## Witness pairs: acceptance and rejection, both by `decide` -/

/-- `1 + 2` printed as `(3, 3)`: Lean accepts the print. -/
example : GueltigAbleitung (.add (.lit 1) (.lit 2)) 3 3 := by decide

/-- `5 / 2` printed as `(0, 5)`: nonneg dividend, positive divisor (M102). -/
example : GueltigAbleitung (.div (.lit 5) (.lit 2)) 0 5 := by decide

/-- `5` widened to `0 .. 10`: a checked `weiter` in the safe direction. -/
example : GueltigAbleitung (.wide 0 10 (.lit 5)) 0 10 := by decide

/-- MISMATCHED print: `1 + 2` claimed as `(0, 0)` -- provably not valid.
    This is the loud failure: no acceptance proof can be built from it. -/
example : ¬ GueltigAbleitung (.add (.lit 1) (.lit 2)) 0 0 := by decide

/-- FORGED proof: `5 / 0` -- the divisor range admits zero, so the table
    yields no range at all. -/
example : ¬ GueltigAbleitung (.div (.lit 5) (.lit 0)) 0 5 := by decide

/-- FORGED widening: `20` claimed in `0 .. 10` -- outside, no certificate. -/
example : ¬ GueltigAbleitung (.wide 0 10 (.lit 20)) 0 10 := by decide

/-! ### CUT-1 and CUT-2 probes: signed division, bitwise, shifts -/

/-- `7 sdiv 2` printed as `(-7, 7)`: the divisor excludes zero (SG-3, second sentence). -/
example : GueltigAbleitung (.sdiv (.lit 7) (.lit 2)) (-7) 7 := by decide

/-- FORGED proof: `7 sdiv 0` -- same claim as above, but the divisor admits zero. -/
example : ¬ GueltigAbleitung (.sdiv (.lit 7) (.lit 0)) (-7) 7 := by decide

/-- `7 srem 2` printed as `(-1, 1)`: the remainder range comes from the DIVISOR. -/
example : GueltigAbleitung (.srem (.lit 7) (.lit 2)) (-1) 1 := by decide

/-- FORGED proof: `7 srem 0` -- same claim as above, but the divisor admits zero. -/
example : ¬ GueltigAbleitung (.srem (.lit 7) (.lit 0)) (-1) 1 := by decide

/-- `6 band 3` printed as `(0, 6)`: both operands nonneg (M137). -/
example : GueltigAbleitung (.band (.lit 6) (.lit 3)) 0 6 := by decide

/-- FORGED proof: a negative operand under `band` -- no range at all. -/
example : ¬ GueltigAbleitung (.band (.sub (.lit 0) (.lit 1)) (.lit 3)) 0 0 := by decide

/-- `6 bor 3` in width 3 printed as `(0, 7)`: both bounds fit under `2 ^ 3`. -/
example : GueltigAbleitung (.bor 3 (.lit 6) (.lit 3)) 0 7 := by decide

/-- FORGED proof: width 2 does not hold `6` -- the width side condition fails. -/
example : ¬ GueltigAbleitung (.bor 2 (.lit 6) (.lit 3)) 0 3 := by decide

/-- `6 bxor 3` in width 3 printed as `(0, 7)`: same width rule as `bor`. -/
example : GueltigAbleitung (.bxor 3 (.lit 6) (.lit 3)) 0 7 := by decide

/-- FORGED proof: width 2 does not hold `6` under `bxor` either. -/
example : ¬ GueltigAbleitung (.bxor 2 (.lit 6) (.lit 3)) 0 3 := by decide

/-- `3 shl 2` printed as `(0, 12)`: `3 * 2 ^ 2`, both operands nonneg. -/
example : GueltigAbleitung (.shl (.lit 3) (.lit 2)) 0 12 := by decide

/-- FORGED proof: a negative value shifted -- no range at all. -/
example : ¬ GueltigAbleitung (.shl (.sub (.lit 0) (.lit 1)) (.lit 2)) 0 0 := by decide

/-- `12 shr 2` printed as `(0, 12)`: a right shift never widens (M137). -/
example : GueltigAbleitung (.shr (.lit 12) (.lit 2)) 0 12 := by decide

/-- FORGED proof: a negative value shifted right -- no range at all. -/
example : ¬ GueltigAbleitung (.shr (.sub (.lit 0) (.lit 1)) (.lit 2)) 0 0 := by decide

/-- End to end: a valid print YIELDS an accepted derivation. -/
example {D : Deklaration} : ∃ _ : Expr D [] [] (.int 3 3), True :=
  zeugnis_sound (.add (.lit 1) (.lit 2)) 3 3 (by decide)

#eval certRange (.mul (.lit 2) (.lit 3))
#eval certRange (.div (.lit 5) (.lit 0))
#eval certRange (.sdiv (.lit 7) (.lit 2))
#eval certRange (.bor 3 (.lit 6) (.lit 3))

#print axioms zeugnis_sound

end Gabbro.Grammatik
