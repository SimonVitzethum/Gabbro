/-
  File:      Grammatik/Isabelle/Intervall_Aussen.lean
  Part of:   Gabbro -- Lean port of `beweise/Intervall_Aussen.thy`
             (outward rounding in M1's float propagation; lane 168).

  What this file is: the promise that the COMPUTED bound holds. The
  checker derives facts with `f64` operations; the claim is that the
  outward-rounded interval still encloses the true value. Two halves:
  addition is monotone over the value domain (ordinary interval
  arithmetic, the harmless half), and the computed bound encloses the
  real one (`huelle_haelt` -- the half this proof exists for). And the
  sharpness: exact corners do not move.

  Model notes: Isabelle works over `real` (Complex_Main) with `add_mono`
  and order transitivity from the library. There is no real library
  here, so the value domain is an abstract type `R` with an abstract
  order `le` and addition `add`, and exactly the four facts the proofs
  use are explicit hypotheses on each lemma (Isabelle's `assumes`
  lines): `h_add_mono` (the `add_mono` instance), `h_le_refl` and
  `h_le_trans` (reflexivity and transitivity of the order), and
  `h_nachbarn` (the locale assumption: the true value lies between the
  neighbours of the computed one -- the round-to-nearest promise). The locale `rundung` is these
  parameters; `aussen_lo`/`aussen_hi` are the same definitions. The real
  instance recovers the original statements. The concrete `Int` instance
  below inhabits every premise, giving the witnesses.

  No bridge to the model semantics: the checker-side float computation
  has no counterpart in `Semantik.lean`.
-/

namespace Gabbro.Grammatik.IntervallAussen

set_option linter.unusedSectionVars false

section Rundung

variable {R : Type} [DecidableEq R]
variable (le : R → R → Prop) (add : R → R → R)
variable (fl nd nu : R → R)

/-- What the checker does, SHARPLY: an exact corner does not move. -/
def aussenLo (z : R) : R :=
  if fl z = z then z else nd (fl z)

/-- What the checker does, SHARPLY: an exact corner does not move. -/
def aussenHi (z : R) : R :=
  if fl z = z then z else nu (fl z)

/-- The hull holds: the computed bound encloses the true value. -/
theorem huelle_haelt (h_le_refl : ∀ a, le a a)
    (h_nachbarn : ∀ z, le (nd (fl z)) z ∧ le z (nu (fl z))) (z : R) :
    le (aussenLo fl nd z) z ∧ le z (aussenHi fl nu z) := by
  by_cases h : fl z = z
  · have e1 : aussenLo fl nd z = z := by simp [aussenLo, h]
    have e2 : aussenHi fl nu z = z := by simp [aussenHi, h]
    rw [e1, e2]
    exact ⟨h_le_refl _, h_le_refl _⟩
  · have e1 : aussenLo fl nd z = nd (fl z) := by simp [aussenLo, h]
    have e2 : aussenHi fl nu z = nu (fl z) := by simp [aussenHi, h]
    rw [e1, e2]
    exact h_nachbarn z

/-- M-1, lower half: addition is monotone -- ordinary interval
    arithmetic. -/
theorem monoton_unten (h_add_mono : ∀ a x c y, le a x → le c y → le (add a c) (add x y))
    {a x c y : R} (h1 : le a x) (h2 : le c y) :
    le (add a c) (add x y) :=
  h_add_mono a x c y h1 h2

/-- M-1, upper half: addition is monotone -- ordinary interval
    arithmetic. -/
theorem monoton_oben (h_add_mono : ∀ a x c y, le a x → le c y → le (add a c) (add x y))
    {x b y d : R} (h1 : le x b) (h2 : le y d) :
    le (add x y) (add b d) :=
  h_add_mono x b y d h1 h2

/-- M-1, the theorem: the sum lies inside the computed bound. -/
theorem summe_liegt_in_der_gerechneten_schranke
    (h_add_mono : ∀ a x c y, le a x → le c y → le (add a c) (add x y))
    (h_le_trans : ∀ a b c, le a b → le b c → le a c)
    (h_le_refl : ∀ a, le a a)
    (h_nachbarn : ∀ z, le (nd (fl z)) z ∧ le z (nu (fl z)))
    {a x b c y d : R}
    (h1 : le a x) (h2 : le x b) (h3 : le c y) (h4 : le y d) :
    le (aussenLo fl nd (add a c)) (add x y) ∧
    le (add x y) (aussenHi fl nu (add b d)) := by
  have hlo := (huelle_haelt (le := le) (fl := fl) (nd := nd) (nu := nu)
    (h_le_refl := h_le_refl) (h_nachbarn := h_nachbarn) (add a c)).1
  have hhi := (huelle_haelt (le := le) (fl := fl) (nd := nd) (nu := nu)
    (h_le_refl := h_le_refl) (h_nachbarn := h_nachbarn) (add b d)).2
  exact ⟨h_le_trans _ _ _ hlo (monoton_unten le add h_add_mono h1 h3),
         h_le_trans _ _ _ (monoton_oben le add h_add_mono h2 h4) hhi⟩

/-- Sharpness: exact means UNCHANGED. -/
theorem exakt_wandert_nicht {z : R} (h : fl z = z) :
    aussenLo fl nd z = z ∧ aussenHi fl nu z = z := by
  simp [aussenLo, aussenHi, h]

end Rundung

/-! ## Witnesses: the `Int` instance with exact arithmetic.

`fl = nd = nu = id` satisfies every premise (`Int.add_le_add` is the
monotonicity, `Int.le_refl` the neighbours, `Int.le_trans` the order),
so each lemma fires on concrete integers. -/

/-- Outward rounding over `Int` with exact arithmetic (nothing moves). -/
abbrev cLo : Int → Int :=
  aussenLo id id

/-- Outward rounding over `Int` with exact arithmetic (nothing moves). -/
abbrev cHi : Int → Int :=
  aussenHi id id

theorem huelle_haelt_zeuge (z : Int) : cLo z ≤ z ∧ z ≤ cHi z :=
  huelle_haelt (le := (· ≤ ·)) (fl := id) (nd := id) (nu := id)
    (h_le_refl := fun _ => Int.le_refl _)
    (h_nachbarn := fun _ => ⟨Int.le_refl _, Int.le_refl _⟩) z

theorem monoton_unten_zeuge {a x c y : Int} (h1 : a ≤ x) (h2 : c ≤ y) :
    a + c ≤ x + y :=
  monoton_unten (le := (· ≤ ·)) (add := (· + ·))
    (h_add_mono := fun _ _ _ _ g1 g2 => Int.add_le_add g1 g2) h1 h2

theorem monoton_oben_zeuge {x b y d : Int} (h1 : x ≤ b) (h2 : y ≤ d) :
    x + y ≤ b + d :=
  monoton_oben (le := (· ≤ ·)) (add := (· + ·))
    (h_add_mono := fun _ _ _ _ g1 g2 => Int.add_le_add g1 g2) h1 h2

theorem summe_liegt_in_der_gerechneten_schranke_zeuge
    {a x b c y d : Int} (h1 : a ≤ x) (h2 : x ≤ b) (h3 : c ≤ y)
    (h4 : y ≤ d) :
    cLo (a + c) ≤ x + y ∧ x + y ≤ cHi (b + d) :=
  summe_liegt_in_der_gerechneten_schranke (le := (· ≤ ·)) (add := (· + ·))
    (fl := id) (nd := id) (nu := id)
    (h_add_mono := fun _ _ _ _ g1 g2 => Int.add_le_add g1 g2)
    (h_le_trans := fun _ _ _ g1 g2 => Int.le_trans g1 g2)
    (h_le_refl := fun _ => Int.le_refl _)
    (h_nachbarn := fun _ => ⟨Int.le_refl _, Int.le_refl _⟩) h1 h2 h3 h4

theorem exakt_wandert_nicht_zeuge (z : Int) : cLo z = z ∧ cHi z = z :=
  exakt_wandert_nicht (fl := (id : Int → Int)) (nd := id) (nu := id)
    (h := rfl)

end Gabbro.Grammatik.IntervallAussen
