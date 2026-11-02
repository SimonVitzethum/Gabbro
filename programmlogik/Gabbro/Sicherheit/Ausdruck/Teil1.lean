/-
  Datei:      Gabbro/Sicherheit/Ausdruck.lean
  Gegenstand: **Der Sicherheitssatz fuer AUSDRUECKE** -- ein Ausdruck, den der Pruefer
              annimmt, wird in `Body.lean`s Semantik NIE `none`, und sein Wert hat die
              Gestalt, die der Pruefer ihm gerechnet hat.

  Angelegt 2026-09-09. **Die Frage, die dieser Ordner beantworten soll:**

  > Deckt die Grammatik samt ihren Paessen JEDEN Fehler ab, so dass der einzige Fehler,
  > den ein angenommenes Gabbro-Programm noch haben kann, die Logik des Schreibers ist?

  `Coverage.lean` beantwortet sie als KLASSIFIKATION: jede Form bekommt ein Urteil.
  Was dort NICHT steht, ist der SEMANTISCHE Satz -- dass ein angenommenes Programm im
  Modell an keiner Stelle stecken bleibt, die nicht `requires` oder `invariant` heisst.
  `Body.lean` hat den Begriff dafuer (`Outcome.stuck`, `eval … = none`), aber keinen
  Satz, der ihn fuer angenommene Programme AUSSCHLIESST. **Das ist der Satz, der hier
  anfaengt.** Er hat zwei Haelften; diese Datei ist die erste (Ausdruecke), die zweite
  steht in `Anweisung.lean`.

  WAS MODELLIERT WIRD
    Ein PRUEFER als Algorithmus, nicht als Relation: `schluss` rechnet zu einem Ausdruck
    die Gestalt (`Shape`) aus, die er tragen wird -- oder `none`, und `none` ist die
    ABSAGE des Pruefers. Er rechnet so, wie `LANGUAGE.md` §3 M1 es sagt: Bereiche werden
    durch die Arithmetik getragen (`M104`), ein Nenner muss die Null ausschliessen
    (`M102`), ein Index muss in `0 ..< count` liegen (`M103`), ein `match` findet nur
    Faelle, die der Typ erklaert (`D005`).

    Der Satz `schluss_sicher` sagt dann: liegt die Welt in ihrer Typisierung (`WF`) und
    liegen die Lokalen in ihrer (`WFL`), so liefert `eval` einen Wert dieser Gestalt.
    **Kein `none`** -- also keine Division durch null, kein Bitoperator auf einer
    negativen Zahl, keine Gestaltverwechslung, kein Index ausserhalb.

  QUELLSAETZE
    dokumente/LANGUAGE.md:677   -- "Every operation must stay inside the range of its
                                  result type; […] compile error, not a runtime check.
                                  Division and remainder demand a denominator whose range
                                  excludes zero."
    dokumente/SYNTAX.md:715    -- "M1 acts here and nowhere else"
    dokumente/SYNTAX.md:719    -- "`%` and `/` by `u32 in 0..n` are not writable"
    dokumente/SYNTAX.md:1027   -- "`match` is exhaustive -- there is no catch-all branch"
    programmlogik/Gabbro/Body.lean, `binop`  -- "A zero denominator gets the model STUCK",
                                  "A bit mask, over the NON-NEGATIVE integers and nowhere else"
    passlogik/Passlogik/Bereich.lean -- `add_korrekt`, `sub_korrekt`, `mul_korrekt`: die
                                  Ueberdeckung, hier NEU bewiesen, weil die beiden
                                  Lake-Projekte einander nicht importieren.

  ANGENOMMEN STATT BEWIESEN
    (S1) Die Typisierung der Welt ist je Traeger und Feld EINHEITLICH im Index:
         `Γ (.slot c k f) = Σ c f` fuer jedes `k` in `0 ..< count c`. So schreibt der
         Erzeuger `Γ` aus den Deklarationen; hier ist es die Praemisse `Deklariert`.
    (S2) Fuer `reaches`/`chain` muss das `via`-Feld an JEDEM Index eine Option tragen,
         nicht nur in `0 ..< count` -- `chase` folgt einem `present m` ohne
         Schranke. **Das ist ein FUND, kein Modellfehler:** `Shape.opt` traegt keinen
         Bereich, also ist `option index into T` im Modell ein Zeiger ohne Schranke.
         Siehe `Sicherheit.lean`, Fund 2.
    (S3) `wrapTo` liefert `.int` ohne Bereich. Dass `wrap b sg n` in `[0, 2^b)` bzw.
         `[-2^(b-1), 2^(b-1))` liegt, ist ein zweiter Satz und steht hier nicht.
    (S4) Division, remainder, shifts and bitwise operations carry the ranges
         `typen.rs` computes (`teile`, `rest`, `bitweise`, `schiebe` over
         `lo1/hi1/lo2/hi2`): the proof shows the value inside the computed
         interval, so an accepted expression neither gets stuck nor loses its
         range. What the model cannot name stays out: the machine width behind
         `ergebnis` (no width lives in `Shape`, Fund 1) and the mixed-form
         unknowns of `gemeinsame_form` (no width or signedness lives in `Shape`
         either -- a model range may then refuse where the checker stays
         silent, and that direction is booked, not built).
-/
module
public import Gabbro.Body
-- Umbrella import on purpose: the range proofs below use order, `tdiv`/`tmod`,
-- bitwise and `norm_cast` lemmas spread over a dozen Mathlib modules, and a wrong
-- guess at the module split costs a build cycle each. Oleans are cache-fetched,
-- so this costs load time, not build time. Narrowed later if measured slow.
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Order.Lattice
@[expose] public section


namespace Gabbro.Sicherheit

open Gabbro.Body

/-! ## 0. Intervalle -- das Stueck `Bereich.lean`, das hier gebraucht wird -/

def imin (a b : Int) : Int := if a ≤ b then a else b
def imax (a b : Int) : Int := if a ≤ b then b else a

theorem imin_le_left (a b : Int) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Int) : imin a b ≤ b := by unfold imin; split <;> omega
theorem le_imax_left (a b : Int) : a ≤ imax a b := by unfold imax; split <;> omega
theorem le_imax_right (a b : Int) : b ≤ imax a b := by unfold imax; split <;> omega

/-- Das Vier-Ecken-Produkt -- `mul_korrekt` aus `Bereich.lean`, hier als Hilfssatz. -/
theorem produkt_in_ecken (p q r s u v : Int) (hpu : p ≤ u) (huq : u ≤ q) (hrv : r ≤ v)
    (hvs : v ≤ s) :
    imin (imin (p*r) (p*s)) (imin (q*r) (q*s)) ≤ u*v
    ∧ u*v ≤ imax (imax (p*r) (p*s)) (imax (q*r) (q*s)) := by
  have hpv_qv : (p*v ≤ u*v ∧ u*v ≤ q*v) ∨ (q*v ≤ u*v ∧ u*v ≤ p*v) := by
    rcases Int.lt_or_le v 0 with hv | hv
    · right
      exact ⟨Int.mul_le_mul_of_nonpos_right huq (Int.le_of_lt hv),
             Int.mul_le_mul_of_nonpos_right hpu (Int.le_of_lt hv)⟩
    · left
      exact ⟨Int.mul_le_mul_of_nonneg_right hpu hv, Int.mul_le_mul_of_nonneg_right huq hv⟩
  have hp : (p*r ≤ p*v ∧ p*v ≤ p*s) ∨ (p*s ≤ p*v ∧ p*v ≤ p*r) := by
    rcases Int.lt_or_le p 0 with hp0 | hp0
    · right
      exact ⟨Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hp0) hvs,
             Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hp0) hrv⟩
    · left
      exact ⟨Int.mul_le_mul_of_nonneg_left hrv hp0, Int.mul_le_mul_of_nonneg_left hvs hp0⟩
  have hq : (q*r ≤ q*v ∧ q*v ≤ q*s) ∨ (q*s ≤ q*v ∧ q*v ≤ q*r) := by
    rcases Int.lt_or_le q 0 with hq0 | hq0
    · right
      exact ⟨Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hq0) hvs,
             Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hq0) hrv⟩
    · left
      exact ⟨Int.mul_le_mul_of_nonneg_left hrv hq0, Int.mul_le_mul_of_nonneg_left hvs hq0⟩
  have l1 := imin_le_left (imin (p*r) (p*s)) (imin (q*r) (q*s))
  have l2 := imin_le_right (imin (p*r) (p*s)) (imin (q*r) (q*s))
  have l3 := imin_le_left (p*r) (p*s)
  have l4 := imin_le_right (p*r) (p*s)
  have l5 := imin_le_left (q*r) (q*s)
  have l6 := imin_le_right (q*r) (q*s)
  have u1 := le_imax_left (imax (p*r) (p*s)) (imax (q*r) (q*s))
  have u2 := le_imax_right (imax (p*r) (p*s)) (imax (q*r) (q*s))
  have u3 := le_imax_left (p*r) (p*s)
  have u4 := le_imax_right (p*r) (p*s)
  have u5 := le_imax_left (q*r) (q*s)
  have u6 := le_imax_right (q*r) (q*s)
  rcases hpv_qv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hp with ⟨p1, p2⟩ | ⟨p1, p2⟩ <;>
    rcases hq with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> omega

/-! ## 0.5. Range formulas -- F4 mirrors `teile`, `rest`, `bitweise`, `schiebe`

    Each helper mirrors one function in `crates/gabbro-check/src/typen.rs` over bare
    bounds (`lo1/hi1/lo2/hi2`); `arith` below only calls them. Two things the checker
    knows never travel here: the machine width behind `ergebnis` (so no overflow
    flag and no full-width fallback -- a range that leaves every width is still a
    range) and the form agreement of `gemeinsame_form` (so no unknown on mixed
    widths -- `Shape` carries no width and no signedness to agree on). -/

/-- Below `c`, from both sides. -/
theorem le_imin {a b c : Int} (h1 : c ≤ a) (h2 : c ≤ b) : c ≤ imin a b := by
  unfold imin; split <;> omega

/-- Above `c`, from both sides. -/
theorem imax_le {a b c : Int} (h1 : a ≤ c) (h2 : b ≤ c) : imax a b ≤ c := by
  unfold imax; split <;> omega

/-- Truncated division is antitone in a positive denominator over a non-negative
    dividend. From the defining equation `q * y + r = x`: a quotient strictly above
    against a denominator at or above overshoots `x`. -/
theorem tdiv_anti_nonneg {x y₁ y₂ : Int} (hx : 0 ≤ x) (h1 : 0 < y₁) (h12 : y₁ ≤ y₂) :
    x.tdiv y₂ ≤ x.tdiv y₁ := by
  rcases le_or_gt (x.tdiv y₂) (x.tdiv y₁) with h | h
  · exact h
  · have hle : x.tdiv y₁ + 1 ≤ x.tdiv y₂ := by omega
    have e1 := Int.tdiv_mul_add_tmod x y₁
    have e2 := Int.tdiv_mul_add_tmod x y₂
    have r1nn : 0 ≤ x.tmod y₁ := Int.tmod_nonneg y₁ hx
    have r1lt : x.tmod y₁ < y₁ := Int.tmod_lt_of_pos x h1
    have h2 : 0 < y₂ := lt_of_lt_of_le h1 h12
    have r2nn : 0 ≤ x.tmod y₂ := Int.tmod_nonneg y₂ hx
    have q1nn : 0 ≤ x.tdiv y₁ := Int.tdiv_nonneg hx (le_of_lt h1)
    have s1 : x.tdiv y₁ * y₁ ≤ x.tdiv y₁ * y₂ :=
      Int.mul_le_mul_of_nonneg_left h12 q1nn
    have s2 : (x.tdiv y₁ + 1) * y₂ ≤ x.tdiv y₂ * y₂ :=
      Int.mul_le_mul_of_nonneg_right hle (le_of_lt h2)
    have hexpand : (x.tdiv y₁ + 1) * y₂ = x.tdiv y₁ * y₂ + y₂ := by ring
    omega

/-- ... and monotone the same way over a non-positive dividend -- by negation. -/
theorem tdiv_anti_neg {x y₁ y₂ : Int} (hx : x ≤ 0) (h1 : 0 < y₁) (h12 : y₁ ≤ y₂) :
    x.tdiv y₁ ≤ x.tdiv y₂ := by
  have hN := tdiv_anti_nonneg (show (0 : Int) ≤ -x by omega) h1 h12
  rw [Int.neg_tdiv, Int.neg_tdiv] at hN
  exact neg_le_neg_iff.mp hN

/-- The signed corners of `teile`. -/
def divEckenLo (lo1 hi1 lo2 hi2 : Int) : Int :=
  imin (imin (lo1.tdiv lo2) (lo1.tdiv hi2)) (imin (hi1.tdiv lo2) (hi1.tdiv hi2))

/-- ... the upper corners. -/
def divEckenHi (lo1 hi1 lo2 hi2 : Int) : Int :=
  imax (imax (lo1.tdiv lo2) (lo1.tdiv hi2)) (imax (hi1.tdiv lo2) (hi1.tdiv hi2))

/-- The four corners of `teile` over a positive denominator range: every `x/y` with
    `x` in `[lo1, hi1]` and `y` in `[lo2, hi2]` lies between the extremes of the four
    corner quotients. Which corner binds depends on the signs of the dividend ends;
    each link below is numerator monotonicity (`Int.tdiv_le_tdiv`) or denominator
    (anti-)monotonicity in the bound's own sign -- never in the value's. -/
theorem tdiv_vierecken (lo1 hi1 lo2 hi2 x y : Int)
    (hx1 : lo1 ≤ x) (hx2 : x ≤ hi1) (hy1 : lo2 ≤ y) (hy2 : y ≤ hi2) (hpos : 0 < lo2) :
    divEckenLo lo1 hi1 lo2 hi2 ≤ x.tdiv y ∧ x.tdiv y ≤ divEckenHi lo1 hi1 lo2 hi2 := by
  have hle : lo1 ≤ hi1 := le_trans hx1 hx2
  have hypos : (0 : Int) < y := lt_of_lt_of_le hpos hy1
  have hhi2pos : (0 : Int) < hi2 := lt_of_lt_of_le hpos (le_trans hy1 hy2)
  rcases le_or_gt 0 lo1 with hlo1 | hlo1
  · have hhi1nn : (0 : Int) ≤ hi1 := le_trans hlo1 hle
    have lv : lo1.tdiv hi2 ≤ x.tdiv y :=
      le_trans (tdiv_anti_nonneg hlo1 hypos hy2) (Int.tdiv_le_tdiv hypos hx1)
    have uv : x.tdiv y ≤ hi1.tdiv lo2 :=
      le_trans (Int.tdiv_le_tdiv hypos hx2) (tdiv_anti_nonneg hhi1nn hpos hy1)
    simp only [divEckenLo, divEckenHi]
    exact ⟨le_trans (imin_le_left _ _) (le_trans (imin_le_right _ _) lv),
      le_trans uv (le_trans (le_imax_left _ _) (le_imax_right _ _))⟩
  · rcases le_or_gt 0 hi1 with hhi1 | hhi1
    · have hlo10 : lo1 ≤ 0 := le_of_lt hlo1
      have lv : lo1.tdiv lo2 ≤ x.tdiv y :=
        le_trans (tdiv_anti_neg hlo10 hpos hy1) (Int.tdiv_le_tdiv hypos hx1)
      have uv : x.tdiv y ≤ hi1.tdiv lo2 :=
        le_trans (Int.tdiv_le_tdiv hypos hx2) (tdiv_anti_nonneg hhi1 hpos hy1)
      simp only [divEckenLo, divEckenHi]
      exact ⟨le_trans (imin_le_left _ _) (le_trans (imin_le_left _ _) lv),
        le_trans uv (le_trans (le_imax_left _ _) (le_imax_right _ _))⟩
    · have hhi10 : hi1 ≤ 0 := le_of_lt hhi1
      have hlo10 : lo1 ≤ 0 := le_trans hle hhi10
      have lv : lo1.tdiv lo2 ≤ x.tdiv y :=
        le_trans (tdiv_anti_neg hlo10 hpos hy1) (Int.tdiv_le_tdiv hypos hx1)
      have uv : x.tdiv y ≤ hi1.tdiv hi2 :=
        le_trans (Int.tdiv_le_tdiv hypos hx2) (tdiv_anti_neg hhi10 hypos hy2)
      simp only [divEckenLo, divEckenHi]
      exact ⟨le_trans (imin_le_left _ _) (le_trans (imin_le_left _ _) lv),
        le_trans uv (le_trans (le_imax_right _ _) (le_imax_right _ _))⟩

/-- Negation swaps the extremes -- the negative-denominator reduction of `teile`
    reads the four corners through this. -/
theorem imin_neg (a b : Int) : imin (-a) (-b) = -(imax a b) := by
  rcases le_or_gt a b with h | h
  · rcases eq_or_lt_of_le h with rfl | hlt
    · simp only [imin, Std.le_refl, ↓reduceIte, imax]
    · have hF : ¬ -a ≤ -b := by omega
      have hT : a ≤ b := le_of_lt hlt
      simp only [imin, imax, if_neg hF, if_pos hT]
  · have hT : -a ≤ -b := by omega
    have hF : ¬ a ≤ b := by omega
    simp only [imin, imax, if_pos hT, if_neg hF]

/-- ... and back. -/
theorem imax_neg (a b : Int) : imax (-a) (-b) = -(imin a b) := by
  rcases le_or_gt a b with h | h
  · rcases eq_or_lt_of_le h with rfl | hlt
    · simp only [imax, Std.le_refl, ↓reduceIte, imin]
    · have hF : ¬ -a ≤ -b := by omega
      have hT : a ≤ b := le_of_lt hlt
      simp only [imin, imax, if_neg hF, if_pos hT]
  · have hT : -a ≤ -b := by omega
    have hF : ¬ a ≤ b := by omega
    simp only [imin, imax, if_pos hT, if_neg hF]

/-- The two orders of four corners coincide -- the negated denominator range lists
    them swapped, and the mirror bound has to meet the proved one. -/
theorem imax_swap4 (A B C D : Int) :
    imax (imax A B) (imax C D) ≤ imax (imax B A) (imax D C) :=
  imax_le
    (imax_le (le_trans (le_imax_right _ _) (le_imax_left _ _))
      (le_trans (le_imax_left _ _) (le_imax_left _ _)))
    (imax_le (le_trans (le_imax_right _ _) (le_imax_right _ _))
      (le_trans (le_imax_left _ _) (le_imax_right _ _)))

/-- ... and below. -/
theorem imin_swap4 (A B C D : Int) :
    imin (imin B A) (imin D C) ≤ imin (imin A B) (imin C D) :=
  le_imin
    (le_imin (le_trans (imin_le_left _ _) (imin_le_right _ _))
      (le_trans (imin_le_left _ _) (imin_le_left _ _)))
    (le_imin (le_trans (imin_le_right _ _) (imin_le_right _ _))
      (le_trans (imin_le_right _ _) (imin_le_left _ _)))

/-- `max |lo2| |hi2| - 1` without absolute values: `max hi2 (-lo2) - 1` -- the signed
    arm of `rest`. -/
def remSchranke (lo2 hi2 : Int) : Int := imax hi2 (-lo2) - 1

/-- The signed arm of `rest`: against a positive denominator the remainder lies
    between `±Schranke`. The sign rides on the dividend (`Int.neg_tmod`); the modulus
    bounds are `Int.tmod_nonneg` and `Int.tmod_lt_of_pos`. -/
theorem trem_pos (y x : Int) (lo2 hi2 : Int) (hypos : 0 < y)
    (hS : y ≤ imax hi2 (-lo2)) :
    -(remSchranke lo2 hi2) ≤ x.tmod y ∧ x.tmod y ≤ remSchranke lo2 hi2 := by
  have hS1 : y ≤ remSchranke lo2 hi2 + 1 := by simp only [remSchranke]; omega
  rcases le_or_gt 0 x with hx0 | hx0
  · have h1 : (0 : Int) ≤ x.tmod y := Int.tmod_nonneg y hx0
    have h2 : x.tmod y < y := Int.tmod_lt_of_pos x hypos
    exact ⟨by omega, by omega⟩
  · have hxN : (0 : Int) < -x := by omega
    have h1 : (0 : Int) ≤ (-x).tmod y := Int.tmod_nonneg y (le_of_lt hxN)
    have h2 : (-x).tmod y < y := Int.tmod_lt_of_pos (-x) hypos
    have hN : x.tmod y = -((-x).tmod y) := by rw [Int.neg_tmod]; simp only [neg_neg]
    rw [hN]
    exact ⟨by omega, by omega⟩

/-- `maske` in `typen.rs`: the smallest `2^k - 1` covering `n` -- the `bor`/`bxor`
    bound. `0` covers `0`; otherwise the previous mask stands while it covers, else
    one bit grows. -/
def maskeNat : Nat → Nat
  | 0 => 0
  | (n + 1) => if n + 1 ≤ maskeNat n then maskeNat n else 2 * maskeNat n + 1

/-- Every value fits under its mask. -/
theorem maskeNat_ge (n : Nat) : n ≤ maskeNat n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [maskeNat]
    split
    · rename_i h; exact h
    · rename_i h; omega

/-- Every mask plus one is a power of two. -/
theorem maskeNat_pow2 (n : Nat) : ∃ k, maskeNat n + 1 = 2 ^ k := by
  induction n with
  | zero => exact ⟨0, by simp only [maskeNat, zero_add, pow_zero]⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    simp only [maskeNat]
    split
    · rename_i h; exact ⟨k, hk⟩
    · rename_i h
      refine ⟨k + 1, ?_⟩
      have hk2 : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
        have s : k + 1 = k.succ := by omega
        rw [s, Nat.pow_succ]
        exact Nat.mul_comm _ _
      omega

/-- ... over `Int`, with `0` for non-positive inputs (there `toNat` is `0`). -/
def maske (w : Int) : Int := ((maskeNat w.toNat : Nat) : Int)

/-- The mask covers. -/
theorem maske_ge (w : Int) : w ≤ maske w := by
  unfold maske
  cases w with
  | negSucc n =>
    have h0 : (Int.negSucc n).toNat = 0 := Int.toNat_negSucc n
    simp only [maskeNat, h0, Nat.cast_zero]
    omega
  | ofNat n =>
    have h3 : (Int.ofNat n).toNat = n := rfl
    rw [h3]
    have h : n ≤ maskeNat n := maskeNat_ge n
    have h2 : ((n : Nat) : Int) ≤ ((maskeNat n : Nat) : Int) := by exact_mod_cast h
    exact h2

/-- `2^m ≤ 2^n` over `Int` -- shift counts grow with the count (`schiebe`). -/
theorem zwei_pow_le {m n : Nat} (h : m ≤ n) : (2 : Int) ^ m ≤ 2 ^ n := by
  have h' : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (show (2 : Nat) > 0 by decide) h
  exact_mod_cast h'

/-! ## 1. Die Typisierung der LOKALEN, neben der der Welt aus `Body.lean` -/

/-- Die Gestalt jedes lokalen Namens -- was `let` und die Parameter erklaert haben.
    `none` heisst: der Name traegt keine Gestalt, und der Pruefer liest ihn dann nicht. -/
abbrev Lokal := String → Option Shape

/-- Die Lokalen liegen in ihrer Typisierung -- das Gegenstueck zu `WF` fuer `local'`. -/
def WFL (Δ : Lokal) (β : Binding) : Prop :=
  ∀ n sh, Δ n = some sh → (β n).hasShape sh = true

/-- Die Gestalt je Traeger und SLOTFELD, einheitlich im Index (S1), und je Traeger die
    `count`-Schranke. So steht es in der Deklaration; `Γ` ist daraus abgeleitet. -/
structure Deklaration where
  slot   : String → String → Option Shape
  count  : String → Int
  /-- Felder eines Verbunds oder `format` (`.field c f`). -/
  feld   : String → String → Option Shape
  /-- `static`s und `atomic`s (`.global g`). -/
  global : String → Option Shape

/-- **(S1)** `Γ` IST die Deklaration: an jedem Index innerhalb der Schranke traegt das
    Slotfeld die erklaerte Gestalt; Feld und Global ebenso. -/
def Deklariert (D : Deklaration) (Γ : Typing) : Prop :=
  (∀ c k f, 0 ≤ k → k < D.count c → Γ (.slot c k f) = D.slot c f)
  ∧ (∀ c f, Γ (.field c f) = D.feld c f)
  ∧ (∀ g, Γ (.global g) = D.global g)

/-! ## 2. Der Pruefer als ALGORITHMUS -- was M1 an einem Ausdruck rechnet

    `schluss` gibt `none` zurueck, wo der Pruefer ABSAGT. Jede Absage traegt in der
    Bemerkung daneben die Kennung des Passes, die sie in `gabbro-check` traegt. -/

/-- Ist die Gestalt eine Zahl -- und mit welchem Bereich? `.int` ist die Zahl ohne
    erklaerten Bereich (`u64` ohne `in`, Ergebnis einer Division, …). -/
def zahl : Shape → Option (Option (Int × Int))
  | .int => some none
  | .intIn lo hi => some (some (lo, hi))
  | _ => none

/-- Der Bereich einer Zahlgestalt, wo einer steht. -/
def bereich : Shape → Option (Int × Int)
  | .intIn lo hi => some (lo, hi)
  | _ => none

/-- Die Arithmetik des Passes ueber zwei Zahlgestalten: mit Bereich, wenn beide einen
    tragen (`M104` rechnet dann das Ergebnisintervall), sonst `.int`. -/
def arith (op : BinOp) (a b : Shape) : Option Shape :=
  match zahl a, zahl b with
  | some (some (lo1, hi1)), some (some (lo2, hi2)) =>
      match op with
      | .add => some (.intIn (lo1 + lo2) (hi1 + hi2))
      | .sub => some (.intIn (lo1 - hi2) (hi1 - lo2))
      | .mul => some (.intIn (imin (imin (lo1*lo2) (lo1*hi2)) (imin (hi1*lo2) (hi1*hi2)))
                             (imax (imax (lo1*lo2) (lo1*hi2)) (imax (hi1*lo2) (hi1*hi2))))
      -- `M102`: der Nenner schliesst die Null aus, oder der Pass sagt ab.
      -- Inside: `teile` divides the edges over a non-negative dividend and a
      -- positive denominator, else the four corners; `rest` is `0 .. min` or
      -- the symmetric bound. `Int.tdiv`/`Int.tmod` truncate like the machine.
      | .div =>
          if 0 < lo2 ∨ hi2 < 0 then
            if 0 ≤ lo1 ∧ 0 < lo2 then some (.intIn (lo1.tdiv hi2) (hi1.tdiv lo2))
            else some (.intIn (divEckenLo lo1 hi1 lo2 hi2) (divEckenHi lo1 hi1 lo2 hi2))
          else none
      | .rem =>
          if 0 < lo2 ∨ hi2 < 0 then
            if 0 ≤ lo1 ∧ 0 < lo2 then some (.intIn 0 (imin (hi2 - 1) hi1))
            else some (.intIn (-(remSchranke lo2 hi2)) (remSchranke lo2 hi2))
          else none
      -- `M137`/`M104`: Bitoperatoren und Schiebungen nur ueber NICHTNEGATIVEN Bereichen.
      -- Inside: `bitweise` (`Und` through the minimum, `Oder`/`Xor` through the mask)
      -- and the four corners of the shifts (`schiebe_links`, `schiebe_rechts`).
      -- No width travels here, so no overflow flag either (Fund 1).
      | .band =>
          if 0 ≤ lo1 ∧ 0 ≤ lo2 then some (.intIn 0 (imin hi1 hi2)) else none
      | .bor | .bxor =>
          if 0 ≤ lo1 ∧ 0 ≤ lo2 then some (.intIn 0 (maske (imax hi1 hi2))) else none
      | .shl =>
          if 0 ≤ lo1 ∧ 0 ≤ lo2 then
            some (.intIn (lo1 * 2 ^ lo2.toNat) (hi1 * 2 ^ hi2.toNat))
          else none
      | .shr =>
          if 0 ≤ lo1 ∧ 0 ≤ lo2 then
            some (.intIn (lo1.tdiv (2 ^ hi2.toNat)) (hi1.tdiv (2 ^ lo2.toNat)))
          else none
      | _ => none
  -- Ohne Bereich auf einer Seite: Addition und Co. bleiben Zahlen; Division, Rest und
  -- Bits brauchen einen Bereich, sonst weiss der Pass nichts ueber den Nenner (`M102`).
  | some _, some _ =>
      match op with
      | .add | .sub | .mul => some .int
      | _ => none
  | _, _ => none

/-- Der Vergleich: Zahlen liefern `bool`; `==`/`!=` stehen ueber ALLEN Werten. -/
def vergleich (op : BinOp) (a b : Shape) : Option Shape :=
  match op with
  | .eq | .ne => some .bool
  | .lt | .le | .gt | .ge => match zahl a, zahl b with
      | some _, some _ => some .bool
      | _, _ => none
  | .and | .or => match a, b with
      | .bool, .bool => some .bool
      | _, _ => none
  | _ => none

/-- Ein `tagged`-Fall, den der Typ erklaert, mit einer Nutzlast, die passt (`D005`, `M106`). -/
def fallPasst (cases : List (String × Option (Option (Int × Int)))) (t : String)
    (nutz : Option Shape) : Bool :=
  cases.any fun c =>
    c.1 == t &&
    match c.2, nutz with
    | none, none => true
    | some none, some sh => (zahl sh).isSome
    | some (some (lo, hi)), some (.intIn lo' hi') => decide (lo ≤ lo' ∧ hi' ≤ hi)
    | _, _ => false

end Gabbro.Sicherheit
