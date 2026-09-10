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
    ABSAGE des Pruefers. Er rechnet so, wie `SPRACHE.md` §3 M1 es sagt: Bereiche werden
    durch die Arithmetik getragen (`M104`), ein Nenner muss die Null ausschliessen
    (`M102`), ein Index muss in `0 ..< count` liegen (`M103`), ein `match` findet nur
    Faelle, die der Typ erklaert (`D005`).

    Der Satz `schluss_sicher` sagt dann: liegt die Welt in ihrer Typisierung (`WF`) und
    liegen die Lokalen in ihrer (`WFL`), so liefert `eval` einen Wert dieser Gestalt.
    **Kein `none`** -- also keine Division durch null, kein Bitoperator auf einer
    negativen Zahl, keine Gestaltverwechslung, kein Index ausserhalb.

  QUELLSAETZE
    dokumente/SPRACHE.md:677   -- "Every operation must stay inside the range of its
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
import Gabbro.Body
-- Umbrella import on purpose: the range proofs below use order, `tdiv`/`tmod`,
-- bitwise and `norm_cast` lemmas spread over a dozen Mathlib modules, and a wrong
-- guess at the module split costs a build cycle each. Oleans are cache-fetched,
-- so this costs load time, not build time. Narrowed later if measured slow.
import Mathlib

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
    · simp [imin, imax]
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
    · simp [imin, imax]
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
    have hN : x.tmod y = -((-x).tmod y) := by rw [Int.neg_tmod]; simp
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
  | zero => exact ⟨0, by simp [maskeNat]⟩
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

/-- **Der Pruefer.** `schluss D Δ e = some sh`: der Pass nimmt `e` an und gibt ihm die
    Gestalt `sh`; `none` ist die Absage. -/
def schluss (D : Deklaration) : Lokal → Expr → Option Shape
  | _, .lit v =>
      -- Ein Literal traegt seine eigene Gestalt: eine Zahl den Punktbereich `[n, n]`.
      match v with
      | .int n => some (.intIn n n)
      | .bool _ => some .bool
      | .absent => some .opt
      | .present _ => some .opt
      | .reason _ => none
      | .tagged _ _ => none
  | Δ, .name n => Δ n
  | _, .global g => D.global g
  | Δ, .place c i f =>
      -- `M103`: der Index liegt in `0 ..< count`, oder der Pass sagt ab.
      match schluss D Δ i with
      | some (.intIn lo hi) => if 0 ≤ lo ∧ hi < D.count c then D.slot c f else none
      | _ => none
  | _, .fieldOf c f => D.feld c f
  | Δ, .un .not a =>
      match schluss D Δ a with
      | some .bool => some .bool
      | _ => none
  | Δ, .un .neg a =>
      match schluss D Δ a with
      | some .int => some .int
      | some (.intIn lo hi) => some (.intIn (-hi) (-lo))
      | _ => none
  | Δ, .bin op a b =>
      match schluss D Δ a, schluss D Δ b with
      | some sa, some sb =>
          match arith op sa sb with
          | some sh => some sh
          | none => vergleich op sa sb
      | _, _ => none
  | Δ, .someOf a =>
      match schluss D Δ a with
      | some sh => if (zahl sh).isSome then some .opt else none
      | none => none
  | Δ, .forallSlots v n b =>
      -- Der Binder traegt den Indexbereich der Domaene (`slots of`: `0 ..< count`).
      match schluss D (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m) b with
      | some .bool => some .bool
      | _ => none
  | Δ, .existsSlots v n b =>
      match schluss D (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m) b with
      | some .bool => some .bool
      | _ => none
  | Δ, .reaches c a z via _ =>
      -- (S2): das `via`-Feld ist an jedem Index eine Option, sonst Absage.
      match schluss D Δ a, schluss D Δ z, D.slot c via with
      | some sa, some sz, some .opt => if (zahl sa).isSome ∧ (zahl sz).isSome then some .bool else none
      | _, _, _ => none
  | Δ, .chainFrom c h x via _ =>
      match schluss D Δ h, schluss D Δ x, D.slot c via with
      | some .opt, some sx, some .opt => if (zahl sx).isSome then some .bool else none
      | _, _, _ => none
  | _, .hasShape _ _ => some .bool
  | Δ, .wrapTo _ _ a =>
      match schluss D Δ a with
      | some sh => if (zahl sh).isSome then some .int else none
      | none => none
  | _, .tagOf _ none => none
  | _, .tagOf _ (some _) => none
  -- **Ein `tagged`-Wert ohne Zieltyp hat keine Gestalt** -- `Coverage.lean` nennt die
  -- Form `constructedValue` und sagt sie ab; der Pruefer kennt den Typ nur aus dem ZIEL
  -- (`M106`), und ein Ausdruck allein hat keines. Hier ebenso: `none`. Die Ableitung
  -- gegen ein Ziel steht in `Anweisung.lean` (`fallPasst`).

/-- `Some` against the target option's payload bound (F10, `M101`): with no target any
    number passes, as before; with `(lo, hi)` only a ranged payload inside it does.
    `gift/170` (`Some(8)` on `count 8`) is refused here instead of flowing on. The
    bound lives at the use site, so `schluss` above does not thread it -- the carrier
    `schlussMitZiel` does, and wiring it into `pruefe` is its own step. -/
def somePasst : Option (Int × Int) → Shape → Option Shape
  | none, sh => if (zahl sh).isSome then some .opt else none
  | some (lo, hi), sh =>
    match sh with
    | .intIn lo' hi' => if lo ≤ lo' ∧ hi' ≤ hi then some .opt else none
    | _ => none

/-- The checker with the option target bound carried into `someOf`: every other form
    delegates to `schluss`, so the two can never drift apart -- and the safety proof
    below reuses `schluss_sicher` arm by arm for the same reason. -/
def schlussMitZiel (D : Deklaration) (ziel : Option (Int × Int)) : Lokal → Expr → Option Shape
  | Δ, .someOf a =>
      match schluss D Δ a with
      | some sh => somePasst ziel sh
      | none => none
  | Δ, e => schluss D Δ e

/-! ## 3. Der Satz -- ein angenommener Ausdruck wird nie `none`, und sein Wert passt -/

/-- **(S2) als Praemisse:** das `via`-Feld ist an JEDEM Index option-gestaltig. -/
def KettenWohlgeformt (D : Deklaration) (σ : World) : Prop :=
  ∀ c via k, D.slot c via = some .opt → (σ (.slot c k via)).hasShape .opt = true

theorem zahl_some_int {sh : Shape} {v : Value} (hz : (zahl sh).isSome = true)
    (hv : v.hasShape sh = true) : ∃ n, v = .int n := by
  cases sh <;> simp [zahl] at hz
  · exact Value.hasShape_int_true v hv
  · obtain ⟨n, hn, _⟩ := Value.hasShape_intIn_true v _ _ hv; exact ⟨n, hn⟩

theorem zahl_some_of_zahl {sh : Shape} {r : Option (Int × Int)} (h : zahl sh = some r) :
    (zahl sh).isSome = true := by rw [h]; rfl

theorem bereich_of_zahl {sh : Shape} {lo hi : Int} (h : zahl sh = some (some (lo, hi))) :
    sh = .intIn lo hi := by
  cases sh <;> simp [zahl] at h
  obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl

theorem int_of_zahl_none {sh : Shape} (h : zahl sh = some none) : sh = .int := by
  cases sh <;> simp [zahl] at h; rfl

/-- `allBelow` ueber einer Funktion, die immer einen `bool` liefert, liefert einen `bool`. -/
theorem allBelow_bool (f : Nat → Option Value) :
    ∀ n, (∀ k, k < n → ∃ b, f k = some (.bool b)) → ∃ b, allBelow f n = some (.bool b) := by
  intro n
  rw [allBelow_eq]
  induction n with
  | zero => intro _; exact ⟨true, rfl⟩
  | succ n ih =>
      intro hf
      obtain ⟨a, ha⟩ := ih (fun k hk => hf k (Nat.lt_succ_of_lt hk))
      obtain ⟨b, hb⟩ := hf n (Nat.lt_succ_self n)
      exact ⟨a && b, by simp [allBelowImpl, ha, hb]⟩

theorem anyBelow_bool (f : Nat → Option Value) :
    ∀ n, (∀ k, k < n → ∃ b, f k = some (.bool b)) → ∃ b, anyBelow f n = some (.bool b) := by
  intro n
  rw [anyBelow_eq]
  induction n with
  | zero => intro _; exact ⟨false, rfl⟩
  | succ n ih =>
      intro hf
      obtain ⟨a, ha⟩ := ih (fun k hk => hf k (Nat.lt_succ_of_lt hk))
      obtain ⟨b, hb⟩ := hf n (Nat.lt_succ_self n)
      exact ⟨a || b, by simp [anyBelowImpl, ha, hb]⟩

/-- `chase` ueber wohlgeformten Ketten liefert einen `bool` -- mit jedem Treibstoff. -/
theorem chase_bool (σ : World) (c via : String) (bis : Int)
    (hk : ∀ k, (σ (.slot c k via)).hasShape .opt = true) :
    ∀ n k, ∃ b, chase σ c via bis k n = some (.bool b) := by
  intro n
  rw [chase_eq]
  induction n with
  | zero => intro k; exact ⟨_, rfl⟩
  | succ n ih =>
      intro k
      simp only [chaseImpl]
      split
      · exact ⟨true, rfl⟩
      · rcases Value.hasShape_opt_true _ (hk k) with h | ⟨m, h⟩
        · rw [h]; exact ⟨false, rfl⟩
        · rw [h]; exact ih m

/-- **Der Rumpf eines Quantors**: unter dem Binder mit dem Indexbereich `0 ..< n` liefert
    er fuer jeden GERUFENEN Index einen `bool`. Herausgezogen, weil `forall` und `exists`
    denselben Schritt brauchen. -/
theorem quant_rumpf (D : Deklaration) (Γ : Typing) {b : Expr}
    (ih : ∀ (Δ : Lokal) (s : State) (sh : Shape), WF Γ s.world → WFL Δ s.local' →
        KettenWohlgeformt D s.world → schluss D Δ b = some sh →
        ∃ v, eval s b = some v ∧ v.hasShape sh = true)
    (Δ : Lokal) (s : State) (n : Int) {v : String}
    (hw : WF Γ s.world) (hl : WFL Δ s.local') (hk : KettenWohlgeformt D s.world)
    (hb : schluss D (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m) b = some .bool) :
    ∀ k : Nat, k < n.toNat →
      ∃ t, eval { s with local' := bindLocal s.local' v (.int k) } b = some (.bool t) := by
  intro k hkn
  have hl' : WFL (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m)
      (bindLocal s.local' v (.int k)) := by
    intro m sh hm
    by_cases hmv : m = v
    · subst hmv; simp at hm; subst hm
      simp [Value.hasShape]
      omega
    · simp [hmv] at hm; simpa [bindLocal, hmv] using hl m sh hm
  obtain ⟨t, ht, hts⟩ := ih _ ⟨s.world, bindLocal s.local' v (.int k)⟩ _ hw hl' hk hb
  obtain ⟨tb, rfl⟩ := Value.hasShape_bool_true t hts
  exact ⟨tb, ht⟩

/-- Der Sicherheitssatz fuer Ausdruecke. **BEWEIST NICHT**, dass der Pruefer in
    `gabbro-check` dasselbe rechnet wie `schluss` -- das ist die Naht (`W16`), und sie
    steht in keiner Zeile hier. Er beweist: WENN ein Pruefer so rechnet, DANN bleibt kein
    angenommener Ausdruck stecken. -/
theorem schluss_sicher (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ) :
    ∀ (e : Expr) (Δ : Lokal) (s : State) (sh : Shape),
      WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world →
      schluss D Δ e = some sh →
      ∃ v, eval s e = some v ∧ v.hasShape sh = true
  | .lit v, Δ, s, sh => by
      intro _ _ _ h
      cases v <;> simp [schluss] at h <;> subst h
      · exact ⟨_, rfl, by simp [Value.hasShape]⟩
      · exact ⟨_, rfl, by simp [Value.hasShape]⟩
      · exact ⟨_, rfl, by simp [Value.hasShape]⟩
      · exact ⟨_, rfl, by simp [Value.hasShape]⟩
  | .name n, Δ, s, sh => by
      intro _ hl _ h
      exact ⟨_, rfl, hl n sh h⟩
  | .global g, Δ, s, sh => by
      intro hw _ _ h
      refine ⟨_, rfl, hw _ sh ?_⟩
      rw [hD.2.2 g]; exact h
  | .place c i f, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD i
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i lo hi hi'
        split at h
        · rename_i hb
          obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk hi'
          obtain ⟨k, hk', hlo, hhi⟩ := Value.hasShape_intIn_true v lo hi hvs
          subst hk'
          refine ⟨_, ?_, hw (.slot c k f) sh ?_⟩
          · simp [eval, hv]
          · rw [hD.1 c k f (by omega) (by omega)]; exact h
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .fieldOf c f, Δ, s, sh => by
      intro hw _ _ h
      refine ⟨_, rfl, hw _ sh ?_⟩
      rw [hD.2.1 c f]; exact h
  | .un op a, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD a
      intro hw hl hk h
      cases op with
      | not =>
          simp only [schluss] at h
          split at h
          · rename_i ha
            obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
            obtain ⟨b, rfl⟩ := Value.hasShape_bool_true v hvs
            cases h
            simp [eval, hv, unop, Value.hasShape]
          · exact absurd h (by simp)
      | neg =>
          simp only [schluss] at h
          split at h
          · rename_i ha
            obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
            obtain ⟨n, rfl⟩ := Value.hasShape_int_true v hvs
            cases h
            simp [eval, hv, unop, Value.hasShape]
          · rename_i lo hi ha
            obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
            obtain ⟨n, rfl, h1, h2⟩ := Value.hasShape_intIn_true v lo hi hvs
            cases h
            simp [eval, hv, unop, Value.hasShape]; omega
          · exact absurd h (by simp)
  | .bin op a b, Δ, s, sh => by
      have iha := schluss_sicher D Γ hD a
      have ihb := schluss_sicher D Γ hD b
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i sa sb ha hb
        obtain ⟨va, hva, hvas⟩ := iha Δ s _ hw hl hk ha
        obtain ⟨vb, hvb, hvbs⟩ := ihb Δ s _ hw hl hk hb
        -- Zwei Faelle: Arithmetik oder Vergleich.
        split at h
        · -- Arithmetik
          rename_i sh' harith
          cases h
          unfold arith at harith
          split at harith
          · -- beide mit Bereich: `M104` rechnet das Intervall
            rename_i lo1 hi1 lo2 hi2 hz1 hz2
            have ea := bereich_of_zahl hz1; have eb := bereich_of_zahl hz2
            subst ea; subst eb
            obtain ⟨x, rfl, hx1, hx2⟩ := Value.hasShape_intIn_true va lo1 hi1 hvas
            obtain ⟨y, rfl, hy1, hy2⟩ := Value.hasShape_intIn_true vb lo2 hi2 hvbs
            cases op with
            | add => cases harith; simp [eval, hva, hvb, binop, Value.hasShape]; omega
            | sub => cases harith; simp [eval, hva, hvb, binop, Value.hasShape]; omega
            | mul =>
                cases harith
                simp only [eval, hva, hvb, binop, Value.hasShape, Option.some.injEq,
                  exists_eq_left', decide_eq_true_eq]
                exact produkt_in_ecken lo1 hi1 lo2 hi2 x y hx1 hx2 hy1 hy2
            | div =>
                dsimp only at harith
                split at harith
                · rename_i hc
                  split at harith
                  · rename_i hs
                    cases harith
                    obtain ⟨hs1, hs2⟩ := hs
                    have hy : y ≠ 0 := by omega
                    have hLo : lo1.tdiv hi2 ≤ x.tdiv y :=
                      le_trans (tdiv_anti_nonneg hs1 (lt_of_lt_of_le hs2 hy1) hy2)
                        (Int.tdiv_le_tdiv (lt_of_lt_of_le hs2 hy1) hx1)
                    have hHi : x.tdiv y ≤ hi1.tdiv lo2 :=
                      le_trans (Int.tdiv_le_tdiv (lt_of_lt_of_le hs2 hy1) hx2)
                        (tdiv_anti_nonneg (le_trans hs1 (le_trans hx1 hx2)) hs2 hy1)
                    simp only [eval, hva, hvb, binop, hy, ite_false, Value.hasShape,
                      Option.some.injEq, exists_eq_left', decide_eq_true_eq]
                    exact ⟨hLo, hHi⟩
                  · rename_i hs
                    cases harith
                    have hy : y ≠ 0 := by omega
                    rcases hc with hc1 | hc2
                    · obtain ⟨hlo, hhi⟩ :=
                        tdiv_vierecken lo1 hi1 lo2 hi2 x y hx1 hx2 hy1 hy2 hc1
                      simp only [eval, hva, hvb, binop, hy, ite_false, Value.hasShape,
                        Option.some.injEq, exists_eq_left', decide_eq_true_eq]
                      exact ⟨hlo, hhi⟩
                    · have hyN : (0 : Int) < -y := by omega
                      have hmem1 : -hi2 ≤ -y := by omega
                      have hmem2 : -y ≤ -lo2 := by omega
                      have hpos : (0 : Int) < -hi2 := by omega
                      obtain ⟨hlo', hhi'⟩ :=
                        tdiv_vierecken lo1 hi1 (-hi2) (-lo2) x (-y) hx1 hx2 hmem1 hmem2 hpos
                      have e1 : lo1.tdiv lo2 = -(lo1.tdiv (-lo2)) := by
                        have h := Int.tdiv_neg lo1 (-lo2)
                        rwa [Int.neg_neg] at h
                      have e2 : lo1.tdiv hi2 = -(lo1.tdiv (-hi2)) := by
                        have h := Int.tdiv_neg lo1 (-hi2)
                        rwa [Int.neg_neg] at h
                      have e3 : hi1.tdiv lo2 = -(hi1.tdiv (-lo2)) := by
                        have h := Int.tdiv_neg hi1 (-lo2)
                        rwa [Int.neg_neg] at h
                      have e4 : hi1.tdiv hi2 = -(hi1.tdiv (-hi2)) := by
                        have h := Int.tdiv_neg hi1 (-hi2)
                        rwa [Int.neg_neg] at h
                      have ev : x.tdiv y = -(x.tdiv (-y)) := by
                        have h := Int.tdiv_neg x (-y)
                        rwa [Int.neg_neg] at h
                      have hLo : divEckenLo lo1 hi1 lo2 hi2 ≤ x.tdiv y := by
                        simp only [divEckenLo]
                        rw [e1, e2, e3, e4, ev, imin_neg, imin_neg, imin_neg]
                        exact neg_le_neg_iff.mpr (le_trans hhi' (imax_swap4 _ _ _ _))
                      have hHi : x.tdiv y ≤ divEckenHi lo1 hi1 lo2 hi2 := by
                        simp only [divEckenHi]
                        rw [e1, e2, e3, e4, ev, imax_neg, imax_neg, imax_neg]
                        exact neg_le_neg_iff.mpr (le_trans (imin_swap4 _ _ _ _) hlo')
                      simp only [eval, hva, hvb, binop, hy, ite_false, Value.hasShape,
                        Option.some.injEq, exists_eq_left', decide_eq_true_eq]
                      exact ⟨hLo, hHi⟩
                · cases harith
            | rem =>
                dsimp only at harith
                split at harith
                · rename_i hc
                  split at harith
                  · rename_i hs
                    cases harith
                    obtain ⟨hs1, hs2⟩ := hs
                    have hy : y ≠ 0 := by omega
                    have hx0 : (0 : Int) ≤ x := le_trans hs1 hx1
                    have hypos : (0 : Int) < y := lt_of_lt_of_le hs2 hy1
                    have e1 := Int.tdiv_mul_add_tmod x y
                    have qnn : (0 : Int) ≤ x.tdiv y := Int.tdiv_nonneg hx0 (le_of_lt hypos)
                    have qy : (0 : Int) ≤ x.tdiv y * y := Int.mul_nonneg qnn (le_of_lt hypos)
                    have hrx : x.tmod y ≤ x := by omega
                    have hlt : x.tmod y < y := Int.tmod_lt_of_pos x hypos
                    have h0 : (0 : Int) ≤ x.tmod y := Int.tmod_nonneg y hx0
                    have hHi : x.tmod y ≤ imin (hi2 - 1) hi1 :=
                      le_imin (by omega) (le_trans hrx hx2)
                    simp only [eval, hva, hvb, binop, hy, ite_false, Value.hasShape,
                      Option.some.injEq, exists_eq_left', decide_eq_true_eq]
                    exact ⟨h0, hHi⟩
                  · rename_i hs
                    cases harith
                    have hy : y ≠ 0 := by omega
                    rcases le_or_gt 0 y with hy0 | hy0
                    · have hypos : (0 : Int) < y := lt_of_le_of_ne hy0 (Ne.symm hy)
                      have hS : y ≤ imax hi2 (-lo2) :=
                        le_trans hy2 (le_imax_left hi2 (-lo2))
                      obtain ⟨hlo, hhi⟩ := trem_pos y x lo2 hi2 hypos hS
                      simp only [eval, hva, hvb, binop, hy, ite_false, Value.hasShape,
                        Option.some.injEq, exists_eq_left', decide_eq_true_eq]
                      exact ⟨hlo, hhi⟩
                    · have hyN : (0 : Int) < -y := by omega
                      have hrw : x.tmod y = x.tmod (-y) := by
                        have h := Int.tmod_neg x (-y)
                        rwa [Int.neg_neg] at h
                      have hS : -y ≤ imax hi2 (-lo2) :=
                        le_trans (by omega : -y ≤ -lo2) (le_imax_right hi2 (-lo2))
                      obtain ⟨hlo, hhi⟩ := trem_pos (-y) x lo2 hi2 hyN hS
                      have hLo : -(remSchranke lo2 hi2) ≤ x.tmod y := by
                        rw [hrw]; exact hlo
                      have hHi : x.tmod y ≤ remSchranke lo2 hi2 := by
                        rw [hrw]; exact hhi
                      simp only [eval, hva, hvb, binop, hy, ite_false, Value.hasShape,
                        Option.some.injEq, exists_eq_left', decide_eq_true_eq]
                      exact ⟨hLo, hHi⟩
                · cases harith
            | band =>
                dsimp only at harith
                split at harith
                · rename_i hc
                  cases harith
                  obtain ⟨hg1, hg2⟩ := hc
                  have hxnn : (0 : Int) ≤ x := le_trans hg1 hx1
                  have hyn : (0 : Int) ≤ y := le_trans hg2 hy1
                  have hNat1 : x.toNat &&& y.toNat ≤ x.toNat := Nat.and_le_left
                  have hNat2 : x.toNat &&& y.toNat ≤ y.toNat := Nat.and_le_right
                  have c1 : (((x.toNat &&& y.toNat : Nat)) : Int) ≤ (((x.toNat : Nat)) : Int) := by
                    exact_mod_cast hNat1
                  have c2 : (((x.toNat &&& y.toNat : Nat)) : Int) ≤ (((y.toNat : Nat)) : Int) := by
                    exact_mod_cast hNat2
                  have rx : ((((x.toNat : Nat))) : Int) = x := Int.toNat_of_nonneg hxnn
                  have ry : ((((y.toNat : Nat))) : Int) = y := Int.toNat_of_nonneg hyn
                  have h0 : (0 : Int) ≤ (((x.toNat &&& y.toNat : Nat)) : Int) := by positivity
                  have hmin : (((x.toNat &&& y.toNat : Nat)) : Int) ≤ imin hi1 hi2 := by
                    have h1 : (((x.toNat &&& y.toNat : Nat)) : Int) ≤ hi1 := by omega
                    have h2 : (((x.toNat &&& y.toNat : Nat)) : Int) ≤ hi2 := by omega
                    exact le_imin h1 h2
                  simp only [eval, hva, hvb, binop, bits, and_true, ite_true, ite_false, show 0 ≤ x by omega,
                    show 0 ≤ y by omega, Value.hasShape,
                    Option.some.injEq, exists_eq_left', decide_eq_true_eq]
                  exact ⟨h0, hmin⟩
                · cases harith
            | bor =>
                dsimp only at harith
                split at harith
                · rename_i hc
                  cases harith
                  obtain ⟨hg1, hg2⟩ := hc
                  have hxM : x ≤ imax hi1 hi2 := le_trans hx2 (le_imax_left hi1 hi2)
                  have hyM : y ≤ imax hi1 hi2 := le_trans hy2 (le_imax_right hi1 hi2)
                  have hxN : x.toNat ≤ (imax hi1 hi2).toNat := Int.toNat_le_toNat hxM
                  have hyN : y.toNat ≤ (imax hi1 hi2).toNat := Int.toNat_le_toNat hyM
                  have hcov : (imax hi1 hi2).toNat ≤ maskeNat ((imax hi1 hi2).toNat) :=
                    maskeNat_ge _
                  obtain ⟨k, hk⟩ := maskeNat_pow2 ((imax hi1 hi2).toNat)
                  have hxo : x.toNat < 2 ^ k :=
                    lt_of_le_of_lt (Nat.le_trans hxN hcov) (by omega)
                  have hyo : y.toNat < 2 ^ k :=
                    lt_of_le_of_lt (Nat.le_trans hyN hcov) (by omega)
                  have hbor : x.toNat ||| y.toNat < 2 ^ k := Nat.or_lt_two_pow hxo hyo
                  have hle : x.toNat ||| y.toNat ≤ maskeNat ((imax hi1 hi2).toNat) := by omega
                  have hleI : ((((x.toNat ||| y.toNat : Nat))) : Int)
                      ≤ ((((maskeNat ((imax hi1 hi2).toNat) : Nat))) : Int) := by
                    exact_mod_cast hle
                  have hmask : ((((maskeNat ((imax hi1 hi2).toNat) : Nat))) : Int)
                      = maske (imax hi1 hi2) := rfl
                  have hfin : ((((x.toNat ||| y.toNat : Nat))) : Int) ≤ maske (imax hi1 hi2) := by
                    omega
                  have h0 : (0 : Int) ≤ ((((x.toNat ||| y.toNat : Nat))) : Int) := by positivity
                  simp only [eval, hva, hvb, binop, bits, and_true, ite_true, ite_false, show 0 ≤ x by omega,
                    show 0 ≤ y by omega, Value.hasShape,
                    Option.some.injEq, exists_eq_left', decide_eq_true_eq]
                  exact ⟨h0, hfin⟩
                · cases harith
            | bxor =>
                dsimp only at harith
                split at harith
                · rename_i hc
                  cases harith
                  obtain ⟨hg1, hg2⟩ := hc
                  have hxM : x ≤ imax hi1 hi2 := le_trans hx2 (le_imax_left hi1 hi2)
                  have hyM : y ≤ imax hi1 hi2 := le_trans hy2 (le_imax_right hi1 hi2)
                  have hxN : x.toNat ≤ (imax hi1 hi2).toNat := Int.toNat_le_toNat hxM
                  have hyN : y.toNat ≤ (imax hi1 hi2).toNat := Int.toNat_le_toNat hyM
                  have hcov : (imax hi1 hi2).toNat ≤ maskeNat ((imax hi1 hi2).toNat) :=
                    maskeNat_ge _
                  obtain ⟨k, hk⟩ := maskeNat_pow2 ((imax hi1 hi2).toNat)
                  have hxo : x.toNat < 2 ^ k :=
                    lt_of_le_of_lt (Nat.le_trans hxN hcov) (by omega)
                  have hyo : y.toNat < 2 ^ k :=
                    lt_of_le_of_lt (Nat.le_trans hyN hcov) (by omega)
                  have hxor : x.toNat ^^^ y.toNat < 2 ^ k := Nat.xor_lt_two_pow hxo hyo
                  have hle : x.toNat ^^^ y.toNat ≤ maskeNat ((imax hi1 hi2).toNat) := by omega
                  have hleI : ((((x.toNat ^^^ y.toNat : Nat))) : Int)
                      ≤ ((((maskeNat ((imax hi1 hi2).toNat) : Nat))) : Int) := by
                    exact_mod_cast hle
                  have hmask : ((((maskeNat ((imax hi1 hi2).toNat) : Nat))) : Int)
                      = maske (imax hi1 hi2) := rfl
                  have hfin : ((((x.toNat ^^^ y.toNat : Nat))) : Int) ≤ maske (imax hi1 hi2) := by
                    omega
                  have h0 : (0 : Int) ≤ ((((x.toNat ^^^ y.toNat : Nat))) : Int) := by positivity
                  simp only [eval, hva, hvb, binop, bits, and_true, ite_true, ite_false, show 0 ≤ x by omega,
                    show 0 ≤ y by omega, Value.hasShape,
                    Option.some.injEq, exists_eq_left', decide_eq_true_eq]
                  exact ⟨h0, hfin⟩
                · cases harith
            | shl =>
                dsimp only at harith
                split at harith
                · rename_i hc
                  cases harith
                  obtain ⟨hg1, hg2⟩ := hc
                  have hxnn : (0 : Int) ≤ x := le_trans hg1 hx1
                  have hhi1nn : (0 : Int) ≤ hi1 := le_trans hg1 (le_trans hx1 hx2)
                  have ln : lo2.toNat ≤ y.toNat := Int.toNat_le_toNat hy1
                  have yn : y.toNat ≤ hi2.toNat := Int.toNat_le_toNat hy2
                  have p0 : (2 : Int) ^ lo2.toNat ≤ 2 ^ y.toNat := zwei_pow_le ln
                  have p1 : (2 : Int) ^ y.toNat ≤ 2 ^ hi2.toNat := zwei_pow_le yn
                  have e0 : (0 : Int) ≤ 2 ^ lo2.toNat := Int.pow_nonneg (by omega)
                  have e1 : (0 : Int) ≤ 2 ^ y.toNat := Int.pow_nonneg (by omega)
                  have hLo : lo1 * 2 ^ lo2.toNat ≤ x * 2 ^ y.toNat :=
                    le_trans (Int.mul_le_mul_of_nonneg_right hx1 e0)
                      (Int.mul_le_mul_of_nonneg_left p0 hxnn)
                  have hHi : x * 2 ^ y.toNat ≤ hi1 * 2 ^ hi2.toNat :=
                    le_trans (Int.mul_le_mul_of_nonneg_right hx2 e1)
                      (Int.mul_le_mul_of_nonneg_left p1 hhi1nn)
                  simp only [eval, hva, hvb, binop, and_true, ite_true, ite_false, show 0 ≤ x by omega,
                    show 0 ≤ y by omega, Value.hasShape,
                    Option.some.injEq, exists_eq_left', decide_eq_true_eq]
                  exact ⟨hLo, hHi⟩
                · cases harith
            | shr =>
                dsimp only at harith
                split at harith
                · rename_i hc
                  cases harith
                  obtain ⟨hg1, hg2⟩ := hc
                  have hxnn : (0 : Int) ≤ x := le_trans hg1 hx1
                  have hhi1nn : (0 : Int) ≤ hi1 := le_trans hg1 (le_trans hx1 hx2)
                  have ln : lo2.toNat ≤ y.toNat := Int.toNat_le_toNat hy1
                  have yn : y.toNat ≤ hi2.toNat := Int.toNat_le_toNat hy2
                  have p0 : (2 : Int) ^ lo2.toNat ≤ 2 ^ y.toNat := zwei_pow_le ln
                  have p1 : (2 : Int) ^ y.toNat ≤ 2 ^ hi2.toNat := zwei_pow_le yn
                  have e0 : (0 : Int) < 2 ^ lo2.toNat := Int.pow_pos (by omega)
                  have e1 : (0 : Int) < 2 ^ y.toNat := Int.pow_pos (by omega)
                  have e2 : (0 : Int) < 2 ^ hi2.toNat := Int.pow_pos (by omega)
                  have hLo : lo1.tdiv (2 ^ hi2.toNat) ≤ x.tdiv (2 ^ y.toNat) :=
                    le_trans (Int.tdiv_le_tdiv e2 hx1) (tdiv_anti_nonneg hxnn e1 p1)
                  have hHi : x.tdiv (2 ^ y.toNat) ≤ hi1.tdiv (2 ^ lo2.toNat) :=
                    le_trans (Int.tdiv_le_tdiv e1 hx2) (tdiv_anti_nonneg hhi1nn e0 p0)
                  simp only [eval, hva, hvb, binop, and_true, ite_true, ite_false, show 0 ≤ x by omega,
                    show 0 ≤ y by omega, Value.hasShape,
                    Option.some.injEq, exists_eq_left', decide_eq_true_eq]
                  exact ⟨hLo, hHi⟩
                · cases harith
            | eq => cases harith
            | ne => cases harith
            | lt => cases harith
            | le => cases harith
            | gt => cases harith
            | ge => cases harith
            | and => cases harith
            | or => cases harith
          · -- eine Seite ohne Bereich: nur `+`, `-`, `*` bleiben Zahlen
            rename_i hz1 hz2
            obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
            obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
            cases op <;> cases harith
            all_goals simp [eval, hva, hvb, binop, Value.hasShape]
          · cases harith
        · -- Vergleich
          rename_i harith
          unfold vergleich at h
          cases op with
          | eq => cases h; simp [eval, hva, hvb, binop, Value.hasShape]
          | ne => cases h; simp [eval, hva, hvb, binop, Value.hasShape]
          | lt =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp [eval, hva, hvb, binop, Value.hasShape]
              · cases h
          | le =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp [eval, hva, hvb, binop, Value.hasShape]
              · cases h
          | gt =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp [eval, hva, hvb, binop, Value.hasShape]
              · cases h
          | ge =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp [eval, hva, hvb, binop, Value.hasShape]
              · cases h
          | and =>
              dsimp only at h
              split at h
              · cases h
                obtain ⟨x, rfl⟩ := Value.hasShape_bool_true va hvas
                obtain ⟨y, rfl⟩ := Value.hasShape_bool_true vb hvbs
                simp [eval, hva, hvb, andBool, Value.hasShape]
              · cases h
          | or =>
              dsimp only at h
              split at h
              · cases h
                obtain ⟨x, rfl⟩ := Value.hasShape_bool_true va hvas
                obtain ⟨y, rfl⟩ := Value.hasShape_bool_true vb hvbs
                simp [eval, hva, hvb, orBool, Value.hasShape]
              · cases h
          | add => cases h
          | sub => cases h
          | mul => cases h
          | div => cases h
          | rem => cases h
          | band => cases h
          | bor => cases h
          | bxor => cases h
          | shl => cases h
          | shr => cases h
      · cases h
  | .someOf a, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD a
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i sa ha
        split at h
        · rename_i hz
          cases h
          obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
          obtain ⟨n, rfl⟩ := zahl_some_int hz hvs
          simp [eval, hv, Value.hasShape]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .forallSlots v n b, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD b
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i hb
        cases h
        obtain ⟨t, ht⟩ := allBelow_bool _ n.toNat (quant_rumpf D Γ ih Δ s n hw hl hk hb)
        simp [eval, ht, Value.hasShape]
      · exact absurd h (by simp)
  | .existsSlots v n b, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD b
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i hb
        cases h
        obtain ⟨t, ht⟩ := anyBelow_bool _ n.toNat (quant_rumpf D Γ ih Δ s n hw hl hk hb)
        simp [eval, ht, Value.hasShape]
      · exact absurd h (by simp)
  | .reaches c a z via cnt, Δ, s, sh => by
      have iha := schluss_sicher D Γ hD a
      have ihz := schluss_sicher D Γ hD z
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i sa sz ha hz hvia
        split at h
        · rename_i hzz
          cases h
          obtain ⟨va, hva, hvas⟩ := iha Δ s _ hw hl hk ha
          obtain ⟨vz, hvz, hvzs⟩ := ihz Δ s _ hw hl hk hz
          obtain ⟨k, rfl⟩ := zahl_some_int hzz.1 hvas
          obtain ⟨t, rfl⟩ := zahl_some_int hzz.2 hvzs
          obtain ⟨b, hb⟩ := chase_bool s.world c via t (fun k => hk c via k hvia) cnt.toNat k
          simp [eval, hva, hvz, hb, Value.hasShape]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .chainFrom c hd x via cnt, Δ, s, sh => by
      have ihh := schluss_sicher D Γ hD hd
      have ihx := schluss_sicher D Γ hD x
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i sx hh hx hvia
        split at h
        · rename_i hzz
          cases h
          obtain ⟨vh, hvh, hvhs⟩ := ihh Δ s _ hw hl hk hh
          obtain ⟨vx, hvx, hvxs⟩ := ihx Δ s _ hw hl hk hx
          obtain ⟨t, rfl⟩ := zahl_some_int hzz hvxs
          rcases Value.hasShape_opt_true vh hvhs with rfl | ⟨m, rfl⟩
          · simp [eval, hvh, hvx, Value.hasShape]
          · obtain ⟨b, hb⟩ := chase_bool s.world c via t (fun k => hk c via k hvia) cnt.toNat m
            simp [eval, hvh, hvx, hb, Value.hasShape]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .hasShape n sh', Δ, s, sh => by
      intro _ _ _ h
      simp only [schluss] at h; cases h
      exact ⟨_, rfl, by simp [Value.hasShape]⟩
  | .wrapTo b sg a, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD a
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i sa ha
        split at h
        · rename_i hz
          cases h
          obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
          obtain ⟨n, rfl⟩ := zahl_some_int hz hvs
          simp [eval, hv, Value.hasShape]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .tagOf t p, Δ, s, sh => by
      intro _ _ _ h
      cases p <;> simp [schluss] at h

/-- The checker with a carried option target bound is still safe: what it accepts
    evaluates, and to a value of the computed shape. For every form but `someOf`
    this is `schluss_sicher` through the delegation; for `someOf` the inner value
    is a number by `schluss_sicher`, hence `present`, hence `.opt`. The bound
    itself leaves no trace in the shape -- `Shape.opt` carries none (Fund 2) --
    it only decides acceptance. -/
theorem schlussMitZiel_sicher (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (ziel : Option (Int × Int)) (e : Expr) (Δ : Lokal) (s : State) (sh : Shape)
    (hw : WF Γ s.world) (hl : WFL Δ s.local') (hk : KettenWohlgeformt D s.world)
    (h : schlussMitZiel D ziel Δ e = some sh) :
    ∃ v, eval s e = some v ∧ v.hasShape sh = true := by
  cases e with
  | someOf a =>
    simp only [schlussMitZiel] at h
    split at h
    · rename_i sa ha
      cases ziel with
      | none =>
        simp only [somePasst] at h
        split at h
        · rename_i hz
          cases h
          obtain ⟨v, hv, hvs⟩ := schluss_sicher D Γ hD a Δ s _ hw hl hk ha
          obtain ⟨n, rfl⟩ := zahl_some_int hz hvs
          simp [eval, hv, Value.hasShape]
        · exact absurd h (by simp)
      | some bh =>
        obtain ⟨lo, hi⟩ := bh
        cases sa with
        | int =>
          simp only [somePasst] at h
          cases h
        | bool =>
          simp only [somePasst] at h
          cases h
        | opt =>
          simp only [somePasst] at h
          cases h
        | intIn lo' hi' =>
          simp only [somePasst] at h
          split at h
          · rename_i hs
            cases h
            obtain ⟨v, hv, hvs⟩ := schluss_sicher D Γ hD a Δ s _ hw hl hk ha
            obtain ⟨n, rfl, _, _⟩ := Value.hasShape_intIn_true v lo' hi' hvs
            simp [eval, hv, Value.hasShape]
          · exact absurd h (by simp)
        | sum cs =>
          simp only [somePasst] at h
          cases h
    · exact absurd h (by simp)
  | lit v =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.lit v) Δ s sh hw hl hk h
  | name n =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.name n) Δ s sh hw hl hk h
  | place c i f =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.place c i f) Δ s sh hw hl hk h
  | global g =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.global g) Δ s sh hw hl hk h
  | un op a =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.un op a) Δ s sh hw hl hk h
  | bin op a b =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.bin op a b) Δ s sh hw hl hk h
  | fieldOf c f =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.fieldOf c f) Δ s sh hw hl hk h
  | forallSlots v n b =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.forallSlots v n b) Δ s sh hw hl hk h
  | existsSlots v n b =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.existsSlots v n b) Δ s sh hw hl hk h
  | reaches c a z via cnt =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.reaches c a z via cnt) Δ s sh hw hl hk h
  | chainFrom c hd x via cnt =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.chainFrom c hd x via cnt) Δ s sh hw hl hk h
  | hasShape n sh' =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.hasShape n sh') Δ s sh hw hl hk h
  | wrapTo b sg a =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.wrapTo b sg a) Δ s sh hw hl hk h
  | tagOf t p =>
    simp only [schlussMitZiel] at h
    exact schluss_sicher D Γ hD (.tagOf t p) Δ s sh hw hl hk h

/-! ## 4. Decided examples -- the formulas above, computed

    Each example evaluates `schluss` (or `schlussMitZiel`) on literals and checks
    the exact range the checker promises. They run wherever the file builds. -/

/-- An empty declaration and an empty scope: literals need neither. -/
def leerD : Deklaration := ⟨fun _ _ => none, fun _ => 0, fun _ _ => none, fun _ => none⟩

/-- `7 / 2` over point ranges: `teile` gives `3 .. 3`. -/
example : schluss leerD (fun _ => none)
    (.bin .div (.lit (.int 7)) (.lit (.int 2))) = some (.intIn 3 3) := by decide

/-- `-7 / 2` truncates toward zero through the four corners: `-3 .. -3`. -/
example : schluss leerD (fun _ => none)
    (.bin .div (.lit (.int (-7))) (.lit (.int 2))) = some (.intIn (-3) (-3)) := by decide

/-- `7 % 2`: `rest` gives `0 .. min (2 - 1) 7`. -/
example : schluss leerD (fun _ => none)
    (.bin .rem (.lit (.int 7)) (.lit (.int 2))) = some (.intIn 0 1) := by decide

/-- `6 & 3`: `bitweise` gives `0 .. min 6 3`. -/
example : schluss leerD (fun _ => none)
    (.bin .band (.lit (.int 6)) (.lit (.int 3))) = some (.intIn 0 3) := by decide

/-- `6 | 3`: `bitweise` gives `0 .. maske 6` with `maske 6 = 7`. -/
example : schluss leerD (fun _ => none)
    (.bin .bor (.lit (.int 6)) (.lit (.int 3))) = some (.intIn 0 7) := by decide

/-- `3 << 2`: `schiebe_links` gives `3 * 2^2 .. 3 * 2^2`. -/
example : schluss leerD (fun _ => none)
    (.bin .shl (.lit (.int 3)) (.lit (.int 2))) = some (.intIn 12 12) := by decide

/-- `7 >> 1`: `schiebe_rechts` gives `7 / 2^1 .. 7 / 2^1`. -/
example : schluss leerD (fun _ => none)
    (.bin .shr (.lit (.int 7)) (.lit (.int 1))) = some (.intIn 3 3) := by decide

/-- `Some(8)` against the payload bound `0 .. 7` (`gift/170`): refused (F10). -/
example : schlussMitZiel leerD (some (0, 7)) (fun _ => none)
    (.someOf (.lit (.int 8))) = none := by decide

/-- ... and inside `0 .. 8` it passes. -/
example : schlussMitZiel leerD (some (0, 8)) (fun _ => none)
    (.someOf (.lit (.int 8))) = some .opt := by decide

end Gabbro.Sicherheit
