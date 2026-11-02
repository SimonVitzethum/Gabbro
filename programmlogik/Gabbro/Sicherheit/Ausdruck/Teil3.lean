module

public import Gabbro.Body
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Order.Lattice
public import Gabbro.Sicherheit.Ausdruck.Teil2

@[expose] public section

namespace Gabbro.Sicherheit
open Gabbro.Body

set_option linter.unusedSectionVars false in
theorem schluss_sicher_bin (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (op)
    (a)
    (b)
    (Δ : Lokal)
    (s : State)
    (sh : Shape)
    (ih_schluss_sicher_a : ∀ (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ), ∀ (Δ : Lokal), ∀ (s : State), ∀ (sh : Shape), WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ a = some sh → ∃ v, eval s a = some v ∧ v.hasShape sh = true)
    (ih_schluss_sicher_b : ∀ (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ), ∀ (Δ : Lokal), ∀ (s : State), ∀ (sh : Shape), WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ b = some sh → ∃ v, eval s b = some v ∧ v.hasShape sh = true)
    : WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ (.bin op a b : Expr) = some sh → ∃ v, eval s (.bin op a b : Expr) = some v ∧ v.hasShape sh = true :=
  by
      have iha := ih_schluss_sicher_a D Γ hD
      have ihb := ih_schluss_sicher_b D Γ hD
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
            | add => cases harith; simp only [eval, hva, hvb, binop, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left',
  Bool.and_eq_true, decide_eq_true_eq]; omega
            | sub => cases harith; simp only [eval, hva, hvb, binop, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left',
  tsub_le_iff_right, Bool.and_eq_true, decide_eq_true_eq]; omega
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
            all_goals simp only [eval, hva, hvb, binop, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
          · cases harith
        · -- Vergleich
          rename_i harith
          unfold vergleich at h
          cases op with
          | eq => cases h; simp only [eval, hva, hvb, binop, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
          | ne => cases h; simp only [eval, hva, hvb, binop, ne_eq, decide_not, Option.some.injEq, Value.hasShape, Bool.decide_and,
  exists_eq_left']
          | lt =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp only [eval, hva, hvb, binop, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
              · cases h
          | le =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp only [eval, hva, hvb, binop, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
              · cases h
          | gt =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp only [eval, hva, hvb, binop, gt_iff_lt, Option.some.injEq, Value.hasShape, Bool.decide_and,
  exists_eq_left']
              · cases h
          | ge =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp only [eval, hva, hvb, binop, ge_iff_le, Option.some.injEq, Value.hasShape, Bool.decide_and,
  exists_eq_left']
              · cases h
          | and =>
              dsimp only at h
              split at h
              · cases h
                obtain ⟨x, rfl⟩ := Value.hasShape_bool_true va hvas
                obtain ⟨y, rfl⟩ := Value.hasShape_bool_true vb hvbs
                simp only [eval, andBool, hva, hvb, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
              · cases h
          | or =>
              dsimp only at h
              split at h
              · cases h
                obtain ⟨x, rfl⟩ := Value.hasShape_bool_true va hvas
                obtain ⟨y, rfl⟩ := Value.hasShape_bool_true vb hvbs
                simp only [eval, orBool, hva, hvb, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
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

set_option linter.unusedSectionVars false in
theorem schluss_sicher_someOf (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (a)
    (Δ : Lokal)
    (s : State)
    (sh : Shape)
    (ih_schluss_sicher_a : ∀ (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ), ∀ (Δ : Lokal), ∀ (s : State), ∀ (sh : Shape), WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ a = some sh → ∃ v, eval s a = some v ∧ v.hasShape sh = true)
    : WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ (.someOf a : Expr) = some sh → ∃ v, eval s (.someOf a : Expr) = some v ∧ v.hasShape sh = true :=
  by
  have ih := ih_schluss_sicher_a D Γ hD
  intro hw hl hk h
  simp only [schluss] at h
  split at h
  · rename_i sa ha
    split at h
    · rename_i hz
      cases h
      obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
      obtain ⟨n, rfl⟩ := zahl_some_int hz hvs
      simp only [eval, hv, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

set_option linter.unusedSectionVars false in
theorem schluss_sicher_reaches (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (c)
    (a)
    (z)
    (via)
    (cnt)
    (Δ : Lokal)
    (s : State)
    (sh : Shape)
    (ih_schluss_sicher_a : ∀ (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ), ∀ (Δ : Lokal), ∀ (s : State), ∀ (sh : Shape), WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ a = some sh → ∃ v, eval s a = some v ∧ v.hasShape sh = true)
    (ih_schluss_sicher_z : ∀ (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ), ∀ (Δ : Lokal), ∀ (s : State), ∀ (sh : Shape), WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ z = some sh → ∃ v, eval s z = some v ∧ v.hasShape sh = true)
    : WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ (.reaches c a z via cnt : Expr) = some sh → ∃ v, eval s (.reaches c a z via cnt : Expr) = some v ∧ v.hasShape sh = true :=
  by
  have iha := ih_schluss_sicher_a D Γ hD
  have ihz := ih_schluss_sicher_z D Γ hD
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
      simp only [eval, hva, hvz, hb, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

end Gabbro.Sicherheit
