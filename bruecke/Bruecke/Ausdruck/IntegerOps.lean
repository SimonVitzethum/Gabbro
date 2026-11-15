module

public import Bruecke.Ausdruck.Teil1

@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

variable {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
variable (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ)

/-! Agreement of the actual checked integer lowerings with Body. G excludes zero
denominators in the operand types; both models use unbounded integers and truncation
toward zero, including a negative dividend or denominator. Shift widths and the 4096
limit remain checked by the lowering. Body needs only the resulting nonnegative values.
No machine-width wraparound or masked shift count is introduced here. -/

theorem lowDurch_binop {x y z : LowSide u Γ Λ} (h : LowSide.durch x y = .ok z) :
    Gabbro.Body.binop .div
      (valOf (.int x.range.1 x.range.2) (eval σ₀ x.term σ ρ))
      (valOf (.int y.range.1 y.range.2) (eval σ₀ y.term σ ρ)) =
      some (valOf (.int z.range.1 z.range.2) (eval σ₀ z.term σ ρ)) := by
  unfold LowSide.durch at h
  repeat' split at h
  all_goals try { cases h; done }
  all_goals
    cases h
    have hlo := (eval σ₀ y.term σ ρ).lo_le
    have hhi := (eval σ₀ y.term σ ρ).le_hi
    have hn : (eval σ₀ y.term σ ρ).n ≠ 0 := by omega
    simp only [valOf_int, Gabbro.Body.binop, if_neg hn]
    rfl

theorem lowRest_binop {x y z : LowSide u Γ Λ} (h : LowSide.rest x y = .ok z) :
    Gabbro.Body.binop .rem
      (valOf (.int x.range.1 x.range.2) (eval σ₀ x.term σ ρ))
      (valOf (.int y.range.1 y.range.2) (eval σ₀ y.term σ ρ)) =
      some (valOf (.int z.range.1 z.range.2) (eval σ₀ z.term σ ρ)) := by
  unfold LowSide.rest at h
  repeat' split at h
  all_goals try { cases h; done }
  all_goals
    cases h
    have hlo := (eval σ₀ y.term σ ρ).lo_le
    have hhi := (eval σ₀ y.term σ ρ).le_hi
    have hn : (eval σ₀ y.term σ ρ).n ≠ 0 := by omega
    simp only [valOf_int, Gabbro.Body.binop, if_neg hn]
    rfl

theorem lowLinks_binop {x y z : LowSide u Γ Λ} (h : LowSide.links x y = .ok z) :
    Gabbro.Body.binop .shl
      (valOf (.int x.range.1 x.range.2) (eval σ₀ x.term σ ρ))
      (valOf (.int y.range.1 y.range.2) (eval σ₀ y.term σ ρ)) =
      some (valOf (.int z.range.1 z.range.2) (eval σ₀ z.term σ ρ)) := by
  unfold LowSide.links at h
  repeat' split at h
  all_goals try { cases h; done }
  cases h
  have hx := (eval σ₀ x.term σ ρ).lo_le
  have hy := (eval σ₀ y.term σ ρ).lo_le
  have ha : 0 ≤ (eval σ₀ x.term σ ρ).n := by omega
  have hb : 0 ≤ (eval σ₀ y.term σ ρ).n := by omega
  simp only [valOf_int, Gabbro.Body.binop, if_pos (And.intro ha hb)]
  rfl

theorem lowRechts_binop {x y z : LowSide u Γ Λ} (h : LowSide.rechts x y = .ok z) :
    Gabbro.Body.binop .shr
      (valOf (.int x.range.1 x.range.2) (eval σ₀ x.term σ ρ))
      (valOf (.int y.range.1 y.range.2) (eval σ₀ y.term σ ρ)) =
      some (valOf (.int z.range.1 z.range.2) (eval σ₀ z.term σ ρ)) := by
  unfold LowSide.rechts at h
  repeat' split at h
  all_goals try { cases h; done }
  cases h
  have hx := (eval σ₀ x.term σ ρ).lo_le
  have hy := (eval σ₀ y.term σ ρ).lo_le
  have ha : 0 ≤ (eval σ₀ x.term σ ρ).n := by omega
  have hb : 0 ≤ (eval σ₀ y.term σ ρ).n := by omega
  simp only [valOf_int, Gabbro.Body.binop, if_pos (And.intro ha hb)]
  change some (Gabbro.Body.Value.int ((eval σ₀ x.term σ ρ).n.tdiv
    (2 ^ (eval σ₀ y.term σ ρ).n.toNat))) =
    some (.int ((eval σ₀ x.term σ ρ).n / (2 ^ (eval σ₀ y.term σ ρ).n.toNat)))
  rw [Int.tdiv_eq_ediv_nonneg ha]

theorem lowAnd_binop {x y z : LowSide u Γ Λ} (h : LowSide.and x y = .ok z) :
    Gabbro.Body.binop .band
      (valOf (.int x.range.1 x.range.2) (eval σ₀ x.term σ ρ))
      (valOf (.int y.range.1 y.range.2) (eval σ₀ y.term σ ρ)) =
      some (valOf (.int z.range.1 z.range.2) (eval σ₀ z.term σ ρ)) := by
  unfold LowSide.and at h
  repeat' split at h
  all_goals try { cases h; done }
  cases h
  have hx := (eval σ₀ x.term σ ρ).lo_le
  have hy := (eval σ₀ y.term σ ρ).lo_le
  have ha : 0 ≤ (eval σ₀ x.term σ ρ).n := by omega
  have hb : 0 ≤ (eval σ₀ y.term σ ρ).n := by omega
  simp only [valOf_int, Gabbro.Body.binop, Gabbro.Body.bits, if_pos (And.intro ha hb)]
  rfl

theorem lowOr_binop {x y z : LowSide u Γ Λ} (h : LowSide.or x y = .ok z) :
    Gabbro.Body.binop .bor
      (valOf (.int x.range.1 x.range.2) (eval σ₀ x.term σ ρ))
      (valOf (.int y.range.1 y.range.2) (eval σ₀ y.term σ ρ)) =
      some (valOf (.int z.range.1 z.range.2) (eval σ₀ z.term σ ρ)) := by
  unfold LowSide.or at h
  repeat' split at h
  all_goals try { cases h; done }
  cases h
  have hx := (eval σ₀ x.term σ ρ).lo_le
  have hy := (eval σ₀ y.term σ ρ).lo_le
  have ha : 0 ≤ (eval σ₀ x.term σ ρ).n := by omega
  have hb : 0 ≤ (eval σ₀ y.term σ ρ).n := by omega
  simp only [valOf_int, Gabbro.Body.binop, Gabbro.Body.bits, if_pos (And.intro ha hb)]
  rfl

theorem lowXor_binop {x y z : LowSide u Γ Λ} (h : LowSide.xoder x y = .ok z) :
    Gabbro.Body.binop .bxor
      (valOf (.int x.range.1 x.range.2) (eval σ₀ x.term σ ρ))
      (valOf (.int y.range.1 y.range.2) (eval σ₀ y.term σ ρ)) =
      some (valOf (.int z.range.1 z.range.2) (eval σ₀ z.term σ ρ)) := by
  unfold LowSide.xoder at h
  repeat' split at h
  all_goals try { cases h; done }
  cases h
  have hx := (eval σ₀ x.term σ ρ).lo_le
  have hy := (eval σ₀ y.term σ ρ).lo_le
  have ha : 0 ≤ (eval σ₀ x.term σ ρ).n := by omega
  have hb : 0 ≤ (eval σ₀ y.term σ ρ).n := by omega
  simp only [valOf_int, Gabbro.Body.binop, Gabbro.Body.bits, if_pos (And.intro ha hb)]
  rfl

end Gabbro.Bruecke
