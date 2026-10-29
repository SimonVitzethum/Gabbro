/-
  File:      stage0/Stage0/Senke/Ausdruck/Top.lean
  Subject:   The slot an expression's code stops at (`lowE_top`), and the shape of a binary operation's code
             (`bin_some`, `binE_ok`): its two operands, then one instruction.
-/
import Stage0.Senke.Ausdruck.Gleit.Grenze
import Stage0.Senke.Ausdruck.Gleichungen
import Stage0.Senke.Ausdruck.Sim
import Stage0.Senke.Ausdruck.Wort

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-! ## The slot the lowering stops at -/

/-- The code of a binary operation stops above `d` once its first operand does. -/
theorem bin_top {Λ : List (Res D)} {Γ : Ctx} {τa τb : Ty} {a : Expr D Γ Λ τa} {b : Expr D Γ Λ τb} {o d : Nat}
    {c : List II} {top : Nat} (ht : ∀ c t, lowE L a d = some (c, t) → d < t)
    (h : (do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 o d ca cb)) = some (c, top)) : d < top := by
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, he⟩ := h
  simp only [bin2, pure, Option.some.injEq, Prod.mk.injEq] at he
  have := ht ca ta ha
  omega

theorem lowN_top {Λ : List (Res D)} {Γ : Ctx} {tag : Nat} :
    {a : Option (Int × Int)} → (e : NutzlastExpr D Γ Λ a) → (d : Nat) → (c : List II) →
    (top : Nat) → lowN L tag e d = some (c, top) → d < top
  | _, .empty, d, c, top, h => by
    simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h; omega
  | _, .num e, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ce, te⟩, _, he⟩ := h
      simp only [packSum, bin2, Prod.mk.injEq] at he
      omega
    · cases h

theorem readBytesL_top (L : Lay D) (t : D.Tab) (f : D.Feld t) (idx : Nat → Option (List II × Nat)) :
    (n j d : Nat) → (c : List II) → (top : Nat) →
    readBytesL L t f idx j n d = some (c, top) → d < top
  | 0, j, d, c, top, h => by
    simp only [readBytesL, Option.some.injEq, Prod.mk.injEq] at h; omega
  | n + 1, j, d, c, top, h => by
    simp only [readBytesL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨ci', _, head, _, tail, _, h⟩ := h
    simp only [bin2, Prod.mk.injEq] at h
    omega

theorem reachEqL_top {d top : Nat} {a b : Option (List II × Nat)} {c : List II}
    (h : reachEqL d a b = some (c, top)) : d < top := by
  simp only [reachEqL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨ca, _, cb, _, he⟩ := h
  simp only [Prod.mk.injEq] at he
  omega

theorem reachL_top {d top : Nat} {L : Lay D} {t : D.Tab} {f : D.Feld t} {c : List II}
    (n : Nat) (a b : Option (List II × Nat)) (h : reachL L t f d n a b = some (c, top)) : d < top := by
  cases n with
  | zero => exact reachEqL_top h
  | succ n =>
    simp only [reachL, wennL, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨cc, tc⟩, hc, ca, _, cb, _, h⟩ := h
    have := reachEqL_top hc
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · cases h

theorem lowE_top {Λ : List (Res D)} : {Γ : Ctx} → {τ : Ty} → (e : Expr D Γ Λ τ) → (d : Nat) → (c : List II) →
    (top : Nat) → lowE L e d = some (c, top) → d < top
  | _, _, .widen _ _ e, d, c, top, h => lowE_top e d c top h
  | _, _, .some e, d, c, top, h => lowE_top e d c top h
  | _, _, .add a b, d, c, top, h | _, _, .sub a b, d, c, top, h | _, _, .mul a b, d, c, top, h
  | _, _, .and a b, d, c, top, h | _, _, .or a b, d, c, top, h =>
    bin_top (fun c t h => lowE_top a d c t h) h
  | _, _, .lt a b, d, c, top, h | _, _, .eq a b, d, c, top, h | _, _, .div _ _ a b, d, c, top, h
  | _, _, .rem _ _ a b, d, c, top, h | _, _, .sdiv _ a b, d, c, top, h | _, _, .srem _ a b, d, c, top, h
  | _, _, .band _ _ a b, d, c, top, h | _, _, .bor _ _ _ _ _ a b, d, c, top, h
  | _, _, .bxor _ _ _ _ _ a b, d, c, top, h | _, _, .shl _ _ _ _ _ a b, d, c, top, h
  | _, _, .shr _ _ _ _ _ a b, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact bin_top (fun c t h => lowE_top a d c t h) h
    · cases h
  | _, _, .fllt a b, d, c, top, h | _, _, .flle a b, d, c, top, h => floatExprL_top h
  | _, _, .neg a, d, c, top, h => by
    simp only [lowE_eqs, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, _, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, _, .not a, d, c, top, h => by
    simp only [lowE_eqs, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, _, he⟩ := h
    simp only [bin2, Prod.mk.injEq] at he
    omega
  | _, _, .istSome e, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ce, te⟩, _, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      omega
    · cases h
  | _, _, .le a b, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨cb, tb⟩, _, ⟨ca, ta⟩, _, he⟩ := h
      simp only [bin2, Prod.mk.injEq] at he
      omega
    · cases h
  | _, _, .lit n, d, c, top, h | _, _, .why .., d, c, top, h
  | _, _, .fnref .., d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · cases h
  | _, _, .tru, d, c, top, h | _, _, .fls, d, c, top, h | _, _, .var _, d, c, top, h
  | _, _, .none _, d, c, top, h | _, _, .ptrOf .., d, c, top, h => by
    simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at h; omega
  | _, _, .glob .., d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · cases h
  | _, _, .slot _ _ i _, d, c, top, h | _, _, .thru _ _ _ _ i _, d, c, top, h => by
    simp only [lowE_eqs, bind, Option.bind_eq_some_iff] at h
    obtain ⟨ci', _, hs⟩ := h
    simp only [slotC, slotA, Option.map_eq_some_iff] at hs
    obtain ⟨a, ha, he⟩ := hs
    split at ha
    · simp only [Option.some.injEq] at ha; subst ha; simp only [Prod.mk.injEq] at he; omega
    · cases ha
  | _, _, .case cs i nutz, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact lowN_top nutz _ _ _ h
    · cases h
  | _, _, .wenn cond a b, d, c, top, h => by
    simp only [lowE_eqs, wennL, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨cc, tc⟩, hc, ⟨ca, ta⟩, _, ⟨cb, tb⟩, _, h⟩ := h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      have := lowE_top cond d cc tc hc
      omega
    · cases h
  | _, _, .eng e lo' hi' b, d, c, top, h => by
    simp only [lowE_eqs, engL] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨ce, te⟩, _, ⟨cb, tb⟩, _, h⟩ := h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · cases h
    · cases h
  | _, _, .getBytes t f _ n i _ _ _, d, c, top, h => by
    simp only [lowE_eqs] at h
    split at h
    · exact readBytesL_top L t f (lowE L i) n 0 d c top h
    · cases h
  | _, _, .forallSlots .., d, c, top, h | _, _, .existsSlots .., d, c, top, h => by
    simp only [lowE_eqs, quantL] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨cb, _, h⟩ := h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · cases h
  | _, _, .reaches .., d, c, top, h => by
    simp only [lowE_eqs, reachesL, bind, Option.bind_eq_some_iff] at h
    obtain ⟨ca, _, cb, _, h⟩ := h
    split at h
    · exact reachL_top _ _ _ h
    · cases h
  | _, _, .oldG .., _, _, _, h
  | _, _, .oldS .., _, _, _, h
  | _, _, .refEq .., _, _, _, h
  | _, _, .slotRef .., _, _, _, h
  | _, _, .arrNil .., _, _, _, h
  | _, _, .arrCons .., _, _, _, h
  | _, _, .arrGet .., _, _, _, h
  | _, _, .arrSet .., _, _, _, h
  | _, _, .strLit .., _, _, _, h
  | _, _, .strLen .., _, _, _, h
  | _, _, .strCat .., _, _, _, h
  | _, _, .strGet .., _, _, _, h
  | _, _, .strEq .., _, _, _, h
  | _, _, .strLt .., _, _, _, h
  | _, _, .strWeit .., _, _, _, h => by simp [lowE_eqs] at h

theorem Ok.mono {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {c : List II} {P Q : Runner.W → Prop}
    (h : Ok m pc fp K d c P) (hq : ∀ w, P w → Q w) : Ok m pc fp K d c Q := by
  obtain ⟨m', s, a, w, r, p⟩ := h
  exact ⟨m', s, a, w, r, hq w p⟩

/-- Destructure the code of a binary operation. -/
theorem bin_some {Λ : List (Res D)} {Γ : Ctx} {τa τb : Ty} {a : Expr D Γ Λ τa} {b : Expr D Γ Λ τb} {o d : Nat}
    {c : List II} {top : Nat}
    (h : (do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 o d ca cb)) = some (c, top)) :
    ∃ ca ta cb tb, lowE L a d = some (ca, ta) ∧ lowE L b (d + 1) = some (cb, tb) ∧
      c = ca ++ cb ++ [ci o d d (d + 1)] ∧ top = max ta tb := by
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, he⟩ := h
  simp only [bin2, pure, Option.some.injEq, Prod.mk.injEq] at he
  exact ⟨ca, ta, cb, tb, ha, hb, he.1.symm, he.2.symm⟩


/-- A binary operation whose operands the lowering accepts: `a` into `d`, `b` into `d+1`, the instruction `o`. -/
theorem binE_ok {Λ : List (Res D)} {Γ : Ctx} {τa τb : Ty} {a : Expr D Γ Λ τa} {b : Expr D Γ Λ τb} {o d : Nat}
    {c : List II} {top K : Nat} {fp : Runner.W} {W : Runner.Mem → Prop} {ρ : Env D Γ} {m : Runner.Mem}
    {pc : Runner.W} {Pa Pb P : Runner.W → Prop} {g : Runner.W → Runner.W → Option Runner.W}
    (h : (do let ca ← lowE L a d; let cb ← lowE L b (d + 1); pure (bin2 o d ca cb)) = some (c, top))
    (hK : top ≤ K)
    (iha : ∀ ca ta, lowE L a d = some (ca, ta) → ta ≤ K → ∀ m pc, Pre L m pc fp K d ca ρ W → Ok m pc fp K d ca Pa)
    (ihb : ∀ cb tb, lowE L b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc, Pre L m pc fp K (d + 1) cb ρ W →
      Ok m pc fp K (d + 1) cb Pb)
    (hg : ∀ wa wb, Pa wa → Pb wb → ∃ r, g wa wb = some r ∧ P r) (hop : op o = bin g) (ho : o < 256)
    (hp : Pre L m pc fp K d c ρ W) : Ok m pc fp K d c P := by
  obtain ⟨ca, ta, cb, tb, ha, hb, rfl, rfl⟩ := bin_some h
  have := lowE_top b (d + 1) cb tb hb
  exact bin_ok (iha ca ta ha (by omega)) (ihb cb tb hb (by omega)) hg hop ho (by omega) hp

end Gabbro.Stage0.Senke
