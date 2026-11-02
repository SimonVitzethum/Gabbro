module

public import Grammatik.Code.Lower.Stmt
public import Grammatik.Code.Refine.Struct.Mono.Teil1

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr Args)
variable {D : Deklaration}

mutual

/-- **Registers only go up.** -/
theorem lowerE_mono (lay : Layout D) (cenv : List Reg) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : GTy} (e : Expr D Γ Λ τ) (r : Nat) (c : LR),
      lowerE lay cenv e r = some c → r ≤ c.2.2

  | _, _, _, .lit n, r, c, h => by
      simp only [lowerE] at h
      split at h
      · obtain rfl := Option.some.inj h; exact Nat.le_refl _
      · simp only [reduceCtorEq] at h
  | _, _, _, .tru, r, c, h => by
      simp only [lowerE] at h
      obtain rfl := Option.some.inj h; exact Nat.le_refl _
  | _, _, _, .fls, r, c, h => by
      simp only [lowerE] at h
      obtain rfl := Option.some.inj h; exact Nat.le_refl _
  | _, _, τ, .var x, r, c, h => by
      simp only [lowerE] at h
      split at h
      · split at h
        · exact loadG_mono h
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
  | _, _, _, .glob g _, r, c, h => by
      simp only [lowerE] at h
      split at h
      · exact loadG_mono h
      · simp only [reduceCtorEq] at h
  | _, _, _, .ptrOf t _ _ _, r, c, h => by
      simp only [lowerE] at h
      obtain rfl := Option.some.inj h; exact Nat.le_refl _
  | _, _, _, .slot t f i _, r, c, h => by
      simp only [lowerE] at h
      rcases hi : lowerE lay cenv i r with _ | ⟨ci, oi, r1⟩
      · simp only [hi, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv i r _ hi
      simp only [hi] at h
      rcases hs : slotAddr lay t f (.glob (lay.gblk t)) (.int 0 (D.count t - 1)) oi r1 with _ | ⟨ca, oa, r2⟩
      · simp only [hs, reduceCtorEq] at h
      have m2 := slotAddr_mono hs
      simp only [hs] at h
      by_cases hs' : supp (D.typ t f) = true
      · simp only [hs', if_true] at h
        rcases hl : loadG (D.typ t f) oa r2 with _ | ⟨cl, ol, r3⟩
        · simp only [hl, reduceCtorEq] at h
        · have m3 := loadG_mono hl
          simp only [hl] at h
          obtain rfl := Option.some.inj h
          simp only at m1 m2 m3 ⊢
          omega
      · simp only [hs', Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | _, _, _, .thru p t _ f i _, r, c, h => by
      simp only [lowerE] at h
      rcases hp : lowerE lay cenv p r with _ | ⟨cp, op, r1⟩
      · simp only [hp, reduceCtorEq] at h
      have m0 := lowerE_mono lay cenv p r _ hp
      simp only [hp] at h
      rcases hi : lowerE lay cenv i r1 with _ | ⟨ci, oi, r2⟩
      · simp only [hi, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv i r1 _ hi
      simp only [hi] at h
      rcases hs : slotAddr lay t f op (.int 0 (D.count t - 1)) oi r2 with _ | ⟨ca, oa, r3⟩
      · simp only [hs, reduceCtorEq] at h
      have m2 := slotAddr_mono hs
      simp only [hs] at h
      by_cases hs' : supp (D.typ t f) = true
      · simp only [hs', if_true] at h
        rcases hl : loadG (D.typ t f) oa r3 with _ | ⟨cl, ol, r4⟩
        · simp only [hl, reduceCtorEq] at h
        · have m3 := loadG_mono hl
          simp only [hl] at h
          obtain rfl := Option.some.inj h
          simp only at m0 m1 m2 m3 ⊢
          omega
      · simp only [hs', Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | _, _, _, .widen h1 h2 e, r, c, h => by
      simp only [lowerE] at h
      rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
      · simp only [he, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv e r _ he
      simp only [he] at h
      rcases hcv : cvtG (ety e) (ety (Expr.widen h1 h2 e)) oe r1 with _ | ⟨c2, o2, r2⟩
      · simp only [hcv, reduceCtorEq] at h
      have m2 := cvtG_mono hcv
      simp only [hcv] at h
      split at h
      · obtain rfl := Option.some.inj h
        simp only at m1 m2 ⊢
        omega
      · simp only [reduceCtorEq] at h
  | _, _, _, .add a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : binRest .add (ety (Expr.add a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := binRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .sub a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : binRest .sub (ety (Expr.sub a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := binRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .mul a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : binRest .mul (ety (Expr.mul a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := binRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .neg a, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hr : binRest .sub (ety (Expr.neg a)) (.int 0 0) (ety a) (.int (twid (.int 0 0)) 0) oa r1
        with _ | ⟨ct, ot, r2⟩
      · simp only [hr, reduceCtorEq] at h
      have m3 := binRest_mono hr
      simp only [hr] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m3 ⊢
      omega
  | _, _, _, .lt a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : cmpRest .ult .slt (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := cmpRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .le a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : cmpRest .ule .sle (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := cmpRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .eq a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : cmpRest .eq .eq (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := cmpRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .and a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 ⊢
      omega
  | _, _, _, .or a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 ⊢
      omega
  | _, _, _, .not a, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      obtain rfl := Option.some.inj h
      simp only at m1 ⊢
      omega
  | _, _, _, .fnref .., r, c, h => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .oldG .., r, c, h => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .oldS .., r, c, h => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .div h0 h1 a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : divRest .udiv (ety (Expr.div h0 h1 a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := divRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .rem h0 h1 a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : divRest .urem (ety (Expr.rem h0 h1 a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := divRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .sdiv (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb', reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .sdiv (jsdiv l1 h1 l2 h2) (ety (Expr.sdiv hb a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .srem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb', reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .srem (jsrem l1 h1 l2 h2) (ety (Expr.srem hb a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .getBytes .., r, c, h => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .band (h1 := h1) (h2 := h2) h0 h0' a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb', reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .and (jbit h1 h2 h1) (ety (Expr.band h0 h0' a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .bor (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb', reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .or (jbit h1 h2 (2 ^ w - 1)) (ety (Expr.bor w h0 h0' hw1 hw2 a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .bxor (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb', reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .xor (jbit h1 h2 (2 ^ w - 1)) (ety (Expr.bxor w h0 h0' hw1 hw2 a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .shl (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb', reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .shl (jshl h1 h2) (ety (Expr.shl w hw1 hw2 h0 h0' a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .shr (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp only [hb', reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .lshr (jshr h1 h2) (ety (Expr.shr w hw1 hw2 h0 h0' a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp only [List.append_assoc, hr, Option.map_none, reduceCtorEq] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .fllt .., r, c, h => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .flle .., r, c, h => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .none .., r, c, h => by
      simp only [lowerE] at h
      split at h
      · obtain rfl := Option.some.inj h; exact Nat.le_refl _
      · simp only [reduceCtorEq] at h
  | _, _, _, .some (n := n) e, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv e r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv e r _ ha
      simp only [ha] at h
      split at h
      · rcases hcv : cvtG (.int 0 (n - 1)) (.int (-1) (n - 1)) oa r1 with _ | ⟨c2, o2, r2⟩
        · simp only [Int.reduceNeg, hcv, Option.map_none, reduceCtorEq] at h
        have m2 := cvtG_mono hcv
        simp only [hcv, Option.map_some] at h
        obtain rfl := Option.some.inj h
        simp only at m1 m2 ⊢
        omega
      · simp only [reduceCtorEq] at h
  | _, _, _, .istSome e, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv e r with _ | ⟨ca, oa, r1⟩
      · simp only [ha, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv e r _ ha
      simp only [ha] at h
      split at h
      · obtain rfl := Option.some.inj h
        simp only at m1 ⊢
        omega
      · simp only [reduceCtorEq] at h
  | _, _, _, .case cs i nutz, r, c, h => by
      simp only [lowerE] at h
      split at h
      · exact lowerNutz_mono lay cenv _ _ _ nutz r c h
      · simp only [reduceCtorEq] at h
  | _, _, _, .why .., r, c, h => by
      simp only [lowerE] at h
      split at h
      · obtain rfl := Option.some.inj h; exact Nat.le_refl _
      · simp only [reduceCtorEq] at h
  | _, _, _, .forallSlots .., r, c, h => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .existsSlots .., r, c, h => by
      simp only [lowerE, reduceCtorEq] at h
  | _, _, _, .reaches .., r, c, h => by
      simp only [lowerE, reduceCtorEq] at h

theorem lowerNutz_mono (lay : Layout D) (cenv : List Reg) (W L i : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option Gabbro.Grammatik.Ty}
      (nutz : Gabbro.Grammatik.NutzlastExpr D Γ Λ c) (r : Nat) (c0 : LR),
      lowerNutz lay cenv W L i nutz r = some c0 → r ≤ c0.2.2
  | _, _, _, .empty, r, c0, h => by
      simp only [lowerNutz, Option.some.injEq] at h
      subst h
      exact Nat.le_refl _
  | _, _, _, .val (τ := .int lo hi) e, r, c0, h => by
      simp only [lowerNutz] at h
      rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
      · simp only [he, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv e r _ he
      simp only [he] at h
      rcases hn : numCode lo hi W L i oe r1 with ⟨cn, on, r2⟩
      have m2 := numCode_mono (lo := lo) (hi := hi) (W := W) (L := L) (i := i) (oe := oe) (r := r1)
      rw [hn] at m2 h
      simp only [Option.some.injEq] at h
      subst h
      simp only at m1 m2 ⊢
      omega

end

end Gabbro.Code.Lower
