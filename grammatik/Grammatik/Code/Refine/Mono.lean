import Grammatik.Code.Lower.Stmt

/-
  File:      Grammatik/Code/Refine/Mono.lean
  Subject:   TRACK L, PHASE L1 -- THE LOWERING ONLY USES REGISTERS AND LABELS UPWARD, AND ITS
             BLOCKS HAVE NO PHIS: `lowerE_mono`, `lowerS_shape`/`lowerB_shape`/`lowerEnd_shape`.

  The shape lemmas say of every lowering result: the first block carries the entry label, no
  block has phis (a jump into it leaves the registers alone), and the counters did not fall.
-/

namespace Gabbro.Code.Lower


variable [Conf]

open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr Args)

variable {D : Deklaration}

theorem cvt_mono (src dst : Nat) (sg : Bool) (o : Opd) (r : Nat) : r ≤ (cvt src dst sg o r).2.2 := by
  unfold cvt
  split <;> try (simp; done)
  split <;> simp

theorem cvtG_mono {σ τ : GTy} {o : Opd} {r : Nat} {c : LR} (h : cvtG σ τ o r = some c) : r ≤ c.2.2 := by
  unfold cvtG at h
  split at h
  · obtain rfl := Option.some.inj h; exact cvt_mono _ _ _ _ _
  · simp at h

theorem loadG_mono {τ : GTy} {p : Opd} {r : Nat} {c : LR} (h : loadG τ p r = some c) : r ≤ c.2.2 := by
  unfold loadG at h
  split at h <;> first
    | (obtain rfl := Option.some.inj h; simp; done)
    | (split at h <;> first
        | (obtain rfl := Option.some.inj h; simp; done)
        | (simp at h; done))
    | (simp at h; done)

theorem slotAddr_mono {lay : Layout D} {t : D.Tab} {f : D.Feld t} {base : Opd} {iτ : GTy} {oi : Opd}
    {r : Nat} {c : LR} (h : slotAddr lay t f base iτ oi r = some c) : r ≤ c.2.2 := by
  unfold slotAddr at h
  split at h
  · split at h
    · rename_i cc oo rr hc
      have := cvtG_mono hc
      obtain rfl := Option.some.inj h
      simp only at this ⊢
      omega
    · simp at h
  · simp at h

theorem binRest_mono {op : BinOp} {τ σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : binRest op τ σa σb oa ob r = some c) : r ≤ c.2.2 := by
  unfold binRest at h
  rcases hc1 : cvtG σa τ oa r with _ | ⟨c1, oa', r1⟩
  · simp [hc1] at h
  · have m1 := cvtG_mono hc1
    simp only [hc1] at h
    rcases hc2 : cvtG σb τ ob r1 with _ | ⟨c2, ob', r2⟩
    · simp [hc2] at h
    · have m2 := cvtG_mono hc2
      simp only [hc2] at h
      split at h
      · obtain rfl := Option.some.inj h
        simp only at m1 m2 ⊢
        omega
      · simp at h

theorem divRest_mono {op : BinOp} {τ σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : divRest op τ σa σb oa ob r = some c) : r ≤ c.2.2 := by
  unfold divRest at h
  split at h
  · rename_i la ha lb hb
    simp only at h
    rcases hc1 : cvtG (.int la ha) (joinT (.int la ha) (.int lb hb)) oa r with _ | ⟨c1, oa', r1⟩
    · simp [hc1] at h
    have m1 := cvtG_mono hc1
    simp only [hc1] at h
    rcases hc2 : cvtG (.int lb hb) (joinT (.int la ha) (.int lb hb)) ob r1 with _ | ⟨c2, ob', r2⟩
    · simp [hc2] at h
    have m2 := cvtG_mono hc2
    simp only [hc2] at h
    split at h
    · rcases hc3 : cvtG (joinT (.int la ha) (.int lb hb)) τ (.reg r2) (r2 + 1) with _ | ⟨c3, o3, r3⟩
      · simp [hc3] at h
      have m3 := cvtG_mono hc3
      simp only [hc3] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
    · simp at h
  · simp at h

theorem cmpRest_mono {pu ps : IPred} {σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : cmpRest pu ps σa σb oa ob r = some c) : r ≤ c.2.2 := by
  unfold cmpRest at h
  split at h
  · dsimp only at h
    split at h
    · rename_i c1 oa' r1 hc1
      split at h
      · rename_i c2 ob' r2 hc2
        split at h
        · obtain rfl := Option.some.inj h
          have m1 := cvtG_mono hc1
          have m2 := cvtG_mono hc2
          simp only at m1 m2 ⊢
          omega
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem cvtM_mono {τ : GTy} {o : Opd} {r : Nat} {c : LR} (h : cvtM τ o r = some c) : r ≤ c.2.2 := by
  unfold cvtM at h
  split at h <;> first
    | (obtain rfl := Option.some.inj h; simp; done)
    | (split at h <;> first
        | (obtain rfl := Option.some.inj h; simp; done)
        | (simp at h; done))
    | (simp at h; done)

theorem storeTo_mono {τ : GTy} {oe : Opd} {r1 : Nat} {p : Opd} {cs : List Instr} {r2 : Nat}
    (h : storeTo τ oe r1 p = some (cs, r2)) : r1 ≤ r2 := by
  unfold storeTo at h
  rcases hc : cvtM τ oe r1 with _ | ⟨cm, om, r3⟩
  · simp [hc] at h
  · have := cvtM_mono hc
    simp only [hc] at h
    have := (Option.some.inj h)
    simp only [Prod.mk.injEq] at this
    obtain ⟨_, rfl⟩ := this
    simpa using cvtM_mono hc

theorem bindCode_mono {τ : GTy} {oe : Opd} {r1 : Nat} {cb : List Instr} {a : Nat} {r2 : Nat}
    (h : bindCode τ oe r1 = some (cb, a, r2)) : r1 ≤ a ∧ a + 1 = r2 := by
  unfold bindCode at h
  rcases hc : cvtM τ oe r1 with _ | ⟨cm, om, r3⟩
  · simp [hc] at h
  · have := cvtM_mono hc
    simp only [hc] at h
    split at h
    · have := (Option.some.inj h)
      simp only [Prod.mk.injEq] at this
      obtain ⟨_, rfl, rfl⟩ := this
      exact ⟨by simpa using cvtM_mono hc, rfl⟩
    · simp at h

theorem payCode_mono {top : Int} {W L : Nat} {lo hi : Int} {ov : Opd} {r : Nat} {c : LR}
    (h : payCode top W L lo hi ov r = some c) : r ≤ c.2.2 := by
  unfold payCode at h
  split at h
  · rcases hc : cvt W (Ar.wid (min 0 lo) (max top hi)) false ov r with ⟨c1, o1, r1⟩
    have m1 := cvt_mono W (Ar.wid (min 0 lo) (max top hi)) false ov r
    rw [hc] at m1 h
    simp only at m1 h
    rcases hv : cvtG (.int (min 0 lo) (max top hi)) (.int lo hi) (.reg (r1 + 1)) (r1 + 2) with
      _ | ⟨c3, o3, r3⟩
    · simp [hv] at h
    have m3 := cvtG_mono hv
    simp only [hv] at h
    obtain rfl := Option.some.inj h
    simp only at m1 m3 ⊢
    omega
  · simp at h

/-- **Registers only go up.** -/
theorem lowerE_mono (lay : Layout D) (cenv : List Reg) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : GTy} (e : Expr D Γ Λ τ) (r : Nat) (c : LR),
      lowerE lay cenv e r = some c → r ≤ c.2.2

  | _, _, _, .lit n, r, c, h => by
      simp only [lowerE] at h
      split at h
      · obtain rfl := Option.some.inj h; exact Nat.le_refl _
      · simp at h
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
        · simp at h
      · simp at h
  | _, _, _, .glob g _, r, c, h => by
      simp only [lowerE] at h
      split at h
      · exact loadG_mono h
      · simp at h
  | _, _, _, .ptrOf t _ _ _, r, c, h => by
      simp only [lowerE] at h
      obtain rfl := Option.some.inj h; exact Nat.le_refl _
  | _, _, _, .slot t f i _, r, c, h => by
      simp only [lowerE] at h
      rcases hi : lowerE lay cenv i r with _ | ⟨ci, oi, r1⟩
      · simp [hi] at h
      have m1 := lowerE_mono lay cenv i r _ hi
      simp only [hi] at h
      rcases hs : slotAddr lay t f (.glob (lay.gblk t)) (.int 0 (D.count t - 1)) oi r1 with _ | ⟨ca, oa, r2⟩
      · simp [hs] at h
      have m2 := slotAddr_mono hs
      simp only [hs] at h
      by_cases hs' : supp (D.typ t f) = true
      · simp only [hs', if_true] at h
        rcases hl : loadG (D.typ t f) oa r2 with _ | ⟨cl, ol, r3⟩
        · simp [hl] at h
        · have m3 := loadG_mono hl
          simp only [hl] at h
          obtain rfl := Option.some.inj h
          simp only at m1 m2 m3 ⊢
          omega
      · simp [hs'] at h
  | _, _, _, .thru p t _ f i _, r, c, h => by
      simp only [lowerE] at h
      rcases hp : lowerE lay cenv p r with _ | ⟨cp, op, r1⟩
      · simp [hp] at h
      have m0 := lowerE_mono lay cenv p r _ hp
      simp only [hp] at h
      rcases hi : lowerE lay cenv i r1 with _ | ⟨ci, oi, r2⟩
      · simp [hi] at h
      have m1 := lowerE_mono lay cenv i r1 _ hi
      simp only [hi] at h
      rcases hs : slotAddr lay t f op (.int 0 (D.count t - 1)) oi r2 with _ | ⟨ca, oa, r3⟩
      · simp [hs] at h
      have m2 := slotAddr_mono hs
      simp only [hs] at h
      by_cases hs' : supp (D.typ t f) = true
      · simp only [hs', if_true] at h
        rcases hl : loadG (D.typ t f) oa r3 with _ | ⟨cl, ol, r4⟩
        · simp [hl] at h
        · have m3 := loadG_mono hl
          simp only [hl] at h
          obtain rfl := Option.some.inj h
          simp only at m0 m1 m2 m3 ⊢
          omega
      · simp [hs'] at h
  | _, _, _, .widen h1 h2 e, r, c, h => by
      simp only [lowerE] at h
      rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      have m1 := lowerE_mono lay cenv e r _ he
      simp only [he] at h
      rcases hcv : cvtG (ety e) (ety (Expr.widen h1 h2 e)) oe r1 with _ | ⟨c2, o2, r2⟩
      · simp [hcv] at h
      have m2 := cvtG_mono hcv
      simp only [hcv] at h
      split at h
      · obtain rfl := Option.some.inj h
        simp only at m1 m2 ⊢
        omega
      · simp at h
  | _, _, _, .add a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : binRest .add (ety (Expr.add a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := binRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .sub a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : binRest .sub (ety (Expr.sub a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := binRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .mul a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : binRest .mul (ety (Expr.mul a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := binRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .neg a, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hr : binRest .sub (ety (Expr.neg a)) (.int 0 0) (ety a) (.int (twid (.int 0 0)) 0) oa r1
        with _ | ⟨ct, ot, r2⟩
      · simp [hr] at h
      have m3 := binRest_mono hr
      simp only [hr] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m3 ⊢
      omega
  | _, _, _, .lt a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : cmpRest .ult .slt (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := cmpRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .le a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : cmpRest .ule .sle (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := cmpRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .eq a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : cmpRest .eq .eq (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := cmpRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .and a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 ⊢
      omega
  | _, _, _, .or a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 ⊢
      omega
  | _, _, _, .not a, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      obtain rfl := Option.some.inj h
      simp only at m1 ⊢
      omega
  | _, _, _, .fnref .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .oldG .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .oldS .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .div h0 h1 a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : divRest .udiv (ety (Expr.div h0 h1 a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := divRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .rem h0 h1 a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb
      simp only [hb] at h
      rcases hr : divRest .urem (ety (Expr.rem h0 h1 a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := divRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .sdiv .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .srem .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .getBytes .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .band .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .bor .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .bxor .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .shl .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .shr .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .fllt .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .flle .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .none .., r, c, h => by
      simp only [lowerE] at h
      split at h
      · obtain rfl := Option.some.inj h; exact Nat.le_refl _
      · simp at h
  | _, _, _, .some (n := n) e, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv e r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv e r _ ha
      simp only [ha] at h
      split at h
      · rcases hcv : cvtG (.int 0 (n - 1)) (.int (-1) (n - 1)) oa r1 with _ | ⟨c2, o2, r2⟩
        · simp [hcv] at h
        have m2 := cvtG_mono hcv
        simp only [hcv, Option.map_some] at h
        obtain rfl := Option.some.inj h
        simp only at m1 m2 ⊢
        omega
      · simp at h
  | _, _, _, .istSome e, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv e r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv e r _ ha
      simp only [ha] at h
      split at h
      · obtain rfl := Option.some.inj h
        simp only at m1 ⊢
        omega
      · simp at h
  | _, _, _, .case .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .why .., r, c, h => by
      simp only [lowerE] at h
      split at h
      · obtain rfl := Option.some.inj h; exact Nat.le_refl _
      · simp at h
  | _, _, _, .forallSlots .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .existsSlots .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .reaches .., r, c, h => by
      simp [lowerE] at h

theorem lowerArgs_mono (lay : Layout D) (cenv : List Reg) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List GTy} (args : Args D Γ Λ τs) (r : Nat)
      (c : List Instr × List Opd × Nat), lowerArgs lay cenv args r = some c → r ≤ c.2.2
  | _, _, _, .nil, r, c, h => by
      simp only [lowerArgs, Option.some.injEq] at h
      subst h
      exact Nat.le_refl _
  | _, _, _, .cons e rest, r, c, h => by
      simp only [lowerArgs] at h
      rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      have m1 := lowerE_mono lay cenv e r _ he
      simp only [he] at h
      rcases hr : lowerArgs lay cenv rest r1 with _ | ⟨cr, os, r2⟩
      · simp [hr] at h
      have m2 := lowerArgs_mono lay cenv rest r1 _ hr
      simp only [hr, Option.some.injEq] at h
      subst h
      simp only at m1 m2 ⊢
      omega

variable {V : Vertrag D}

/-- The facts every lowering result has. -/
def Shape (lb : Lbl) (st st' : St) (blks : List Block) : Prop :=
  (∃ b bs, blks = b :: bs ∧ b.lbl = lb) ∧ (∀ b ∈ blks, b.phis = []) ∧ st.r ≤ st'.r

theorem lowerErg_shape (lay : Layout D) (cenv : List Reg) {Γ : Ctx} {Λ : List (Res D)} {eo : Option GTy}
    (e : ErgExpr D Γ Λ eo) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerErg lay cenv e lb st = some (blks, st')) : Shape lb st st' blks := by
  cases e with
  | empty =>
      simp only [lowerErg] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨⟨_, _, rfl, rfl⟩, by simp, Nat.le_refl _⟩
  | val e =>
      simp only [lowerErg] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      have m1 := lowerE_mono lay cenv e st.r _ he
      simp only [he] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨⟨_, _, rfl, rfl⟩, by simp, m1⟩

mutual

theorem lowerS_shape (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Gabbro.Grammatik.Stmt D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerS lay cenv lv s lb k st = some (blks, st') → Shape lb st st' blks
  | _, _, _, _, .assignSlot t f i e _ _, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      by_cases hs : supp (D.typ t f) = true
      · simp only [hs, if_true] at h
        rcases hi : lowerE lay cenv i st.r with _ | ⟨ci, oi, r1⟩
        · simp [hi] at h
        have m1 := lowerE_mono lay cenv i st.r _ hi
        simp only [hi] at h
        rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
        · simp [he] at h
        have m2 := lowerE_mono lay cenv e r1 _ he
        simp only [he] at h
        rcases hsa : slotAddr lay t f (.glob (lay.gblk t)) (.int 0 (D.count t - 1)) oi r2 with
          _ | ⟨ca, oa, r3⟩
        · simp [hsa] at h
        have m3 := slotAddr_mono hsa
        simp only [hsa] at h
        rcases hst : storeTo (D.typ t f) oe r3 oa with _ | ⟨cs, r4⟩
        · simp [hst] at h
        have m4 := storeTo_mono hst
        simp only [hst] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, by simp, ?_⟩
        simp only at m1 m2 m3 ⊢
        omega
      · simp [hs] at h
  | _, _, _, _, .assignThru p t _ f i e _ _, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      by_cases hs : supp (D.typ t f) = true
      · simp only [hs, if_true] at h
        rcases hp : lowerE lay cenv p st.r with _ | ⟨cp, op, r1⟩
        · simp [hp] at h
        have m0 := lowerE_mono lay cenv p st.r _ hp
        simp only [hp] at h
        rcases hi : lowerE lay cenv i r1 with _ | ⟨ci, oi, r2⟩
        · simp [hi] at h
        have m1 := lowerE_mono lay cenv i r1 _ hi
        simp only [hi] at h
        rcases he : lowerE lay cenv e r2 with _ | ⟨ce, oe, r3⟩
        · simp [he] at h
        have m2 := lowerE_mono lay cenv e r2 _ he
        simp only [he] at h
        rcases hsa : slotAddr lay t f op (.int 0 (D.count t - 1)) oi r3 with _ | ⟨ca, oa, r4⟩
        · simp [hsa] at h
        have m3 := slotAddr_mono hsa
        simp only [hsa] at h
        rcases hst : storeTo (D.typ t f) oe r4 oa with _ | ⟨cs, r5⟩
        · simp [hst] at h
        have m4 := storeTo_mono hst
        simp only [hst] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, by simp, ?_⟩
        simp only at m0 m1 m2 m3 ⊢
        omega
      · simp [hs] at h
  | _, _, _, _, .assignGlob g e _ _, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      by_cases hs : supp (D.gtyp g) = true
      · simp only [hs, if_true] at h
        rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
        · simp [he] at h
        have m1 := lowerE_mono lay cenv e st.r _ he
        simp only [he] at h
        rcases hst : storeTo (D.gtyp g) oe r1 (.glob (lay.ggblk g)) with _ | ⟨cs, r2⟩
        · simp [hst] at h
        have m2 := storeTo_mono hst
        simp only [hst] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, by simp, ?_⟩
        simp only at m1 m2 ⊢
        omega
      · simp [hs] at h
  | _, _, _, _, Gabbro.Grammatik.Stmt.assignVar (τ := τ) x e, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      rcases hc : cenv[varIdx x]? with _ | a
      · simp [hc] at h
      simp only [hc] at h
      by_cases hs : supp τ = true
      · simp only [hs, if_true] at h
        rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
        · simp [he] at h
        have m1 := lowerE_mono lay cenv e st.r _ he
        simp only [he] at h
        rcases hst : storeTo τ oe r1 (.reg a) with _ | ⟨cs, r2⟩
        · simp [hst] at h
        have m2 := storeTo_mono hst
        simp only [hst] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, by simp, ?_⟩
        simp only at m1 m2 ⊢
        omega
      · simp [hs] at h
  | _, _, _, _, .ite c tb eb, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      rcases hc : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
      · simp [hc] at h
      have m1 := lowerE_mono lay cenv c st.r _ hc
      simp only [hc] at h
      rcases hb1 : lowerB lay cenv lv tb st.l k ⟨r1, st.l + 2⟩ with _ | ⟨bt, s1⟩
      · simp [hb1] at h
      have S1 := lowerB_shape lay cenv lv tb st.l k ⟨r1, st.l + 2⟩ s1 bt hb1
      simp only [hb1] at h
      rcases hb2 : lowerB lay cenv lv eb (st.l + 1) k s1 with _ | ⟨be, s2⟩
      · simp [hb2] at h
      have S2 := lowerB_shape lay cenv lv eb (st.l + 1) k s1 s2 be hb2
      simp only [hb2] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons, List.mem_append] at hb
        rcases hb with rfl | hb | hb
        · rfl
        · exact S1.2.1 b hb
        · exact S2.2.1 b hb
      · have a1 := S1.2.2
        have a2 := S2.2.2
        simp only at m1 a1 a2 ⊢
        omega
  | _, _, _, _, .ret e _, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      exact lowerErg_shape lay cenv e lb st st' blks h
  | _, _, _, _, .putBytes .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .shift .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .onOption (n := n) o p a, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      rcases ho : lowerE lay cenv o st.r with _ | ⟨co, oo, r1⟩
      · simp [ho] at h
      have m1 := lowerE_mono lay cenv o st.r _ ho
      simp only [ho] at h
      split at h
      · rcases hv : cvtG (.int (-1) (n - 1)) (.int 0 (n - 1)) oo r1 with _ | ⟨cv, ov, r2⟩
        · simp [hv] at h
        have m2 := cvtG_mono hv
        simp only [hv] at h
        rcases hb : bindCode (.int 0 (n - 1)) ov r2 with _ | ⟨cb, c, r3⟩
        · simp [hb] at h
        have m3 := bindCode_mono hb
        simp only [hb] at h
        rcases hb1 : lowerB lay cenv lv a st.l k ⟨r3, st.l + 3⟩ with _ | ⟨ba, s1⟩
        · simp [hb1] at h
        have S1 := lowerB_shape lay cenv lv a st.l k ⟨r3, st.l + 3⟩ s1 ba hb1
        simp only [hb1] at h
        rcases hb2 : lowerB lay (c :: cenv) lv p (st.l + 2) k s1 with _ | ⟨bp, s2⟩
        · simp [hb2] at h
        have S2 := lowerB_shape lay (c :: cenv) lv p (st.l + 2) k s1 s2 bp hb2
        simp only [hb2] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons, List.mem_append] at hb
          rcases hb with rfl | rfl | hb | hb
          · rfl
          · rfl
          · exact S1.2.1 b hb
          · exact S2.2.1 b hb
        · have a1 := S1.2.2
          have a2 := S2.2.2
          simp only at m1 m2 m3 a1 a2 ⊢
          omega
      · simp at h
  | _, _, _, _, .onTag (cs := cs) v arms, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      rcases hv : lowerE lay cenv v st.r with _ | ⟨cv, ov, r1⟩
      · simp [hv] at h
      have m1 := lowerE_mono lay cenv v st.r _ hv
      simp only [hv] at h
      split at h
      · rcases hga : lowerAr lay cenv lv (sumTop cs) (Ar.wid 0 (sumTop cs)) cs.length ov arms (st.l + 1) k
            ⟨r1 + 1, st.l + 1 + cs.length⟩ with _ | ⟨ba, s1⟩
        · simp [hga] at h
        have G := lowerAr_shape lay cenv lv (sumTop cs) (Ar.wid 0 (sumTop cs)) cs.length ov arms
          (st.l + 1) k ⟨r1 + 1, st.l + 1 + cs.length⟩ s1 ba hga
        simp only [hga] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | rfl | hb
          · rfl
          · rfl
          · exact G.1 b hb
        · have a1 := G.2
          simp only at m1 a1 ⊢
          omega
      · simp at h
  | _, _, _, _, .onWhy (n := n) r arms, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      rcases hr : lowerE lay cenv r st.r with _ | ⟨cr, orr, r1⟩
      · simp [hr] at h
      have m1 := lowerE_mono lay cenv r st.r _ hr
      simp only [hr] at h
      split at h
      · rcases hga : lowerGA lay cenv lv arms (st.l + 1) k ⟨r1, st.l + 1 + n⟩ with _ | ⟨ba, s1⟩
        · simp [hga] at h
        have G := lowerGA_shape lay cenv lv arms (st.l + 1) k ⟨r1, st.l + 1 + n⟩ s1 ba hga
        simp only [hga] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | rfl | hb
          · rfl
          · rfl
          · exact G.1 b hb
        · have a1 := G.2
          simp only at m1 a1 ⊢
          omega
      · simp at h
  | _, _, _, _, .call f args _ _, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
      · simp [hla] at h
      have m1 := lowerArgs_mono lay cenv args st.r _ hla
      simp only [hla, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨⟨_, _, rfl, rfl⟩, by simp, ?_⟩
      simp only at m1 ⊢
      omega
  | _, _, _, _, .callInd .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .locks .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .breaking .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .traverse t _ body, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      by_cases hc : 0 ≤ D.count t ∧ Ar.Fits 0 (D.count t) 128
      · simp only [hc, and_self, if_true] at h
        rcases hv : cvtG (.int 0 (D.count t)) (.int 0 (D.count t - 1)) (.reg st.r) (st.r + 1) with
          _ | ⟨cv, ov, r1⟩
        · simp [hv] at h
        have m1 := cvtG_mono hv
        simp only [hv] at h
        rcases hb : bindCode (.int 0 (D.count t - 1)) ov r1 with _ | ⟨cb, a, r2⟩
        · simp [hb] at h
        have m2 := bindCode_mono hb
        simp only [hb] at h
        rcases hb2 : lowerB lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) ⟨r2, st.l + 4⟩ with
          _ | ⟨bb, s1⟩
        · simp [hb2] at h
        have S2 := lowerB_shape lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) ⟨r2, st.l + 4⟩ s1 bb hb2
        simp only [hb2] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | rfl | rfl | rfl | hb
          · rfl
          · rfl
          · rfl
          · rfl
          · exact S2.2.1 b hb
        · have a2 := S2.2.2
          simp only at m1 m2 a2 ⊢
          omega
      · simp [hc] at h
  | _, _, _, _, .retry n bis body ueb, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      by_cases hc : retryOk n = true
      · simp only [hc, if_true] at h
        rcases hcb : lowerE lay cenv bis (st.r + 1) with _ | ⟨cb, ob, r1⟩
        · simp [hcb] at h
        have m1 := lowerE_mono lay cenv bis (st.r + 1) _ hcb
        simp only [hcb] at h
        rcases hb1 : lowerB lay cenv (k, st.l + 3) body (st.l + 4) (st.l + 3) ⟨r1, st.l + 5⟩ with _ | ⟨bb, s1⟩
        · simp [hb1] at h
        have S1 := lowerB_shape lay cenv (k, st.l + 3) body (st.l + 4) (st.l + 3) ⟨r1, st.l + 5⟩ s1 bb hb1
        simp only [hb1] at h
        rcases hb2 : lowerB lay cenv lv ueb (st.l + 2) k s1 with _ | ⟨bo, s2⟩
        · simp [hb2] at h
        have S2 := lowerB_shape lay cenv lv ueb (st.l + 2) k s1 s2 bo hb2
        simp only [hb2] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons, List.mem_append] at hb
          rcases hb with rfl | rfl | rfl | rfl | hb | hb
          · rfl
          · rfl
          · rfl
          · rfl
          · exact S1.2.1 b hb
          · exact S2.2.1 b hb
        · have a1 := S1.2.2
          have a2 := S2.2.2
          simp only at m1 a1 a2 ⊢
          omega
      · simp [hc] at h
  | _, _, _, _, .forever _ _ body, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      exact lowerB_shape lay cenv (k, lb) body lb lb st st' blks h
  | _, _, _, _, .axiomCall .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .regWrite .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .transition .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .publish .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .advances .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .retires .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .retWhy .., lb, k, st, st', blks, h => by
      simp [lowerS] at h
  | _, _, _, _, .leave .., lb, k, st, st', blks, h => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨_, _, rfl, rfl⟩, by simp, Nat.le_refl _⟩
  | _, _, _, _, .next .., lb, k, st, st', blks, h => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨_, _, rfl, rfl⟩, by simp, Nat.le_refl _⟩

theorem lowerB_shape (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Gabbro.Grammatik.Block D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerB lay cenv lv b lb k st = some (blks, st') → Shape lb st st' blks
  | _, _, _, _, .nil, lb, k, st, st', blks, h => by
      simp only [lowerB] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨⟨_, _, rfl, rfl⟩, by simp, Nat.le_refl _⟩
  | _, _, _, _, .cons s rest, lb, k, st, st', blks, h => by
      simp only [lowerB] at h
      rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
      · simp [hs] at h
      have S1 := lowerS_shape lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs
      simp only [hs] at h
      rcases hr : lowerB lay cenv lv rest st.l k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      have S2 := lowerB_shape lay cenv lv rest st.l k s1 s2 b2 hr
      simp only [hr] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      obtain ⟨⟨hd, tl, hdt, hl⟩, hp, hm⟩ := S1
      refine ⟨⟨hd, tl ++ b2, by rw [hdt]; rfl, hl⟩, ?_, ?_⟩
      · intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact hp b hb
        · exact S2.2.1 b hb
      · have a2 := S2.2.2
        simp only at hm a2 ⊢
        omega
  | _, _, _, _, Gabbro.Grammatik.Block.bind (τ := τ) e rest, lb, k, st, st', blks, h => by
      simp only [lowerB] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      have m1 := lowerE_mono lay cenv e st.r _ he
      simp only [he] at h
      rcases hb : bindCode τ oe r1 with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      have m2 := bindCode_mono hb
      simp only [hb] at h
      rcases hr : lowerB lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp [hr] at h
      have S2 := lowerB_shape lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ s2 b2 hr
      simp only [hr] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · rfl
        · exact S2.2.1 b hb
      · have a2 := S2.2.2
        simp only at m1 m2 a2 ⊢
        omega
  | _, _, _, _, .check c sonst rest, lb, k, st, st', blks, h => by
      simp only [lowerB] at h
      rcases hc : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
      · simp [hc] at h
      have m1 := lowerE_mono lay cenv c st.r _ hc
      simp only [hc] at h
      rcases hb1 : lowerEnd lay cenv lv sonst st.l ⟨r1, st.l + 2⟩ with _ | ⟨be, s1⟩
      · simp [hb1] at h
      have S1 := lowerEnd_shape lay cenv lv sonst st.l ⟨r1, st.l + 2⟩ s1 be hb1
      simp only [hb1] at h
      rcases hb2 : lowerB lay cenv lv rest (st.l + 1) k s1 with _ | ⟨br, s2⟩
      · simp [hb2] at h
      have S2 := lowerB_shape lay cenv lv rest (st.l + 1) k s1 s2 br hb2
      simp only [hb2] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons, List.mem_append] at hb
        rcases hb with rfl | hb | hb
        · rfl
        · exact S1.2.1 b hb
        · exact S2.2.1 b hb
      · have a1 := S1.2.2
        have a2 := S2.2.2
        simp only at m1 a1 a2 ⊢
        omega
  | _, _, _, _, Gabbro.Grammatik.Block.bindCall (τ := τ) f args _ _ _ rest, lb, k, st, st', blks, h => by
      simp only [lowerB] at h
      rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
      · simp [hla] at h
      have m1 := lowerArgs_mono lay cenv args st.r _ hla
      simp only [hla] at h
      rcases hb : bindCode τ (.reg r1) (r1 + 1) with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      have m2 := bindCode_mono hb
      simp only [hb] at h
      rcases hr : lowerB lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp [hr] at h
      have S2 := lowerB_shape lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ s2 b2 hr
      simp only [hr] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · rfl
        · exact S2.2.1 b hb
      · have a2 := S2.2.2
        simp only at m1 m2 a2 ⊢
        omega
  | _, _, _, _, .bindCallInd .., lb, k, st, st', blks, h => by
      simp [lowerB] at h
  | _, _, _, _, .bindCallElse .., lb, k, st, st', blks, h => by
      simp [lowerB] at h
  | _, _, _, _, .bindAxiom .., lb, k, st, st', blks, h => by
      simp [lowerB] at h
  | _, _, _, _, .bindAxiomElse .., lb, k, st, st', blks, h => by
      simp [lowerB] at h
  | _, _, _, _, .regRead .., lb, k, st, st', blks, h => by
      simp [lowerB] at h
  | _, _, _, _, .regReadElse .., lb, k, st, st', blks, h => by
      simp [lowerB] at h
  | _, _, _, _, .awaits .., lb, k, st, st', blks, h => by
      simp [lowerB] at h
  | _, _, _, _, .exchange .., lb, k, st, st', blks, h => by
      simp [lowerB] at h
  | _, _, _, _, Gabbro.Grammatik.Block.narrow (lo := lo) (hi := hi) e lo' hi' sonst rest, lb, k, st, st', blks,
      h => by
      simp only [lowerB] at h
      rcases hc : lowerE lay cenv (Expr.and (Expr.le (Expr.lit lo') e) (Expr.le e (Expr.lit hi'))) st.r with
        _ | ⟨cc, oc, r1⟩
      · simp [hc] at h
      have m1 := lowerE_mono lay cenv _ st.r _ hc
      simp only [hc] at h
      rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
      · simp [he] at h
      have m2 := lowerE_mono lay cenv e r1 _ he
      simp only [he] at h
      rcases hv : cvtG (.int lo hi) (.int lo' hi') oe r2 with _ | ⟨cv, ov, r3⟩
      · simp [hv] at h
      have m3 := cvtG_mono hv
      simp only [hv] at h
      rcases hb : bindCode (.int lo' hi') ov r3 with _ | ⟨cb, a, r4⟩
      · simp [hb] at h
      have m4 := bindCode_mono hb
      simp only [hb] at h
      rcases hb1 : lowerEnd lay cenv lv sonst st.l ⟨r4, st.l + 3⟩ with _ | ⟨be, s1⟩
      · simp [hb1] at h
      have S1 := lowerEnd_shape lay cenv lv sonst st.l ⟨r4, st.l + 3⟩ s1 be hb1
      simp only [hb1] at h
      rcases hb2 : lowerB lay (a :: cenv) lv rest (st.l + 2) k s1 with _ | ⟨br, s2⟩
      · simp [hb2] at h
      have S2 := lowerB_shape lay (a :: cenv) lv rest (st.l + 2) k s1 s2 br hb2
      simp only [hb2] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons, List.mem_append] at hb
        rcases hb with rfl | rfl | hb | hb
        · rfl
        · rfl
        · exact S1.2.1 b hb
        · exact S2.2.1 b hb
      · have a1 := S1.2.2
        have a2 := S2.2.2
        simp only at m1 m2 m3 m4 a1 a2 ⊢
        omega
  | _, _, _, _, .float .., lb, k, st, st', blks, h => by
      simp [lowerB] at h
  | _, _, _, _, .floatLit .., lb, k, st, st', blks, h => by
      simp [lowerB] at h
  | _, _, _, _, .floatOf .., lb, k, st, st', blks, h => by
      simp [lowerB] at h
  | _, _, _, _, .floatNarrow .., lb, k, st, st', blks, h => by
      simp [lowerB] at h

theorem lowerEnd_shape (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (b : Gabbro.Grammatik.Endblock D V l Γ Λ)
      (lb : Lbl) (st st' : St) (blks : List Block),
      lowerEnd lay cenv lv b lb st = some (blks, st') → Shape lb st st' blks
  | _, _, _, .ret e _, lb, st, st', blks, h => by
      simp only [lowerEnd] at h
      exact lowerErg_shape lay cenv e lb st st' blks h
  | _, _, _, .cons s rest, lb, st, st', blks, h => by
      simp only [lowerEnd] at h
      rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
      · simp [hs] at h
      have S1 := lowerS_shape lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs
      simp only [hs] at h
      rcases hr : lowerEnd lay cenv lv rest st.l s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      have S2 := lowerEnd_shape lay cenv lv rest st.l s1 s2 b2 hr
      simp only [hr] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      obtain ⟨⟨hd, tl, hdt, hl⟩, hp, hm⟩ := S1
      refine ⟨⟨hd, tl ++ b2, by rw [hdt]; rfl, hl⟩, ?_, ?_⟩
      · intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact hp b hb
        · exact S2.2.1 b hb
      · have a2 := S2.2.2
        simp only at hm a2 ⊢
        omega
  | _, _, _, Gabbro.Grammatik.Endblock.bind (τ := τ) e rest, lb, st, st', blks, h => by
      simp only [lowerEnd] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
      have m1 := lowerE_mono lay cenv e st.r _ he
      simp only [he] at h
      rcases hb : bindCode τ oe r1 with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      have m2 := bindCode_mono hb
      simp only [hb] at h
      rcases hr : lowerEnd lay (a :: cenv) lv rest st.l ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp [hr] at h
      have S2 := lowerEnd_shape lay (a :: cenv) lv rest st.l ⟨r2, st.l + 1⟩ s2 b2 hr
      simp only [hr] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · rfl
        · exact S2.2.1 b hb
      · have a2 := S2.2.2
        simp only at m1 m2 a2 ⊢
        omega
  | _, _, _, .retWhy .., lb, st, st', blks, h => by
      simp [lowerEnd] at h
  | _, _, _, .leave .., lb, st, st', blks, h => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨_, _, rfl, rfl⟩, by simp, Nat.le_refl _⟩
  | _, _, _, .next .., lb, st, st', blks, h => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨_, _, rfl, rfl⟩, by simp, Nat.le_refl _⟩
  | _, _, _, .bindAxiom .., lb, st, st', blks, h => by
      simp [lowerEnd] at h
  | _, _, _, .bindAxiomElse .., lb, st, st', blks, h => by
      simp [lowerEnd] at h

/-- The arms of a `match` on a tagged value: no phis, the register counter does not fall. -/
theorem lowerAr_shape (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (top : Int) (W L : Nat)
    (ov : Opd) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
      (arms : Gabbro.Grammatik.Arms D V l Γ Λ Λ' cs) (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerAr lay cenv lv top W L ov arms lb k st = some (blks, st') →
      (∀ b ∈ blks, b.phis = []) ∧ st.r ≤ st'.r
  | _, _, _, _, _, .nil, lb, k, st, st', blks, h => by
      simp only [lowerAr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, Nat.le_refl _⟩
  | _, _, _, _, _, .cons (c := none) b rest, lb, k, st, st', blks, h => by
      simp only [lowerAr] at h
      rcases hb : lowerB lay cenv lv b lb k st with _ | ⟨b1, s1⟩
      · simp [hb] at h
      have S1 := lowerB_shape lay cenv lv b lb k st s1 b1 hb
      simp only [hb] at h
      rcases hr : lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      have S2 := lowerAr_shape lay cenv lv top W L ov rest (lb + 1) k s1 s2 b2 hr
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact S1.2.1 x hx
        · exact S2.1 x hx
      · have a1 := S1.2.2
        have a2 := S2.2
        omega
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, lb, k, st, st', blks, h => by
      simp only [lowerAr] at h
      rcases hp : payCode top W L lo hi ov st.r with _ | ⟨cp, op, r1⟩
      · simp [hp] at h
      have m1 := payCode_mono hp
      simp only [hp] at h
      rcases hb : bindCode (.int lo hi) op r1 with _ | ⟨cb, a, r2⟩
      · simp [hb] at h
      have m2 := bindCode_mono hb
      simp only [hb] at h
      rcases hb1 : lowerB lay (a :: cenv) lv b st.l k ⟨r2, st.l + 1⟩ with _ | ⟨bb, s1⟩
      · simp [hb1] at h
      have S1 := lowerB_shape lay (a :: cenv) lv b st.l k ⟨r2, st.l + 1⟩ s1 bb hb1
      simp only [hb1] at h
      rcases hr : lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      have S2 := lowerAr_shape lay cenv lv top W L ov rest (lb + 1) k s1 s2 b2 hr
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · rfl
          · exact S1.2.1 x hx
        · exact S2.1 x hx
      · have a1 := S1.2.2
        have a2 := S2.2
        simp only at m1 m2 a1 a2 ⊢
        omega

/-- The arms of a `match` on a reason: no phis, the register counter does not fall. -/
theorem lowerGA_shape (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (arms : Gabbro.Grammatik.GrundArms D V l Γ Λ Λ' n) (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerGA lay cenv lv arms lb k st = some (blks, st') →
      (∀ b ∈ blks, b.phis = []) ∧ st.r ≤ st'.r
  | _, _, _, _, _, .nil, lb, k, st, st', blks, h => by
      simp only [lowerGA, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, Nat.le_refl _⟩
  | _, _, _, _, _, .cons b rest, lb, k, st, st', blks, h => by
      simp only [lowerGA] at h
      rcases hb : lowerB lay cenv lv b lb k st with _ | ⟨b1, s1⟩
      · simp [hb] at h
      have S1 := lowerB_shape lay cenv lv b lb k st s1 b1 hb
      simp only [hb] at h
      rcases hr : lowerGA lay cenv lv rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp [hr] at h
      have S2 := lowerGA_shape lay cenv lv rest (lb + 1) k s1 s2 b2 hr
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact S1.2.1 x hx
        · exact S2.1 x hx
      · have a1 := S1.2.2
        have a2 := S2.2
        omega

end

end Gabbro.Code.Lower
