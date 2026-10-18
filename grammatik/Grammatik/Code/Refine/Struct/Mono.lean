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

/-- An integer operation at a chosen width: registers only go up. -/
theorem opRest_mono {op : BinOp} {j : Int × Int} {τ σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : opRest op j τ σa σb oa ob r = some c) : r ≤ c.2.2 := by
  unfold opRest at h
  split at h
  · rename_i la ha lb hb
    rcases hc1 : cvtG (.int la ha) (.int j.1 j.2) oa r with _ | ⟨c1, oa', r1⟩
    · simp [hc1] at h
    have m1 := cvtG_mono hc1
    simp only [hc1] at h
    rcases hc2 : cvtG (.int lb hb) (.int j.1 j.2) ob r1 with _ | ⟨c2, ob', r2⟩
    · simp [hc2] at h
    have m2 := cvtG_mono hc2
    simp only [hc2] at h
    split at h
    · rcases hc3 : cvtG (.int j.1 j.2) τ (.reg r2) (r2 + 1) with _ | ⟨c3, o3, r3⟩
      · simp [hc3] at h
      have m3 := cvtG_mono hc3
      simp only [hc3] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
    · simp at h
  · simp at h

theorem numCode_mono {lo hi : Int} {W L i : Nat} {oe : Opd} {r : Nat} :
    r ≤ (numCode lo hi W L i oe r).2.2 := by
  unfold numCode
  rcases hc : cvt (Ar.wid lo hi) W (decide (lo < 0)) oe r with ⟨c1, o1, r2⟩
  have := cvt_mono (Ar.wid lo hi) W (decide (lo < 0)) oe r
  rw [hc] at this
  simp only at this ⊢
  omega

mutual

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
  | _, _, _, .sdiv (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb'] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .sdiv (jsdiv l1 h1 l2 h2) (ety (Expr.sdiv hb a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .srem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) hb a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb'] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .srem (jsrem l1 h1 l2 h2) (ety (Expr.srem hb a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .getBytes .., r, c, h => by
      simp [lowerE] at h
  | _, _, _, .band (h1 := h1) (h2 := h2) h0 h0' a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb'] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .and (jbit h1 h2 h1) (ety (Expr.band h0 h0' a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .bor (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb'] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .or (jbit h1 h2 (2 ^ w - 1)) (ety (Expr.bor w h0 h0' hw1 hw2 a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .bxor (h1 := h1) (h2 := h2) w h0 h0' hw1 hw2 a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb'] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .xor (jbit h1 h2 (2 ^ w - 1)) (ety (Expr.bxor w h0 h0' hw1 hw2 a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .shl (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb'] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .shl (jshl h1 h2) (ety (Expr.shl w hw1 hw2 h0 h0' a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
  | _, _, _, .shr (h1 := h1) (h2 := h2) w hw1 hw2 h0 h0' a b, r, c, h => by
      simp only [lowerE] at h
      rcases ha : lowerE lay cenv a r with _ | ⟨ca, oa, r1⟩
      · simp [ha] at h
      have m1 := lowerE_mono lay cenv a r _ ha
      simp only [ha] at h
      rcases hb' : lowerE lay cenv b r1 with _ | ⟨cb, ob, r2⟩
      · simp [hb'] at h
      have m2 := lowerE_mono lay cenv b r1 _ hb'
      simp only [hb'] at h
      rcases hr : opRest .lshr (jshr h1 h2) (ety (Expr.shr w hw1 hw2 h0 h0' a b)) (ety a) (ety b) oa ob r2 with _ | ⟨ct, ot, r3⟩
      · simp [hr] at h
      have m3 := opRest_mono hr
      simp only [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
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
  | _, _, _, .case cs i nutz, r, c, h => by
      simp only [lowerE] at h
      split at h
      · exact lowerNutz_mono lay cenv _ _ _ nutz r c h
      · simp at h
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

theorem lowerNutz_mono (lay : Layout D) (cenv : List Reg) (W L i : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)}
      (nutz : Gabbro.Grammatik.NutzlastExpr D Γ Λ c) (r : Nat) (c0 : LR),
      lowerNutz lay cenv W L i nutz r = some c0 → r ≤ c0.2.2
  | _, _, _, .empty, r, c0, h => by
      simp only [lowerNutz, Option.some.injEq] at h
      subst h
      exact Nat.le_refl _
  | _, _, _, .num (lo := lo) (hi := hi) e, r, c0, h => by
      simp only [lowerNutz] at h
      rcases he : lowerE lay cenv e r with _ | ⟨ce, oe, r1⟩
      · simp [he] at h
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

end Gabbro.Code.Lower
