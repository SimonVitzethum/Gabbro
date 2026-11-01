module

public import Grammatik.Code.Lower.Stmt

@[expose] public section



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
  split <;> try (simp only [Std.le_refl]; done)
  split <;> simp only [Nat.le_add_right]

theorem cvtG_mono {σ τ : GTy} {o : Opd} {r : Nat} {c : LR} (h : cvtG σ τ o r = some c) : r ≤ c.2.2 := by
  unfold cvtG at h
  split at h
  · obtain rfl := Option.some.inj h; exact cvt_mono _ _ _ _ _
  · simp only [reduceCtorEq] at h

theorem loadG_mono {τ : GTy} {p : Opd} {r : Nat} {c : LR} (h : loadG τ p r = some c) : r ≤ c.2.2 := by
  unfold loadG at h
  split at h <;> first
    | (obtain rfl := Option.some.inj h; simp only [Nat.le_add_right]; done)
    | (split at h <;> first
        | (obtain rfl := Option.some.inj h; simp only [Nat.le_add_right]; done)
        | (simp only [reduceCtorEq] at h; done))
    | (simp only [reduceCtorEq] at h; done)

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
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

theorem binRest_mono {op : BinOp} {τ σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : binRest op τ σa σb oa ob r = some c) : r ≤ c.2.2 := by
  unfold binRest at h
  rcases hc1 : cvtG σa τ oa r with _ | ⟨c1, oa', r1⟩
  · simp only [hc1, reduceCtorEq] at h
  · have m1 := cvtG_mono hc1
    simp only [hc1] at h
    rcases hc2 : cvtG σb τ ob r1 with _ | ⟨c2, ob', r2⟩
    · simp only [hc2, reduceCtorEq] at h
    · have m2 := cvtG_mono hc2
      simp only [hc2] at h
      split at h
      · obtain rfl := Option.some.inj h
        simp only at m1 m2 ⊢
        omega
      · simp only [reduceCtorEq] at h

theorem divRest_mono {op : BinOp} {τ σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : divRest op τ σa σb oa ob r = some c) : r ≤ c.2.2 := by
  unfold divRest at h
  split at h
  · rename_i la ha lb hb
    simp only at h
    rcases hc1 : cvtG (.int la ha) (joinT (.int la ha) (.int lb hb)) oa r with _ | ⟨c1, oa', r1⟩
    · simp only [hc1, reduceCtorEq] at h
    have m1 := cvtG_mono hc1
    simp only [hc1] at h
    rcases hc2 : cvtG (.int lb hb) (joinT (.int la ha) (.int lb hb)) ob r1 with _ | ⟨c2, ob', r2⟩
    · simp only [hc2, reduceCtorEq] at h
    have m2 := cvtG_mono hc2
    simp only [hc2] at h
    split at h
    · rcases hc3 : cvtG (joinT (.int la ha) (.int lb hb)) τ (.reg r2) (r2 + 1) with _ | ⟨c3, o3, r3⟩
      · simp only [hc3, reduceCtorEq] at h
      have m3 := cvtG_mono hc3
      simp only [hc3] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

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
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

theorem cvtM_mono {τ : GTy} {o : Opd} {r : Nat} {c : LR} (h : cvtM τ o r = some c) : r ≤ c.2.2 := by
  unfold cvtM at h
  split at h <;> first
    | (obtain rfl := Option.some.inj h; simp only [Nat.le_add_right, Std.le_refl]; done)
    | (split at h <;> first
        | (obtain rfl := Option.some.inj h; simp only [Std.le_refl]; done)
        | (simp only [reduceCtorEq] at h; done))
    | (simp only [reduceCtorEq] at h; done)

theorem storeTo_mono {τ : GTy} {oe : Opd} {r1 : Nat} {p : Opd} {cs : List Instr} {r2 : Nat}
    (h : storeTo τ oe r1 p = some (cs, r2)) : r1 ≤ r2 := by
  unfold storeTo at h
  rcases hc : cvtM τ oe r1 with _ | ⟨cm, om, r3⟩
  · simp only [hc, reduceCtorEq] at h
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
  · simp only [hc, reduceCtorEq] at h
  · have := cvtM_mono hc
    simp only [hc] at h
    split at h
    · have := (Option.some.inj h)
      simp only [Prod.mk.injEq] at this
      obtain ⟨_, rfl, rfl⟩ := this
      exact ⟨by simpa using cvtM_mono hc, rfl⟩
    · simp only [reduceCtorEq] at h

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
    · simp only [hv, reduceCtorEq] at h
    have m3 := cvtG_mono hv
    simp only [hv] at h
    obtain rfl := Option.some.inj h
    simp only at m1 m3 ⊢
    omega
  · simp only [reduceCtorEq] at h

/-- An integer operation at a chosen width: registers only go up. -/
theorem opRest_mono {op : BinOp} {j : Int × Int} {τ σa σb : GTy} {oa ob : Opd} {r : Nat} {c : LR}
    (h : opRest op j τ σa σb oa ob r = some c) : r ≤ c.2.2 := by
  unfold opRest at h
  split at h
  · rename_i la ha lb hb
    rcases hc1 : cvtG (.int la ha) (.int j.1 j.2) oa r with _ | ⟨c1, oa', r1⟩
    · simp only [hc1, reduceCtorEq] at h
    have m1 := cvtG_mono hc1
    simp only [hc1] at h
    rcases hc2 : cvtG (.int lb hb) (.int j.1 j.2) ob r1 with _ | ⟨c2, ob', r2⟩
    · simp only [hc2, reduceCtorEq] at h
    have m2 := cvtG_mono hc2
    simp only [hc2] at h
    split at h
    · rcases hc3 : cvtG (.int j.1 j.2) τ (.reg r2) (r2 + 1) with _ | ⟨c3, o3, r3⟩
      · simp only [hc3, reduceCtorEq] at h
      have m3 := cvtG_mono hc3
      simp only [hc3] at h
      obtain rfl := Option.some.inj h
      simp only at m1 m2 m3 ⊢
      omega
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

theorem numCode_mono {lo hi : Int} {W L i : Nat} {oe : Opd} {r : Nat} :
    r ≤ (numCode lo hi W L i oe r).2.2 := by
  unfold numCode
  rcases hc : cvt (Ar.wid lo hi) W (decide (lo < 0)) oe r with ⟨c1, o1, r2⟩
  have := cvt_mono (Ar.wid lo hi) W (decide (lo < 0)) oe r
  rw [hc] at this
  simp only at this ⊢
  omega

end Gabbro.Code.Lower
