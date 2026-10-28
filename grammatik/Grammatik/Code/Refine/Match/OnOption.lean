import Grammatik.Code.Refine.Match.Scope

/-
  File:      Grammatik/Code/Refine/Match/OnOption.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT OF `match` ON AN `opt n` (`Stmt.onOption`).

  The lowering (`lowerS`, `.onOption`): the scrutinee's word `z` (`-1` for absent), then
    * `lb`        -- `if z <s 0 then A else B`;
    * `st.l`  `A` -- the lowered absent arm;
    * `st.l+1` `B` -- the word moved to the unsigned width of `0 .. n - 1` and a fresh cell holding it,
                     jump to the present arm;
    * `st.l+2`    -- the lowered present arm, in the environment extended by that cell.
  `onOption_ok` takes the refinement of both arms (`BOk`) and proves the statement's.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl wahr?)

variable {D : Deklaration} {V : Vertrag D}

theorem onOption_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl)
    (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Int}
    (o : Gabbro.Grammatik.Expr D Γ Λ (.opt n))
    (p : Gabbro.Grammatik.Block D V l (.index n :: Γ) Λ Λ') (a : Gabbro.Grammatik.Block D V l Γ Λ Λ')
    (IHp : ∀ c, BOk lay (c :: cenv) lv O passes R p) (IHa : BOk lay cenv lv O passes R a)
    (lb k : Lbl) (st st' : St) (blks : List Block)
    (h : lowerS lay cenv lv (Gabbro.Grammatik.Stmt.onOption o p a) lb k st = some (blks, st'))
    (M : Modl) (S : Sees) (fn : Nat) (hM : InM M fn blks) (hk : KOk M fn k) (hlv : LvOk M fn lv)
    (hFn : FnOk lay M) (hCall : CallRef lay M S R)
    (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m) (hc : ∀ x ∈ cenv, x < st.r) :
    OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst
      (execStmt O passes R (Gabbro.Grammatik.Stmt.onOption o p a) σ ρ) := by
  simp only [lowerS] at h
  rcases ho : lowerE lay cenv o st.r with _ | ⟨co, oo, r1⟩
  · simp only [ho, reduceCtorEq] at h
  simp only [ho] at h
  have hfit : Ar.Fits (-1) (n - 1) 128 ∧ Ar.Fits 0 (n - 1) 128 := by
    apply Classical.byContradiction
    intro hn
    rw [if_neg hn] at h
    simp only [reduceCtorEq] at h
  rw [if_pos hfit] at h
  rcases hv : cvtG (.int (-1) (n - 1)) (.int 0 (n - 1)) oo r1 with _ | ⟨cv, ov, r2⟩
  · simp only [Int.reduceNeg, hv, reduceCtorEq] at h
  simp only [hv] at h
  rcases hb : bindCode (.int 0 (n - 1)) ov r2 with _ | ⟨cb, cc, r3⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hb1 : lowerB lay cenv lv a st.l k ⟨r3, st.l + 3⟩ with _ | ⟨ba, s1⟩
  · simp only [hb1, reduceCtorEq] at h
  simp only [hb1] at h
  rcases hb2 : lowerB lay (cc :: cenv) lv p (st.l + 2) k s1 with _ | ⟨bp, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  simp only [hb2] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have m1 := lowerE_mono lay cenv o st.r _ ho
  have m2 := cvtG_mono hv
  have m3 := bindCode_mono hb
  have S1 := lowerB_shape lay cenv lv a st.l k ⟨r3, st.l + 3⟩ s1 ba hb1
  have S2 := lowerB_shape lay (cc :: cenv) lv p (st.l + 2) k s1 s2 bp hb2
  have hb0 := hM _ (List.mem_cons_self ..)
  have hbb := hM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hMa : InM M fn ba := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hb')))
  have hMp : InM M fn bp := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hb')))
  have hKa := kok_of_shape S1 hMa
  have hKp := kok_of_shape S2 hMp
  have hs12 : s1.r ≤ s2.r := S2.2.2
  have hr3 : r1 ≤ r3 := by
    simp only at m2 m3
    omega
  have hRl : Rep lay (σ.lese Λ o.orte) m := hR
  obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ o.orte := ⟨_, rfl⟩
  simp only [execStmt]
  try rw [← hσl]
  have hRl' : Rep lay σl m := by rw [hσl]; exact hR
  obtain ⟨Fo, _⟩ := lowerE_ok lay hL o cenv st.r (co, oo, r1) ho σl σl ρ m rs hRl' hE hc
  obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fo
  have hs1' : seqI co m rs = some (m, rs1) := hs1
  have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
  have hw8 := Ar.wid_pos (-1) (n - 1)
  have hf0 : FitS true (Ar.wid (-1) (n - 1)) 0 := by
    have hp : (0 : Int) < 2 ^ (Ar.wid (-1) (n - 1) - 1) := by exact_mod_cast Nat.two_pow_pos _
    simp only [FitS, if_true]; omega
  have hb0' : Opd.ev rs1 (Opd.int (Ar.wid (-1) (n - 1)) 0) = some (Val.ofInt (Ar.wid (-1) (n - 1)) 0) := rfl
  rcases hve : eval σl o σl ρ with _ | kk
  · -- absent
    rw [hve] at hev1
    have hev : oo.ev rs1 = some (Val.ofInt (Ar.wid (-1) (n - 1)) (-1)) := hev1
    have hfz := optFit hfit.1 (-1) (Or.inl rfl)
    have hic : Val.icmp .slt (Ar.wid (-1) (n - 1)) (Val.ofInt (Ar.wid (-1) (n - 1)) (-1))
        (Val.ofInt (Ar.wid (-1) (n - 1)) 0) = some (.int 1 (1 : BitVec 1)) := by
      have := val_icmp_lt true (Ar.wid (-1) (n - 1)) (-1) 0 (by omega) hfz hf0
      simp only [if_true] at this
      rw [this, decide_eq_true (show (-1 : Int) < 0 by omega)]
      rfl
    obtain ⟨bka, hbka, hkpa⟩ := hKa
    have hbr0 := reach_block_brc (S := S) (ks := ks) (dst := dst) hb0 rfl hs1' hev hb0' hic
      (by simpa using hbka) hkpa
    have hbr : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l, 0, rs1, dst⟩ ks) := by
      simpa using hbr0
    exact outok_mono hs12 _ (outok_lift hbr (fr_regs hag1) (Nat.le_trans hr1 hr3) hc _
      (IHa st.l k ⟨r3, st.l + 3⟩ s1 ba hb1 M S fn hMa hk hlv hFn hCall σl ρ m rs1 ks dst hRl' hE1 hW
        (fun x hx => Nat.lt_of_lt_of_le (hc1 x hx) hr3)))
  · -- present, with index `kk`
    rw [hve] at hev1
    have hev : oo.ev rs1 = some (Val.ofInt (Ar.wid (-1) (n - 1)) kk.n) := hev1
    have hk0 := kk.lo_le
    have hk1 := kk.le_hi
    have hfz := optFit hfit.1 kk.n (Or.inr ⟨hk0, hk1⟩)
    have hic : Val.icmp .slt (Ar.wid (-1) (n - 1)) (Val.ofInt (Ar.wid (-1) (n - 1)) kk.n)
        (Val.ofInt (Ar.wid (-1) (n - 1)) 0) = some (.int 1 (0 : BitVec 1)) := by
      have := val_icmp_lt true (Ar.wid (-1) (n - 1)) kk.n 0 (by omega) hfz hf0
      simp only [if_true] at this
      rw [this, decide_eq_false (show ¬ (kk.n < 0) by omega)]
      rfl
    obtain ⟨bkb, hbkb, hkpb⟩ : ∃ bk, M.blk fn (st.l + 1) = some bk ∧ bk.phis = [] := ⟨_, hbb, rfl⟩
    have h01 : ¬ ((0 : BitVec 1) = 1) := by decide
    have hbr0 := reach_block_brc (S := S) (ks := ks) (dst := dst) hb0 rfl hs1' hev hb0' hic
      (by simpa [h01] using hbkb) hkpb
    have hbr : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l + 1, 0, rs1, dst⟩ ks) := by
      simpa [h01] using hbr0
    obtain ⟨cV, hcV, FV⟩ := cvtG_frag (lb := 0) (hb := n - 1) (m := m) (rs := rs1) (z := kk.n)
      hfit.1 (by omega) hk1 hev hlt1
    rw [hv] at hcV
    have hcV' := Option.some.inj hcV
    subst hcV'
    have hKr := hKp
    exact outok_lift hbr (fr_regs hag1) hr1 hc _
      (scope_ok (τ := .int 0 (n - 1)) (l := l) (V := V) (lv := lv) (M := M) (S := S) (fn := fn) (k := k) (ks := ks) (dst := dst) ρ kk
        (lb1 := st.l + 1) (bd := st.l + 2) (cv := cv) (cb := cb) (ov := ov) (r0 := r1) (r1 := r2)
        (r2 := r3) (a := cc) (ri := s1.r) (r' := s2.r) m rs1 hRl' hE1 hW hc1 hbb hKr FV hb
        S1.2.2 _
        (fun m1 rs4 hRn hEn hWn hbound => IHp cc (st.l + 2) k s1 s2 bp hb2 M S fn hMp hk hlv hFn hCall σl
          (Env.cons kk ρ) m1 rs4 ks dst hRn hEn hWn hbound))

end Gabbro.Code.Lower
