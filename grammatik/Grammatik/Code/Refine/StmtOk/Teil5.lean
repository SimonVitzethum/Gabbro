module

public import Grammatik.Code.Refine.Stmt
public import Grammatik.Code.Refine.Loops.Loop
public import Grammatik.Code.Refine.Loops.Traverse
public import Grammatik.Code.Refine.Loops.Retry
public import Grammatik.Code.Refine.Calls.CallRun
public import Grammatik.Code.Refine.Match.OnOption
public import Grammatik.Code.Refine.Match.Why
public import Grammatik.Code.Refine.Match.Tag
public import Grammatik.Code.Refine.Match.Else
public import Grammatik.Code.Refine.StmtOk.Teil4

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl alleIndizes evalArgs ergWert)
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem lowerB_ok_GabbroGrammatikBlocknarrow (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (lo)
    (hi)
    (Λ)
    (e)
    (lo')
    (hi')
    (sonst)
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (Gabbro.Grammatik.Block.narrow (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' sonst rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
    (M : Modl)
    (S : Sees)
    (fn : Nat)
    (hM : InM M fn blks)
    (hk : KOk M fn k)
    (hlv : LvOk M fn lv)
    (hFn : FnOk lay M)
    (hCall : CallRef lay M S R)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (ks : List Frame)
    (dst : Option Reg)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hW : WfL lay m)
    (hc : (∀ x ∈ cenv, x < st.r))
    (ih_lowerB_ok_rest : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv rest lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R rest σ ρ))
    (ih_lowerEnd_ok_sonst : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerEnd lay cenv lv sonst lb st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R sonst σ ρ))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R (Gabbro.Grammatik.Block.narrow (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' sonst rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [lowerB] at h
  rcases hcd : lowerE lay cenv (Gabbro.Grammatik.Expr.and (Gabbro.Grammatik.Expr.le
      (Gabbro.Grammatik.Expr.lit lo') e) (Gabbro.Grammatik.Expr.le e (Gabbro.Grammatik.Expr.lit hi')))
      st.r with _ | ⟨cc, oc, r1⟩
  · simp only [hcd, reduceCtorEq] at h
  simp only [hcd] at h
  rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hv : cvtG (.int lo hi) (.int lo' hi') oe r2 with _ | ⟨cv, ov, r3⟩
  · simp only [hv, reduceCtorEq] at h
  simp only [hv] at h
  rcases hb : bindCode (.int lo' hi') ov r3 with _ | ⟨cb, a, r4⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hb1 : lowerEnd lay cenv lv sonst st.l ⟨r4, st.l + 3⟩ with _ | ⟨be, s1⟩
  · simp only [hb1, reduceCtorEq] at h
  simp only [hb1] at h
  rcases hb2 : lowerB lay (a :: cenv) lv rest (st.l + 2) k s1 with _ | ⟨br, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  simp only [hb2] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have m1 := lowerE_mono lay cenv _ st.r _ hcd
  have m2 := lowerE_mono lay cenv e r1 _ he
  have m3 := cvtG_mono hv
  have m4 := bindCode_mono hb
  have S1 := lowerEnd_shape lay cenv lv sonst st.l ⟨r4, st.l + 3⟩ s1 be hb1
  have S2 := lowerB_shape lay (a :: cenv) lv rest (st.l + 2) k s1 s2 br hb2
  have hb0 := hM _ (List.mem_cons_self ..)
  have hbb := hM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hMe : InM M fn be := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hb')))
  have hMr : InM M fn br := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hb')))
  have hKe := kok_of_shape S1 hMe
  have hKr := kok_of_shape S2 hMr
  have hle14 : r1 ≤ r4 := by
    have a2 := m2
    have a3 := m3
    have a4 := m4
    simp only at a2 a3 a4
    omega
  have hRl : Rep lay (σ.lese Λ e.orte) m := hR
  simp only [execBlock]
  -- the test
  obtain ⟨Fc, _⟩ := lowerE_ok lay hL _ cenv st.r (cc, oc, r1) hcd (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs hRl hE hc
  obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fc
  have hs1' : seqI cc m rs = some (m, rs1) := hs1
  have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
  have hcond : (eval (σ.lese Λ e.orte) (Gabbro.Grammatik.Expr.and (Gabbro.Grammatik.Expr.le
      (Gabbro.Grammatik.Expr.lit lo') e) (Gabbro.Grammatik.Expr.le e (Gabbro.Grammatik.Expr.lit hi'))) (σ.lese Λ e.orte) ρ : Bool)
      = (decide (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) && decide ((eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) := by
    first | rfl | simp [eval, Gabbro.Grammatik.wahr?]
  by_cases hn : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
  · rw [dif_pos hn]
    -- the test succeeds: run the bind block
    have hT : (eval (σ.lese Λ e.orte) (Gabbro.Grammatik.Expr.and (Gabbro.Grammatik.Expr.le
        (Gabbro.Grammatik.Expr.lit lo') e) (Gabbro.Grammatik.Expr.le e (Gabbro.Grammatik.Expr.lit hi'))) (σ.lese Λ e.orte) ρ : Bool)
        = true := by
      rw [hcond, decide_eq_true hn.1, decide_eq_true hn.2]; rfl
    have hev : oc.ev rs1 = some (.int 1 (1 : BitVec 1)) := by
      rw [hT] at hev1; exact hev1
    obtain ⟨bkb, hbkb, hkpb⟩ : ∃ bk, M.blk fn (st.l + 1) = some bk ∧ bk.phis = [] := ⟨_, hbb, rfl⟩
    have hbr0 := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (1 : BitVec 1)) hb0 rfl hs1' hev
      (by simpa using hbkb) hkpb
    have hbr : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l + 1, 0, rs1, dst⟩ ks) := by
      simpa using hbr0
    -- the value, moved to the new type
    obtain ⟨Fe, hfe⟩ := lowerE_ok lay hL e cenv r1 (ce, oe, r2) he (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs1 hRl hE1 hc1
    obtain ⟨rs2, hs2, hr2, hag2, hlt2, hev2⟩ := Fe
    have hs2' : seqI ce m rs1 = some (m, rs2) := hs2
    have hE2 := envRep_regs cenv ρ (fun x hx => hag2 x (hc1 x hx)) hE1
    have hc2 : ∀ x ∈ cenv, x < r2 := fun x hx => Nat.lt_of_lt_of_le (hc1 x hx) hr2
    obtain ⟨cV, hcV, FV⟩ := cvtG_frag (lb := lo') (hb := hi') (m := m) (rs := rs2) (z := (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n)
      (hfe lo hi rfl) (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).lo_le (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).le_hi hev2 hlt2
    rw [hv] at hcV
    have hcV' := Option.some.inj hcV
    subst hcV'
    obtain ⟨rs3, hs3, hr3, hag3, hlt3, hev3⟩ := FV
    have hs3' : seqI cv m rs2 = some (m, rs3) := hs3
    have hE3 := envRep_regs cenv ρ (fun x hx => hag3 x (hc2 x hx)) hE2
    have hc3 : ∀ x ∈ cenv, x < r3 := fun x hx => Nat.lt_of_lt_of_le (hc2 x hx) hr3
    obtain ⟨m1, rs4, hs4, hRn, hEnew, hWn, hra, hr4e, hag4, hFb, hcell⟩ :=
      bindCode_run lay (τ := .int lo' hi') (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hn.1, hn.2⟩ : Zahl lo' hi') ov r3 m rs3 hRl hE3 hW
        hev3 hlt3 hc3 hb
    subst hr4e
    have hseq1 : seqI (ce ++ cv) m rs1 = some (m, rs3) := by
      rw [seqI_append, hs2', Option.bind_some]; exact hs3'
    have hseq : seqI (ce ++ cv ++ cb) m rs1 = some (m1, rs4) := by
      rw [seqI_append, hseq1, Option.bind_some]; exact hs4
    obtain ⟨bkr, hbkr, hkpr⟩ := hKr
    have hreach2 := reach_block_jmp (S := S) (ks := ks) (dst := dst) hbb rfl hbkr hkpr hseq
    have hS1r : a + 1 ≤ s1.r := S1.2.2
    have hbound : ∀ x ∈ a :: cenv, x < s1.r := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hS1r
      · exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc3 x hx') hra)) hS1r
    have IHr := ih_lowerB_ok_rest lay hL (a :: cenv) lv O passes R (st.l + 2) k s1 s2 br hb2
      M S fn hMr hk hlv hFn hCall (σ.lese Λ e.orte) (Env.cons ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hn.1, hn.2⟩ ρ) m1 rs4 ks dst hRn hEnew hWn hbound
    have hF123 : Fr lay cenv st.r m rs m1 rs4 :=
      fr_trans (fr_regs hag1) (fr_trans (fr_regs hag2) (fr_trans (fr_regs hag3) hFb hr3 hc2) hr2 hc1) hr1 hc
    exact outok_bind (Reach.trans hbr hreach2) hF123 hcell hc
      (Nat.le_trans (Nat.le_trans hr1 (Nat.le_trans hr2 (Nat.le_trans hr3 hra)))
        (Nat.le_trans (Nat.le_succ a) hS1r)) _ IHr
  · rw [dif_neg hn]
    have hF : (eval (σ.lese Λ e.orte) (Gabbro.Grammatik.Expr.and (Gabbro.Grammatik.Expr.le
        (Gabbro.Grammatik.Expr.lit lo') e) (Gabbro.Grammatik.Expr.le e (Gabbro.Grammatik.Expr.lit hi'))) (σ.lese Λ e.orte) ρ : Bool)
        = false := by
      rw [hcond]
      by_cases h1 : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n
      · have h2 : ¬ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' := fun h2 => hn ⟨h1, h2⟩
        rw [decide_eq_false h2]; exact Bool.and_false _
      · rw [decide_eq_false h1]; rfl
    have hev : oc.ev rs1 = some (.int 1 (0 : BitVec 1)) := by
      rw [hF] at hev1; exact hev1
    obtain ⟨bke, hbke, hkpe⟩ := hKe
    have h01 : ¬ ((0 : BitVec 1) = 1) := by decide
    have hbr0 := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (0 : BitVec 1)) hb0 rfl hs1' hev
      (by simpa [h01] using hbke) hkpe
    have hbr : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l, 0, rs1, dst⟩ ks) := by
      simpa [h01] using hbr0
    exact outok_mono S2.2.2 _ (outok_lift hbr (fr_regs hag1) (Nat.le_trans hr1 hle14) hc _ (outok_of_endok _
      (ih_lowerEnd_ok_sonst lay hL cenv lv O passes R st.l ⟨r4, st.l + 3⟩ s1 be hb1 M S fn hMe hlv hFn hCall (σ.lese Λ e.orte) ρ m rs1
        ks dst hRl hE1 hW (fun x hx => Nat.lt_of_lt_of_le (hc1 x hx) hle14))))

set_option linter.unusedSectionVars false in
theorem lowerEnd_ok_ret (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (Λ)
    (e)
    (zz1)
    (lb : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerEnd lay cenv lv (.ret (Λ := Λ) e zz1 : Gabbro.Grammatik.Endblock D V l Γ Λ) lb st = some (blks, st'))
    (M : Modl)
    (S : Sees)
    (fn : Nat)
    (hM : InM M fn blks)
    (hlv : LvOk M fn lv)
    (hFn : FnOk lay M)
    (hCall : CallRef lay M S R)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (ks : List Frame)
    (dst : Option Reg)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hW : WfL lay m)
    (hc : (∀ x ∈ cenv, x < st.r))
    : EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R (.ret (Λ := Λ) e zz1 : Gabbro.Grammatik.Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [lowerEnd] at h
  simp only [execEnd, EndOk]
  obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerRet_ok lay hL cenv V.gruende e lb st st' blks h M S fn hM
    (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs ks dst hR hE hc
  exact ⟨m, f', hr, hf1, hf2, hret, hR, hW, hFr⟩

set_option linter.unusedSectionVars false in
theorem lowerEnd_ok_cons (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (lb : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerEnd lay cenv lv (.cons (Λ' := zi_Λ') s rest : Gabbro.Grammatik.Endblock D V l Γ Λ) lb st = some (blks, st'))
    (M : Modl)
    (S : Sees)
    (fn : Nat)
    (hM : InM M fn blks)
    (hlv : LvOk M fn lv)
    (hFn : FnOk lay M)
    (hCall : CallRef lay M S R)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (ks : List Frame)
    (dst : Option Reg)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hW : WfL lay m)
    (hc : (∀ x ∈ cenv, x < st.r))
    (ih_lowerS_ok_s : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerS lay cenv lv s lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R s σ ρ))
    (ih_lowerEnd_ok_rest : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerEnd lay cenv lv rest lb st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R rest σ ρ))
    : EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R (.cons (Λ' := zi_Λ') s rest : Gabbro.Grammatik.Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [lowerEnd] at h
  rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
  · simp only [hs, reduceCtorEq] at h
  simp only [hs] at h
  rcases hr : lowerEnd lay cenv lv rest st.l s1 with _ | ⟨b2, s2⟩
  · simp only [hr, reduceCtorEq] at h
  simp only [hr] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have SS := lowerEnd_shape lay cenv lv rest st.l s1 s2 b2 hr
  have hM1 : InM M fn b1 := fun b hb' => hM b (List.mem_append_left _ hb')
  have hM2 : InM M fn b2 := fun b hb' => hM b (List.mem_append_right _ hb')
  have hK2 := kok_of_shape SS hM2
  have IHs := ih_lowerS_ok_s lay hL cenv lv O passes R lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs M S fn hM1 hK2
    hlv hFn hCall σ ρ m rs ks dst hR hE hW hc
  have hle : s1.r ≤ s2.r := SS.2.2
  have S0 := lowerS_shape lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs
  simp only [execEnd]
  rcases hx : execStmt O passes R s σ ρ with ⟨σ1, ρ1⟩ | ⟨σ1, v1⟩ | ⟨σ1, r1'⟩ | ⟨h1, σ1, ρ1⟩ |
    ⟨h1, σ1, ρ1⟩ | e1 | e1
  · rw [hx] at IHs
    obtain ⟨m1, rs1, hr1, hP1, hF1⟩ := IHs
    obtain ⟨hRp, hEp, hWp, hcp⟩ := hP1
    simp only [hx]
    exact endok_lift hr1 hF1 S0.2.2 hc _ (ih_lowerEnd_ok_rest lay hL cenv lv O passes R st.l s1 s2 b2 hr M S fn hM2 hlv hFn hCall
      σ1 ρ1 m1 rs1 ks dst hRp hEp hWp hcp)
  · rw [hx] at IHs
    simp only [hx]
    exact IHs
  · rw [hx] at IHs
    simp only [hx]
    exact IHs
  · rw [hx] at IHs
    simp only [hx]
    exact runOk_mono hle IHs
  · rw [hx] at IHs
    simp only [hx]
    exact runOk_mono hle IHs
  · simp only [hx, EndOk]
  · simp only [hx, EndOk]

set_option linter.unusedSectionVars false in
theorem lowerEnd_ok_GabbroGrammatikEndblockbind (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (τ)
    (Λ)
    (e)
    (rest)
    (lb : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerEnd lay cenv lv (Gabbro.Grammatik.Endblock.bind (τ := τ) (Λ := Λ) e rest : Gabbro.Grammatik.Endblock D V l Γ Λ) lb st = some (blks, st'))
    (M : Modl)
    (S : Sees)
    (fn : Nat)
    (hM : InM M fn blks)
    (hlv : LvOk M fn lv)
    (hFn : FnOk lay M)
    (hCall : CallRef lay M S R)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (ks : List Frame)
    (dst : Option Reg)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hW : WfL lay m)
    (hc : (∀ x ∈ cenv, x < st.r))
    (ih_lowerEnd_ok_rest : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerEnd lay cenv lv rest lb st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R rest σ ρ))
    : EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R (Gabbro.Grammatik.Endblock.bind (τ := τ) (Λ := Λ) e rest : Gabbro.Grammatik.Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [lowerEnd] at h
  rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hb : bindCode τ oe r1 with _ | ⟨cb, a, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hr : lowerEnd lay (a :: cenv) lv rest st.l ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
  · simp only [hr, reduceCtorEq] at h
  simp only [hr] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have SS := lowerEnd_shape lay (a :: cenv) lv rest st.l ⟨r2, st.l + 1⟩ s2 b2 hr
  have hb0 := hM _ (List.mem_cons_self ..)
  have hM2 : InM M fn b2 := fun b hb' => hM b (List.mem_cons_of_mem _ hb')
  have hK2 := kok_of_shape SS hM2
  obtain ⟨bk2, hbk2, hkp2⟩ := hK2
  obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ e.orte := ⟨_, rfl⟩
  try rw [← hσl]
  have hRl : Rep lay σl m := by rw [hσl]; exact hR
  obtain ⟨Fe, _⟩ := lowerE_ok lay hL e cenv st.r (ce, oe, r1) he σl σl ρ m rs hRl hE hc
  obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fe
  have hs1' : seqI ce m rs = some (m, rs1) := hs1
  have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
  have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
  obtain ⟨m1, rs3, hs3, hRn, hEnew, hWn, hra, hr2e, hag3, hFb, hcell⟩ :=
    bindCode_run lay (eval σl e σl ρ) oe r1 m rs1 hRl hE1 hW hev1 hlt1 hc1 hb
  subst hr2e
  have hFbind : Fr lay cenv st.r m rs m1 rs3 := fr_trans (fr_regs hag1) hFb hr1 hc
  have hseq : seqI (ce ++ cb) m rs = some (m1, rs3) := by
    rw [seqI_append, hs1', Option.bind_some]; exact hs3
  have hreach := reach_block_jmp (S := S) (ks := ks) (dst := dst) hb0 rfl hbk2 hkp2 hseq
  have hbound : ∀ x ∈ a :: cenv, x < a + 1 := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc1 x hx') hra)
  have IHr := ih_lowerEnd_ok_rest lay hL (a :: cenv) lv O passes R st.l ⟨a + 1, st.l + 1⟩ s2 b2 hr M S fn
    hM2 hlv hFn hCall σl (Env.cons (eval σl e σl ρ) ρ) m1 rs3 ks dst hRn hEnew hWn hbound
  simp only [execEnd]
  try rw [← hσl]
  exact endok_bind hreach hFbind hcell hc (Nat.le_succ_of_le (Nat.le_trans hr1 hra)) _ IHr

set_option linter.unusedSectionVars false in
theorem lowerEnd_ok_retWhy (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (zz1)
    (lb : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerEnd lay cenv lv (.retWhy r zz1 : Gabbro.Grammatik.Endblock D V l Γ Λ) lb st = some (blks, st'))
    (M : Modl)
    (S : Sees)
    (fn : Nat)
    (hM : InM M fn blks)
    (hlv : LvOk M fn lv)
    (hFn : FnOk lay M)
    (hCall : CallRef lay M S R)
    (σ : World D)
    (ρ : Env D Γ)
    (m : Mem)
    (rs : Regs)
    (ks : List Frame)
    (dst : Option Reg)
    (hR : Rep lay σ m)
    (hE : EnvRep lay rs m cenv ρ)
    (hW : WfL lay m)
    (hc : (∀ x ∈ cenv, x < st.r))
    : EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R (.retWhy r zz1 : Gabbro.Grammatik.Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [lowerEnd] at h
  simp only [execEnd, EndOk]
  obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerWhy_ok lay cenv V.gruende V.erg r.val lb st st' blks h M S fn hM
    m rs ks dst
  exact ⟨m, f', hr, hf1, hf2, hret, hR, hW, hFr⟩

end Gabbro.Code.Lower
