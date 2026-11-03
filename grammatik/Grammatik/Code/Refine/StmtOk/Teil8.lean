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


/-
  File:      Grammatik/Code/Refine/StmtOk/Teil8.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT OF THE C11 END-BLOCK FORMS.

  `lowerEnd_ok_retScoped`/`lowerEnd_ok_retWhyScoped` (like `ret`/`retWhy`: the value is
  evaluated before the release; the scope list is released in recorded order and the memory
  presentation survives the release fold by `Rep.gibt_foldl`) and `lowerEnd_ok_narrowRequired` (like
  `Block.narrowRequired`, with an end-block rest: out of range is `Logik.kapazitaet`, so the
  failure case refines vacuously).
-/

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl alleIndizes evalArgs ergWert)
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem lowerEnd_ok_retScoped (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (Rr)
    (lb : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerEnd lay cenv lv (.retScoped (Λ := Λ) e Rr : Gabbro.Grammatik.Endblock D V l Γ Λ) lb st = some (blks, st'))
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
    : EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R (.retScoped (Λ := Λ) e Rr : Gabbro.Grammatik.Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [lowerEnd] at h
  simp only [execEnd, EndOk]
  obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerRet_ok lay hL cenv V.gruende e lb st st' blks h M S fn hM
    (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs ks dst hR hE hc
  have hRl : Rep lay (σ.lese Λ e.orte) m := hR
  exact ⟨m, f', hr, hf1, hf2, hret, hRl.gibt_foldl Rr.scopes, hW, hFr⟩

set_option linter.unusedSectionVars false in
theorem lowerEnd_ok_retWhyScoped (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (Rr)
    (lb : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerEnd lay cenv lv (.retWhyScoped (Λ := Λ) r Rr : Gabbro.Grammatik.Endblock D V l Γ Λ) lb st = some (blks, st'))
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
    : EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R (.retWhyScoped (Λ := Λ) r Rr : Gabbro.Grammatik.Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [lowerEnd] at h
  simp only [execEnd, EndOk]
  obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerWhy_ok lay cenv V.gruende V.erg r.val lb st st' blks h M S fn hM
    m rs ks dst
  exact ⟨m, f', hr, hf1, hf2, hret, hR.gibt_foldl Rr.scopes, hW, hFr⟩

set_option linter.unusedSectionVars false in
theorem lowerEnd_ok_narrowRequired (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lo)
    (hi)
    (e)
    (lo')
    (hi')
    (rest)
    (lb : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerEnd lay cenv lv (Gabbro.Grammatik.Endblock.narrowRequired (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' rest : Gabbro.Grammatik.Endblock D V l Γ Λ) lb st = some (blks, st'))
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
    : EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R (Gabbro.Grammatik.Endblock.narrowRequired (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' rest : Gabbro.Grammatik.Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [lowerEnd] at h
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
  rcases hb2 : lowerEnd lay (a :: cenv) lv rest (st.l + 2) ⟨r4, st.l + 3⟩ with _ | ⟨br, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  simp only [hb2] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have S2 := lowerEnd_shape lay (a :: cenv) lv rest (st.l + 2) ⟨r4, st.l + 3⟩ s2 br hb2
  have hb0 := hM _ (List.mem_cons_self ..)
  have hbb := hM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hMr : InM M fn br := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb')))
  have hKr := kok_of_shape S2 hMr
  have hRl : Rep lay (σ.lese Λ e.orte) m := hR
  simp only [execEnd]
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
    have hbound : ∀ x ∈ a :: cenv, x < a + 1 := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc3 x hx') hra)
    have IHr := ih_lowerEnd_ok_rest lay hL (a :: cenv) lv O passes R (st.l + 2) ⟨a + 1, st.l + 3⟩ s2 br hb2
      M S fn hMr hlv hFn hCall (σ.lese Λ e.orte) (Env.cons ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hn.1, hn.2⟩ ρ) m1 rs4 ks dst hRn hEnew hWn hbound
    have hF123 : Fr lay cenv st.r m rs m1 rs4 :=
      fr_trans (fr_regs hag1) (fr_trans (fr_regs hag2) (fr_trans (fr_regs hag3) hFb hr3 hc2) hr2 hc1) hr1 hc
    exact endok_bind (Reach.trans hbr hreach2) hF123 hcell hc
      (Nat.le_trans (Nat.le_trans hr1 (Nat.le_trans hr2 (Nat.le_trans hr3 hra)))
        (Nat.le_succ a)) _ IHr
  · rw [dif_neg hn]
    exact trivial

end Gabbro.Code.Lower
