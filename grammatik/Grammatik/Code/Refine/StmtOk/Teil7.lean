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
  File:      Grammatik/Code/Refine/StmtOk/Teil7.lean
  Subject:   TRACK L, PHASE L1 -- THE REFINEMENT OF THE C11 STATEMENT FORMS.

  `lowerS_ok_consumeTraverse` (like `traverse`: the placeholder `execStmt` runs the same fixed
  sweep; re-selection is OPEN), `lowerS_ok_retScoped`/`lowerS_ok_retWhyScoped` (like `ret`/`retWhy`:
  the value is evaluated before the release; the scope list is released in recorded order and the
  memory presentation survives the release fold by `Rep.gibt_foldl`) and `lowerB_ok_narrowRequired`
  (like `Block.narrow`, with the failure leg replaced by an unreachable trap: out of range is
  `Logik.kapazitaet`, so the failure case refines vacuously).
-/

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl alleIndizes evalArgs ergWert)
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem lowerS_ok_consumeTraverse (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (Λ)
    (t)
    (member)
    (edge)
    (inv)
    (bound)
    (mass)
    (body)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.consumeTraverse (Λ := Λ) t member edge inv bound mass body : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
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
    (ih_lowerB_ok_body : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv body lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R body σ ρ))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.consumeTraverse (Λ := Λ) t member edge inv bound mass body : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  by_cases hcn : 0 ≤ D.count t ∧ Ar.Fits 0 (D.count t) 128
  · simp only [hcn, and_self, if_true] at h
    rcases hv : cvtG (.int 0 (D.count t)) (.int 0 (D.count t - 1)) (.reg st.r) (st.r + 1) with
      _ | ⟨cv, ov, r1⟩
    · simp only [hv, reduceCtorEq] at h
    simp only [hv] at h
    rcases hb : bindCode (.int 0 (D.count t - 1)) ov r1 with _ | ⟨cb, a, r2⟩
    · simp only [hb, reduceCtorEq] at h
    simp only [hb] at h
    rcases hb2 : lowerB lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) ⟨r2, st.l + 4⟩ with
      _ | ⟨bb, s1⟩
    · simp only [hb2, reduceCtorEq] at h
    simp only [hb2] at h
    have h' := Option.some.inj h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    have S2 := lowerB_shape lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) ⟨r2, st.l + 4⟩ s1 bb hb2
    have hM0 : M.blk fn lb = some ⟨lb, [], [.bin st.r .add (Ar.wid 0 (D.count t))
        (.int (Ar.wid 0 (D.count t)) 0) (.int (Ar.wid 0 (D.count t)) 0)], .jmp st.l⟩ :=
      hM _ (List.mem_cons_self ..)
    have hMH : M.blk fn st.l = some ⟨st.l, [], [], .brc .ult (Ar.wid 0 (D.count t)) (.reg st.r)
        (.int (Ar.wid 0 (D.count t)) (D.count t)) (st.l + 1) k⟩ :=
      hM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hMB : M.blk fn (st.l + 1) = some ⟨st.l + 1, [], cv ++ cb, .jmp (st.l + 3)⟩ :=
      hM _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hMI : M.blk fn (st.l + 2) = some ⟨st.l + 2, [], [.bin st.r .add (Ar.wid 0 (D.count t))
        (.reg st.r) (.int (Ar.wid 0 (D.count t)) 1)], .jmp st.l⟩ :=
      hM _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    have hMbb : InM M fn bb := fun b hb' =>
      hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hb'))))
    have hKbd := kok_of_shape S2 hMbb
    have hKI : KOk M fn (st.l + 2) := ⟨_, hMI, rfl⟩
    have hKH : KOk M fn st.l := ⟨_, hMH, rfl⟩
    simp only [execStmt]
    -- the counter starts at zero
    have hinit : seqI [Instr.bin st.r .add (Ar.wid 0 (D.count t)) (.int (Ar.wid 0 (D.count t)) 0)
        (.int (Ar.wid 0 (D.count t)) 0)] m rs
        = some (m, rs.set st.r (Val.ofInt (Ar.wid 0 (D.count t)) ((0 : Nat) : Int))) := by
      simp only [seqI, stepI, Opd.ev, val_bin_add, Int.add_zero, Option.map_some, Int.cast_ofNat_Int]
    obtain ⟨bkh, hbkh, hkph⟩ := hKH
    have hI0 := reach_block_jmp (S := S) (ks := ks) (dst := dst) hM0 rfl hbkh hkph hinit
    have hmap : (alleIndizes (D.count t)).map (·.n) =
        (List.range' 0 ((D.count t).toNat - 0)).map (fun k : Nat => (k : Int)) := by
      rw [alleIndizes_map, Nat.sub_zero, ← List.range_eq_range']
    have hE0 := envRep_regs (rs' := rs.set st.r (Val.ofInt (Ar.wid 0 (D.count t)) ((0 : Nat) : Int))) cenv ρ
      (fun x hx => regs_set_ne rs st.r x _ (Nat.ne_of_lt (hc x hx))) hE
    exact outok_lift hI0 (fr_regs (fun x hx => regs_set_ne rs st.r x _ (Nat.ne_of_lt hx))) (Nat.le_refl _) hc _
      (traverse_loop (lay := lay) (lv := lv) (O := O) (passes := passes) (R := R) t inv body
        (c := st.r) (H := st.l) (Bl := st.l + 1) (I := st.l + 2) (Bd := st.l + 3) (cv := cv) (cb := cb)
        (ov := ov) (a := a) (r1 := r1) (r2 := r2) (r' := s1.r) hcn.1 hcn.2 hv hb S2.2.2 hMH hMB hMI hk hKbd
        (fun σ ρ' m rs hR hE hW hc => ih_lowerB_ok_body lay hL (a :: cenv) (k, st.l + 2) O passes R (st.l + 3)
          (st.l + 2) ⟨r2, st.l + 4⟩ s1 bb hb2 M S fn hMbb hKI ⟨hk, hKI⟩ hFn hCall σ ρ' m rs ks dst hR hE hW hc)
        (alleIndizes (D.count t)) 0 hmap (Nat.zero_le _) σ ρ m
        (rs.set st.r (Val.ofInt (Ar.wid 0 (D.count t)) ((0 : Nat) : Int))) hR hE0 hW hc (regs_set_same _ _ _))
  · simp only [hcn, ↓reduceIte, reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerS_ok_retScoped (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (Λ)
    (e)
    (Rr)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.retScoped (Λ := Λ) e Rr : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.retScoped (Λ := Λ) e Rr : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  simp only [execStmt, OutOk]
  obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerRet_ok lay hL cenv V.gruende e lb st st' blks h M S fn hM
    (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ m rs ks dst hR hE hc
  have hRl : Rep lay (σ.lese Λ e.orte) m := hR
  exact ⟨m, f', hr, hf1, hf2, hret, hRl.gibt_foldl Rr.scopes, hW, hFr⟩

set_option linter.unusedSectionVars false in
theorem lowerS_ok_retWhyScoped (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (Rr)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.retWhyScoped (Λ := Λ) r Rr : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.retWhyScoped (Λ := Λ) r Rr : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  simp only [execStmt, OutOk]
  obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerWhy_ok lay cenv V.gruende V.erg r.val lb st st' blks h M S fn hM
    m rs ks dst
  exact ⟨m, f', hr, hf1, hf2, hret, hR.gibt_foldl Rr.scopes, hW, hFr⟩

set_option linter.unusedSectionVars false in
theorem lowerB_ok_narrowRequired (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
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
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (Gabbro.Grammatik.Block.narrowRequired (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R (Gabbro.Grammatik.Block.narrowRequired (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') σ ρ) :=
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
  rcases hb2 : lowerB lay (a :: cenv) lv rest (st.l + 2) k ⟨r4, st.l + 3⟩ with _ | ⟨br, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  simp only [hb2] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have m1 := lowerE_mono lay cenv _ st.r _ hcd
  have m2 := lowerE_mono lay cenv e r1 _ he
  have m3 := cvtG_mono hv
  have m4 := bindCode_mono hb
  have S2 := lowerB_shape lay (a :: cenv) lv rest (st.l + 2) k ⟨r4, st.l + 3⟩ s2 br hb2
  have hb0 := hM _ (List.mem_singleton_self ..)
  have hbb := hM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hMr : InM M fn br := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb')))
  have hKr := kok_of_shape S2 hMr
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
    have hbound : ∀ x ∈ a :: cenv, x < a + 1 := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc3 x hx') hra)
    have IHr := ih_lowerB_ok_rest lay hL (a :: cenv) lv O passes R (st.l + 2) k ⟨a + 1, st.l + 3⟩ s2 br hb2
      M S fn hMr hk hlv hFn hCall (σ.lese Λ e.orte) (Env.cons ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hn.1, hn.2⟩ ρ) m1 rs4 ks dst hRn hEnew hWn hbound
    have hF123 : Fr lay cenv st.r m rs m1 rs4 :=
      fr_trans (fr_regs hag1) (fr_trans (fr_regs hag2) (fr_trans (fr_regs hag3) hFb hr3 hc2) hr2 hc1) hr1 hc
    exact outok_bind (Reach.trans hbr hreach2) hF123 hcell hc
      (Nat.le_trans (Nat.le_trans hr1 (Nat.le_trans hr2 (Nat.le_trans hr3 hra)))
        (Nat.le_succ a)) _ IHr
  · rw [dif_neg hn]
    exact trivial

end Gabbro.Code.Lower
