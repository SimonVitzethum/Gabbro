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
public import Grammatik.Code.Refine.StmtOk.Teil2

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl alleIndizes evalArgs ergWert)
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem lowerS_ok_retry (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (Λ)
    (n)
    (bis)
    (body)
    (ueb)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.retry (Λ := Λ) n bis body ueb : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
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
    (ih_lowerB_ok_ueb : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv ueb lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R ueb σ ρ))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.retry (Λ := Λ) n bis body ueb : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  by_cases hcn : retryOk n = true
  · simp only [hcn, if_true] at h
    rcases hcb : lowerE lay cenv bis (st.r + 1) with _ | ⟨cb, ob, r1⟩
    · simp only [hcb, reduceCtorEq] at h
    simp only [hcb] at h
    rcases hb1 : lowerB lay cenv (k, st.l + 3) body (st.l + 4) (st.l + 3) ⟨r1, st.l + 5⟩ with _ | ⟨bb, s1⟩
    · simp only [hb1, reduceCtorEq] at h
    simp only [hb1] at h
    rcases hb2 : lowerB lay cenv lv ueb (st.l + 2) k s1 with _ | ⟨bo, s2⟩
    · simp only [hb2, reduceCtorEq] at h
    simp only [hb2] at h
    have h' := Option.some.inj h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    have S1 := lowerB_shape lay cenv (k, st.l + 3) body (st.l + 4) (st.l + 3) ⟨r1, st.l + 5⟩ s1 bb hb1
    have S2 := lowerB_shape lay cenv lv ueb (st.l + 2) k s1 s2 bo hb2
    have hM0 : M.blk fn lb = some ⟨lb, [], [.bin st.r .add (Ar.wid 0 (n : Int))
        (.int (Ar.wid 0 (n : Int)) 0) (.int (Ar.wid 0 (n : Int)) 0)], .jmp st.l⟩ :=
      hM _ (List.mem_cons_self ..)
    have hMH : M.blk fn st.l = some ⟨st.l, [], cb, .br ob k (st.l + 1)⟩ :=
      hM _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hMT : M.blk fn (st.l + 1) = some ⟨st.l + 1, [], [], .brc .ult (Ar.wid 0 (n : Int)) (.reg st.r)
        (.int (Ar.wid 0 (n : Int)) (n : Int)) (st.l + 4) (st.l + 2)⟩ :=
      hM _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hMI : M.blk fn (st.l + 3) = some ⟨st.l + 3, [], [.bin st.r .add (Ar.wid 0 (n : Int))
        (.reg st.r) (.int (Ar.wid 0 (n : Int)) 1)], .jmp st.l⟩ :=
      hM _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    have hMbb : InM M fn bb := fun b hb' => hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hb')))))
    have hMbo : InM M fn bo := fun b hb' => hM b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hb')))))
    have hKbd := kok_of_shape S1 hMbb
    have hKov := kok_of_shape S2 hMbo
    have hKI : KOk M fn (st.l + 3) := ⟨_, hMI, rfl⟩
    have hKH : KOk M fn st.l := ⟨_, hMH, rfl⟩
    simp only [execStmt]
    have hinit : seqI [Instr.bin st.r .add (Ar.wid 0 (n : Int)) (.int (Ar.wid 0 (n : Int)) 0)
        (.int (Ar.wid 0 (n : Int)) 0)] m rs
        = some (m, rs.set st.r (Val.ofInt (Ar.wid 0 (n : Int)) ((0 : Nat) : Int))) := by
      simp only [seqI, stepI, Opd.ev, val_bin_add, Int.add_zero, Option.map_some, Int.cast_ofNat_Int]
    obtain ⟨bkh, hbkh, hkph⟩ := hKH
    have hI0 := reach_block_jmp (S := S) (ks := ks) (dst := dst) hM0 rfl hbkh hkph hinit
    have hE0 := envRep_regs (rs' := rs.set st.r (Val.ofInt (Ar.wid 0 (n : Int)) ((0 : Nat) : Int))) cenv ρ
      (fun x hx => regs_set_ne rs st.r x _ (Nat.ne_of_lt (hc x hx))) hE
    exact outok_lift hI0 (fr_regs (fun x hx => regs_set_ne rs st.r x _ (Nat.ne_of_lt hx))) (Nat.le_refl _) hc _
      (retry_loop (lay := lay) hL (lv := lv) (O := O) (passes := passes) (R := R) (cenv := cenv) n bis body ueb
        (c := st.r) (H := st.l) (T := st.l + 1) (OV := st.l + 2) (I := st.l + 3) (BD := st.l + 4)
        (cb := cb) (ob := ob) (r1 := r1) (rb := s1.r) (ro := s2.r) (retryOk_fits hcn) hcb S1.2.2 S2.2.2
        hMH hMT hMI hk hKbd hKov
        (fun σ ρ m rs hR hE hW hc => ih_lowerB_ok_body lay hL cenv (k, st.l + 3) O passes R (st.l + 4)
          (st.l + 3) ⟨r1, st.l + 5⟩ s1 bb hb1 M S fn hMbb hKI ⟨hk, hKI⟩ hFn hCall σ ρ m rs ks dst hR hE hW hc)
        (fun σ ρ m rs hR hE hW hc => ih_lowerB_ok_ueb lay hL cenv lv O passes R (st.l + 2) k s1 s2 bo hb2
          M S fn hMbo hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc)
        n 0 (by omega) σ ρ m (rs.set st.r (Val.ofInt (Ar.wid 0 (n : Int)) ((0 : Nat) : Int))) hR hE0 hW hc
        (regs_set_same _ _ _))
  · simp only [hcn, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerS_ok_forever (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (Λ)
    (a)
    (inv)
    (body)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.forever (Λ := Λ) a inv body : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.forever (Λ := Λ) a inv body : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  have hKl := kok_of_shape (lowerB_shape lay cenv (k, lb) body lb lb st st' blks h) hM
  simp only [execStmt]
  exact forever_ok a inv body (fun σ ρ m rs hR hE hW hc => ih_lowerB_ok_body lay hL cenv (k, lb) O passes R lb lb
    st st' blks h M S fn hM hKl ⟨hk, hKl⟩ hFn hCall σ ρ m rs ks dst hR hE hW hc) passes σ ρ m rs hR hE hW hc

set_option linter.unusedSectionVars false in
theorem lowerS_ok_retWhy (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (zz1)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.retWhy r zz1 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.retWhy r zz1 : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  simp only [execStmt, OutOk]
  obtain ⟨f', hr, hf1, hf2, hret, hFr⟩ := lowerWhy_ok lay cenv V.gruende V.erg r.val lb st st' blks h M S fn hM
    m rs ks dst
  exact ⟨m, f', hr, hf1, hf2, hret, hR, hW, hFr⟩

set_option linter.unusedSectionVars false in
theorem lowerB_ok_nil (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (.nil : Gabbro.Grammatik.Block D V l Γ Λ (Λ)) lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R (.nil : Gabbro.Grammatik.Block D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerB, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [execBlock, OutOk]
  have hb := hM _ (List.mem_singleton_self _)
  obtain ⟨bk, hbk, hkp⟩ := hk
  exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, ⟨hR, hE, hW, hc⟩, fr_regs (fun _ _ => rfl)⟩

set_option linter.unusedSectionVars false in
theorem lowerB_ok_cons (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (.cons (Λ' := zi_Λ') s rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
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
    (ih_lowerS_ok_s : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerS lay cenv lv s lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R s σ ρ))
    (ih_lowerB_ok_rest : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv rest lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R rest σ ρ))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R (.cons (Λ' := zi_Λ') s rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [lowerB] at h
  rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
  · simp only [hs, reduceCtorEq] at h
  simp only [hs] at h
  rcases hr : lowerB lay cenv lv rest st.l k s1 with _ | ⟨b2, s2⟩
  · simp only [hr, reduceCtorEq] at h
  simp only [hr] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have SS := lowerB_shape lay cenv lv rest st.l k s1 s2 b2 hr
  have hM1 : InM M fn b1 := fun b hb' => hM b (List.mem_append_left _ hb')
  have hM2 : InM M fn b2 := fun b hb' => hM b (List.mem_append_right _ hb')
  have hK2 := kok_of_shape SS hM2
  have IHs := ih_lowerS_ok_s lay hL cenv lv O passes R lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs M S fn hM1 hK2
    hlv hFn hCall σ ρ m rs ks dst hR hE hW hc
  have hle : s1.r ≤ s2.r := SS.2.2
  have S0 := lowerS_shape lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ s1 b1 hs
  simp only [execBlock]
  rcases hx : execStmt O passes R s σ ρ with ⟨σ1, ρ1⟩ | ⟨σ1, v1⟩ | ⟨σ1, r1'⟩ | ⟨h1, σ1, ρ1⟩ |
    ⟨h1, σ1, ρ1⟩ | e1 | e1
  · rw [hx] at IHs
    obtain ⟨m1, rs1, hr1, hP1, hF1⟩ := IHs
    obtain ⟨hRp, hEp, hWp, hcp⟩ := hP1
    simp only [hx]
    exact outok_lift hr1 hF1 S0.2.2 hc _ (ih_lowerB_ok_rest lay hL cenv lv O passes R st.l k s1 s2 b2 hr M S fn
      hM2 hk hlv hFn hCall σ1 ρ1 m1 rs1 ks dst hRp hEp hWp hcp)
  · rw [hx] at IHs
    simp only [hx]
    exact IHs
  · rw [hx] at IHs
    simp only [hx]
    exact IHs
  · rw [hx] at IHs
    simp only [hx]
    exact outok_mono hle _ IHs
  · rw [hx] at IHs
    simp only [hx]
    exact outok_mono hle _ IHs
  · simp only [hx, OutOk]
  · simp only [hx, OutOk]

set_option linter.unusedSectionVars false in
theorem lowerB_ok_GabbroGrammatikBlockbind (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (τ)
    (Λ)
    (e)
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (Gabbro.Grammatik.Block.bind (τ := τ) (Λ := Λ) e rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R (Gabbro.Grammatik.Block.bind (τ := τ) (Λ := Λ) e rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [lowerB] at h
  rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hb : bindCode τ oe r1 with _ | ⟨cb, a, r2⟩
  · simp only [hb, reduceCtorEq] at h
  simp only [hb] at h
  rcases hr : lowerB lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
  · simp only [hr, reduceCtorEq] at h
  simp only [hr] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have SS := lowerB_shape lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ s2 b2 hr
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
  have IHr := ih_lowerB_ok_rest lay hL (a :: cenv) lv O passes R st.l k ⟨a + 1, st.l + 1⟩ s2 b2 hr M S fn
    hM2 hk hlv hFn hCall σl (Env.cons (eval σl e σl ρ) ρ) m1 rs3 ks dst hRn hEnew hWn hbound
  simp only [execBlock]
  try rw [← hσl]
  exact outok_bind hreach hFbind hcell hc (Nat.le_succ_of_le (Nat.le_trans hr1 hra)) _ IHr

end Gabbro.Code.Lower
