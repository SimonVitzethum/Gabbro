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
public import Grammatik.Code.Refine.StmtOk.Teil1Pointer

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl alleIndizes evalArgs ergWert)
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem lowerS_ok_GabbroGrammatikStmtassignVar (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (τ)
    (Λ)
    (x)
    (e)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (Gabbro.Grammatik.Stmt.assignVar (τ := τ) (Λ := Λ) x e : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (Gabbro.Grammatik.Stmt.assignVar (τ := τ) (Λ := Λ) x e : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  rcases hcx : cenv[varIdx x]? with _ | a
  · simp only [hcx, reduceCtorEq] at h
  simp only [hcx] at h
  have hs : supp τ = true := by
    cases hbb : supp τ
    · simp only [hbb, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
    · rfl
  simp only [hs, if_true] at h
  rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
  · simp only [he, reduceCtorEq] at h
  simp only [he] at h
  rcases hst : storeTo τ oe r1 (.reg a) with _ | ⟨cs, r2⟩
  · simp only [hst, reduceCtorEq] at h
  simp only [hst] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have hb := hM _ (List.mem_singleton_self _)
  obtain ⟨bk, hbk, hkp⟩ := hk
  simp only [execStmt, OutOk]
  obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ e.orte := ⟨_, rfl⟩
  try rw [← hσl]
  have hRl : Rep lay σl m := by rw [hσl]; exact hR
  obtain ⟨Fe, _⟩ := lowerE_ok lay hL e cenv st.r (ce, oe, r1) he σl σl ρ m rs hRl hE hc
  obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fe
  have hs1' : seqI ce m rs = some (m, rs1) := hs1
  obtain ⟨a', b, ha', hsx, hrb, hfr, hlb⟩ := envRep_get x cenv ρ hE
  rw [hcx] at ha'
  have ha'' := Option.some.inj ha'
  subst ha''
  have hamem : a ∈ cenv := List.mem_of_getElem? hcx
  have hra : a < st.r := hc a hamem
  have hrs1 : rs1 a = rs a := hag1 a hra
  have hp1 : (Opd.reg a).ev rs1 = some (.ptr b 0) := by
    show rs1 a = _
    rw [hrs1]; exact hrb
  obtain ⟨m', rs2, hs2, hst2, hr2, hag2⟩ := storeTo_run lay τ (eval σl e σl ρ) hs oe r1 (.reg a)
    b 0 m rs1 hev1 hlt1 hp1 (opdlt_reg a r1 (Nat.lt_of_lt_of_le hra hr1)) ⟨_, hlb⟩ cs r2 hst
  have hseq : seqI (ce ++ cs) m rs = some (m', rs2) := by
    rw [seqI_append, hs1']; exact hs2
  have hFr : Fr lay cenv st.r m rs m' rs2 := fr_store hst2 (Or.inr ⟨a, hamem, hrb⟩) (fun x hx => by
    rw [hag2 x (Nat.lt_of_lt_of_le hx hr1), hag1 x hx])
  refine ⟨m', rs2, reach_block_jmp hb rfl hbk hkp hseq, ?_, hFr⟩
  have hRn : Rep lay σl m' := rep_store_other hRl hst2 ⟨hfr.1, hfr.2.1⟩
  have hag : ∀ r ∈ cenv, rs2 r = rs r := fun r hr => by
    have l1 : r < r1 := Nat.lt_of_lt_of_le (hc r hr) hr1
    rw [hag2 r l1, hag1 r (hc r hr)]
  have hE2 := envRep_regs cenv ρ hag hE
  have hrb2 : rs2 a = some (.ptr b 0) := by rw [hag a hamem]; exact hrb
  refine ⟨hRn, envRep_set x cenv ρ (eval σl e σl ρ) a hE2 hcx hrb2 hst2, wfL_store hst2 hW, ?_⟩
  intro x hx
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hc x hx) hr1) hr2

set_option linter.unusedSectionVars false in
theorem lowerS_ok_ite (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (Λ)
    (c)
    (tb)
    (eb)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.ite (Λ := Λ) c tb eb : Gabbro.Grammatik.Stmt D V l Γ Λ Λ') lb k st = some (blks, st'))
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
    (ih_lowerB_ok_tb : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv tb lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R tb σ ρ))
    (ih_lowerB_ok_eb : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv eb lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R eb σ ρ))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.ite (Λ := Λ) c tb eb : Gabbro.Grammatik.Stmt D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [lowerS] at h
  rcases hc1 : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
  · simp only [hc1, reduceCtorEq] at h
  simp only [hc1] at h
  rcases hb1 : lowerB lay cenv lv tb st.l k ⟨r1, st.l + 2⟩ with _ | ⟨bt, s1⟩
  · simp only [hb1, reduceCtorEq] at h
  simp only [hb1] at h
  rcases hb2 : lowerB lay cenv lv eb (st.l + 1) k s1 with _ | ⟨be, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  simp only [hb2] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have S1 := lowerB_shape lay cenv lv tb st.l k ⟨r1, st.l + 2⟩ s1 bt hb1
  have S2 := lowerB_shape lay cenv lv eb (st.l + 1) k s1 s2 be hb2
  have hb := hM _ (List.mem_cons_self ..)
  have hMt : InM M fn bt := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_append_left _ hb'))
  have hMe : InM M fn be := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_append_right _ hb'))
  have hKt := kok_of_shape S1 hMt
  have hKe := kok_of_shape S2 hMe
  have hm12 : s1.r ≤ s2.r := S2.2.2
  obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ c.orte := ⟨_, rfl⟩
  try rw [← hσl]
  have hRl : Rep lay σl m := by rw [hσl]; exact hR
  obtain ⟨Fc, _⟩ := lowerE_ok lay hL c cenv st.r (cc, oc, r1) hc1 σl σl ρ m rs hRl hE hc
  obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fc
  have hs1' : seqI cc m rs = some (m, rs1) := hs1
  have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
  have hc1' : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
  have hbrT : (eval σl c σl ρ : Bool) = true →
      Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l, 0, rs1, dst⟩ ks) := by
    intro hv
    have hev : oc.ev rs1 = some (.int 1 (1 : BitVec 1)) := by
      rw [hev1]
      show some (Val.bool (eval σl c σl ρ)) = _
      rw [hv]; rfl
    obtain ⟨bk, hbk, hkp⟩ := hKt
    have := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (1 : BitVec 1)) hb rfl hs1' hev
      (by simpa using hbk) hkp
    simpa using this
  have hbrF : (eval σl c σl ρ : Bool) = false →
      Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l + 1, 0, rs1, dst⟩ ks) := by
    intro hv
    have hev : oc.ev rs1 = some (.int 1 (0 : BitVec 1)) := by
      rw [hev1]
      show some (Val.bool (eval σl c σl ρ)) = _
      rw [hv]; rfl
    obtain ⟨bk, hbk, hkp⟩ := hKe
    have h01 : ¬ ((0 : BitVec 1) = 1) := by decide
    have := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (0 : BitVec 1)) hb rfl hs1' hev
      (by simpa [h01] using hbk) hkp
    simpa [h01] using this
  simp only [execStmt]
  try rw [← hσl]
  by_cases hv : (eval σl c σl ρ : Bool) = true
  · have hv' : Gabbro.Grammatik.wahr? (eval σl c σl ρ) = true := hv
    rw [if_pos hv']
    exact outok_mono hm12 _ (outok_lift (hbrT hv) (fr_regs hag1) hr1 hc _ (ih_lowerB_ok_tb lay hL cenv lv O passes R st.l k
      ⟨r1, st.l + 2⟩ s1 bt hb1 M S fn hMt hk hlv hFn hCall σl ρ m rs1 ks dst hRl hE1 hW hc1'))
  · have hv0 : (eval σl c σl ρ : Bool) = false := Bool.eq_false_iff.mpr hv
    have hv' : ¬ (Gabbro.Grammatik.wahr? (eval σl c σl ρ) = true) := hv
    rw [if_neg hv']
    exact outok_lift (hbrF hv0) (fr_regs hag1) (Nat.le_trans hr1 S1.2.2) hc _
      (ih_lowerB_ok_eb lay hL cenv lv O passes R (st.l + 1) k s1 s2 be hb2
      M S fn hMe hk hlv hFn hCall σl ρ m rs1 ks dst hRl hE1 hW (fun x hx => Nat.lt_of_lt_of_le (hc1' x hx) S1.2.2))

set_option linter.unusedSectionVars false in
theorem lowerS_ok_onOption (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (o)
    (p)
    (a)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.onOption (n := zi_n) o p a : Gabbro.Grammatik.Stmt D V l Γ Λ Λ') lb k st = some (blks, st'))
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
    (ih_lowerB_ok_p : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv p lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R p σ ρ))
    (ih_lowerB_ok_a : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv a lb k st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R a σ ρ))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.onOption (n := zi_n) o p a : Gabbro.Grammatik.Stmt D V l Γ Λ Λ') σ ρ) :=
  
  onOption_ok lay hL cenv lv O passes R o p a
    (fun c lb' k' st1 st1' blks' h' M' S' fn' hM' hk' hlv' hFn' hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc' =>
      ih_lowerB_ok_p lay hL (c :: cenv) lv O passes R lb' k' st1 st1' blks' h' M' S' fn' hM' hk' hlv' hFn'
        hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc')
    (fun lb' k' st1 st1' blks' h' M' S' fn' hM' hk' hlv' hFn' hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc' =>
      ih_lowerB_ok_a lay hL cenv lv O passes R lb' k' st1 st1' blks' h' M' S' fn' hM' hk' hlv' hFn'
        hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc')
    lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc

set_option linter.unusedSectionVars false in
theorem lowerS_ok_call (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (Λ)
    (f)
    (args)
    (zz1)
    (hr)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.call (Λ := Λ) f args zz1 hr : Gabbro.Grammatik.Stmt D V l Γ Λ (Gabbro.Grammatik.nach D f Λ)) lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.call (Λ := Λ) f args zz1 hr : Gabbro.Grammatik.Stmt D V l Γ Λ (Gabbro.Grammatik.nach D f Λ)) σ ρ) :=
  by
  simp only [lowerS] at h
  rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
  · simp only [hla, reduceCtorEq] at h
  simp only [hla, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hb := hM _ (List.mem_singleton_self _)
  obtain ⟨bk, hbk, hkp⟩ := hk
  have hRl : Rep lay (σ.lese Λ args.orte) m := hR
  obtain ⟨rs1, hs1, hr1, hag1, hmap⟩ := lowerArgs_ok lay hL cenv args st.r (ca, ops, r1) hla
    (σ.lese Λ args.orte) (σ.lese Λ args.orte) ρ m rs hRl hE hc
  have hs1' : seqI ca m rs = some (m, rs1) := hs1
  simp only [execStmt]
  rcases hRf : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
    ⟨σ', v⟩ | ⟨σ', r⟩ | e | e
  · simp only [OutOk]
    obtain ⟨m', hreach, hRn, hWn, hK⟩ := call_run_none hFn hCall hRf hb (pre := ca) (post := []) (ks := ks) (dst := dst) rfl hs1'
      hmap hRl hW
    have hjmp := reach_jmp (S := S) (m := m') (ks := ks)
      (f := ⟨fn, lb, ca.length + 1, rs1, dst⟩) (l := k) (blk := ⟨lb, [], ca ++ [.call none (lay.fno f) ops], .jmp k⟩)
      ⟨hb, by simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Std.le_refl], rfl⟩ hbk hkp
    have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
    have hEm : EnvRep lay rs1 m' cenv ρ := envRep_load cenv ρ
      (fun r hr' b hb' hf o t w hl => hK.2 b hf (envRep_blocks_lt hW.1 cenv ρ hE1 r hr' b hb') o t w hl) hE1
    exact ⟨m', rs1, Reach.trans hreach hjmp, ⟨hRn, hEm, hWn, fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1⟩,
      fun x hx => hag1 x hx, hK.1, fun b hf hb' _ o t w hl => hK.2 b hf hb' o t w hl⟩
  · exact (Fin.cast hr r).elim0
  · simp only [OutOk]
  · simp only [OutOk]

set_option linter.unusedSectionVars false in
theorem lowerS_ok_traverse (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (Λ)
    (t)
    (inv)
    (body)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.traverse (Λ := Λ) t inv body : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R (.traverse (Λ := Λ) t inv body : Gabbro.Grammatik.Stmt D V l Γ Λ (Λ)) σ ρ) :=
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

end Gabbro.Code.Lower
