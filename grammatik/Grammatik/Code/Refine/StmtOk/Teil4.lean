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
public import Grammatik.Code.Refine.StmtOk.Teil3

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl alleIndizes evalArgs ergWert)
variable {D : Deklaration} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem lowerB_ok_check (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (Λ)
    (c)
    (sonst)
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (.check (Λ := Λ) c sonst rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R (.check (Λ := Λ) c sonst rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [lowerB] at h
  rcases hc1 : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
  · simp only [hc1, reduceCtorEq] at h
  simp only [hc1] at h
  rcases hb1 : lowerEnd lay cenv lv sonst st.l ⟨r1, st.l + 2⟩ with _ | ⟨be, s1⟩
  · simp only [hb1, reduceCtorEq] at h
  simp only [hb1] at h
  rcases hb2 : lowerB lay cenv lv rest (st.l + 1) k s1 with _ | ⟨br, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  simp only [hb2] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have S1 := lowerEnd_shape lay cenv lv sonst st.l ⟨r1, st.l + 2⟩ s1 be hb1
  have S2 := lowerB_shape lay cenv lv rest (st.l + 1) k s1 s2 br hb2
  have hb := hM _ (List.mem_cons_self ..)
  have hMe : InM M fn be := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_append_left _ hb'))
  have hMr : InM M fn br := fun b hb' =>
    hM b (List.mem_cons_of_mem _ (List.mem_append_right _ hb'))
  have hKe := kok_of_shape S1 hMe
  have hKr := kok_of_shape S2 hMr
  obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ c.orte := ⟨_, rfl⟩
  try rw [← hσl]
  have hRl : Rep lay σl m := by rw [hσl]; exact hR
  obtain ⟨Fc, _⟩ := lowerE_ok lay hL c cenv st.r (cc, oc, r1) hc1 σl σl ρ m rs hRl hE hc
  obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fc
  have hs1' : seqI cc m rs = some (m, rs1) := hs1
  have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
  have hc1' : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
  have hbrT : (eval σl c σl ρ : Bool) = true →
      Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l + 1, 0, rs1, dst⟩ ks) := by
    intro hv
    have hev : oc.ev rs1 = some (.int 1 (1 : BitVec 1)) := by
      rw [hev1]
      show some (Val.bool (eval σl c σl ρ)) = _
      rw [hv]; rfl
    obtain ⟨bk, hbk, hkp⟩ := hKr
    have := reach_block_br (S := S) (ks := ks) (dst := dst) (x := (1 : BitVec 1)) hb rfl hs1' hev
      (by simpa using hbk) hkp
    simpa using this
  have hbrF : (eval σl c σl ρ : Bool) = false →
      Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m ⟨fn, st.l, 0, rs1, dst⟩ ks) := by
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
  simp only [execBlock]
  try rw [← hσl]
  by_cases hv : (eval σl c σl ρ : Bool) = true
  · have hv' : Gabbro.Grammatik.wahr? (eval σl c σl ρ) = true := hv
    rw [if_pos hv']
    exact outok_lift (hbrT hv) (fr_regs hag1) (Nat.le_trans hr1 S1.2.2) hc _
      (ih_lowerB_ok_rest lay hL cenv lv O passes R (st.l + 1) k s1 s2 br hb2
      M S fn hMr hk hlv hFn hCall σl ρ m rs1 ks dst hRl hE1 hW (fun x hx => Nat.lt_of_lt_of_le (hc1' x hx) S1.2.2))
  · have hv0 : (eval σl c σl ρ : Bool) = false := Bool.eq_false_iff.mpr hv
    have hv' : ¬ (Gabbro.Grammatik.wahr? (eval σl c σl ρ) = true) := hv
    rw [if_neg hv']
    exact outok_mono S2.2.2 _ (outok_lift (hbrF hv0) (fr_regs hag1) hr1 hc _ (outok_of_endok _
      (ih_lowerEnd_ok_sonst lay hL cenv lv O passes R st.l ⟨r1, st.l + 2⟩ s1 be hb1 M S fn hMe hlv hFn hCall σl ρ m rs1
        ks dst hRl hE1 hW hc1')))

set_option linter.unusedSectionVars false in
theorem lowerB_ok_GabbroGrammatikBlockbindCall (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (τ)
    (Λ)
    (f)
    (args)
    (he)
    (zz1)
    (hr)
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (Gabbro.Grammatik.Block.bindCall (τ := τ) (Λ := Λ) f args he zz1 hr rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
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
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R (Gabbro.Grammatik.Block.bindCall (τ := τ) (Λ := Λ) f args he zz1 hr rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') σ ρ) :=
  by
      simp only [lowerB] at h
      rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
      · simp only [hla, reduceCtorEq] at h
      simp only [hla] at h
      rcases hb : bindCode τ (.reg r1) (r1 + 1) with _ | ⟨cb, a, r2⟩
      · simp only [hb, reduceCtorEq] at h
      simp only [hb] at h
      rcases hr' : lowerB lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp only [hr', reduceCtorEq] at h
      simp only [hr'] at h
      have h' := Option.some.inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have hm1 := lowerArgs_mono lay cenv args st.r _ hla
      have SS := lowerB_shape lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ s2 b2 hr'
      have hb0 := hM _ (List.mem_cons_self ..)
      have hM2 : InM M fn b2 := fun b hb' => hM b (List.mem_cons_of_mem _ hb')
      obtain ⟨bk2, hbk2, hkp2⟩ := kok_of_shape SS hM2
      have hRl : Rep lay (σ.lese Λ args.orte) m := hR
      obtain ⟨rs1, hs1, hr1, hag1, hmap⟩ := lowerArgs_ok lay hL cenv args st.r (ca, ops, r1) hla
        (σ.lese Λ args.orte) (σ.lese Λ args.orte) ρ m rs hRl hE hc
      have hs1' : seqI ca m rs = some (m, rs1) := hs1
      have hc1 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr1
      simp only [execBlock]
      rcases hRf : R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
        ⟨σ', v⟩ | ⟨σ', r⟩ | e | e
      · simp only [hRf]
        have hw : retImg lay (D.gruende f) (D.erg f) v = some (encR lay τ (ergWert he v)) := by
          unfold retImg
          rw [if_pos hr]
          exact ergImg_ergWert lay he v
        obtain ⟨m', hreach, hRn, hWn, hK⟩ := call_run_some hFn hCall hRf hb0 (pre := ca) (post := cb) (r := r1) (ks := ks) (dst := dst)
          (by simp only [List.append_assoc, List.cons_append, List.nil_append]) hw hs1' hmap hRl hW
        -- the cells of the locals survive the call
        have hE1 := envRep_regs cenv ρ (fun x hx => hag1 x (hc x hx)) hE
        have hEm : EnvRep lay rs1 m' cenv ρ := envRep_load cenv ρ
          (fun r hr' b hb' hf o t w hl => hK.2 b hf (envRep_blocks_lt hW.1 cenv ρ hE1 r hr' b hb') o t w hl) hE1
        have hag2 : ∀ x ∈ cenv, (rs1.set r1 (encR lay τ (ergWert he v))) x = rs1 x := fun x hx =>
          regs_set_ne rs1 r1 x _ (Nat.ne_of_lt (hc1 x hx))
        have hEs := envRep_regs (rs' := rs1.set r1 (encR lay τ (ergWert he v))) cenv ρ hag2 hEm
        obtain ⟨m1, rs4, hs4, hRn', hEnew, hWn', hra, hr2e, hag4, hFb, hcell⟩ :=
          bindCode_run lay (ergWert he v) (.reg r1) (r1 + 1) m' (rs1.set r1 (encR lay τ (ergWert he v))) hRn hEs hWn
            (by simp only [Opd.ev, regs_set_same]) (opdlt_reg r1 (r1 + 1) (Nat.lt_succ_self _))
            (fun x hx => Nat.lt_succ_of_lt (hc1 x hx)) hb
        subst hr2e
        -- the rest of the block: `cb`, then the jump
        have hstr : Stretch M fn lb (ca.length + 1) cb := ⟨_, hb0, fun i hi => by
          show (ca ++ [Instr.call (some r1) (lay.fno f) ops] ++ cb)[ca.length + 1 + i]? = some cb[i]
          rw [List.append_assoc, List.getElem?_append_right (by omega)]
          simp only [List.cons_append, List.nil_append, show ca.length + 1 + i - ca.length = i + 1 by omega,
  List.getElem?_cons_succ, List.getElem?_eq_getElem hi]⟩
        have hseqb := reach_seq M S cb m'
          ⟨fn, lb, ca.length + 1, rs1.set r1 (encR lay τ (ergWert he v)), dst⟩ ks m1 rs4 hstr hs4
        have hjmp := reach_jmp (S := S) (m := m1) (ks := ks)
          (f := ⟨fn, lb, ca.length + 1 + cb.length, rs4, dst⟩) (l := st.l)
          (blk := ⟨lb, [], ca ++ [.call (some r1) (lay.fno f) ops] ++ cb, .jmp st.l⟩)
          ⟨hb0, by simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_cons]; omega, rfl⟩ hbk2 hkp2
        have hbound : ∀ x ∈ a :: cenv, x < a + 1 := fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc1 x hx') (Nat.le_trans (Nat.le_succ _) hra))
        have IHr := ih_lowerB_ok_rest lay hL (a :: cenv) lv O passes R st.l k ⟨a + 1, st.l + 1⟩ s2 b2 hr' M S fn
          hM2 hk hlv hFn hCall σ'
          (Env.cons (ergWert he v) ρ) m1 rs4 ks dst hRn' hEnew hWn' hbound
        have hFa : Fr lay cenv st.r m rs m' rs1 := ⟨fun x hx => hag1 x hx, hK.1,
          fun b hf hb' _ o t w hl => hK.2 b hf hb' o t w hl⟩
        have hFs : Fr lay cenv st.r m' rs1 m' (rs1.set r1 (encR lay τ (ergWert he v))) :=
          fr_regs (fun x hx => regs_set_ne rs1 r1 x _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le hx hr1)))
        have hFtot : Fr lay cenv st.r m rs m1 rs4 :=
          fr_trans hFa (fr_trans hFs (hFb) (Nat.le_succ_of_le hr1) hc) (Nat.le_refl _) hc
        have hcell' : ∀ b, rs4 a = some (.ptr b 0) → m.next ≤ b := fun b hb' => Nat.le_trans hK.1 (hcell b hb')
        have hreach2 : Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks) (.run m1 ⟨fn, st.l, 0, rs4, dst⟩ ks) := by
          have := Reach.trans hreach (Reach.trans hseqb hjmp)
          simpa using this
        exact outok_bind hreach2 hFtot hcell' hc (Nat.le_succ_of_le (Nat.le_trans hr1 (Nat.le_trans (Nat.le_succ _) hra)))
          _ IHr
      · exact (Fin.cast hr r).elim0
      · simp only [OutOk]
      · simp only [OutOk]

set_option linter.unusedSectionVars false in
theorem lowerB_ok_GabbroGrammatikBlockbindCallElse (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (f)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerB lay cenv lv (Gabbro.Grammatik.Block.bindCallElse (τ := zi_τ) f args he hp hr err rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
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
    (ih_lowerEnd_ok_err : ∀ (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f), ∀ (lb : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerEnd lay cenv lv err lb st = some (blks, st') → ∀ (M : Modl), ∀ (S : Sees), ∀ (fn : Nat), InM M fn blks → LvOk M fn lv → FnOk lay M → CallRef lay M S R → ∀ (σ : World D), ∀ (ρ : Env D _), ∀ (m : Mem), ∀ (rs : Regs), ∀ (ks : List Frame), ∀ (dst : Option Reg), Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) → EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R err σ ρ))
    : OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R (Gabbro.Grammatik.Block.bindCallElse (τ := zi_τ) f args he hp hr err rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') σ ρ) :=
  
  bindCallElse_ok lay hL cenv lv O passes R f args he hp hr err rest
    (fun a lb' k' st1 st1' blks' h' M' S' fn' hM' hk' hlv' hFn' hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc' =>
      ih_lowerB_ok_rest lay hL (a :: cenv) lv O passes R lb' k' st1 st1' blks' h' M' S' fn' hM' hk' hlv' hFn'
        hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc')
    (fun a lb' st1 st1' blks' h' M' S' fn' hM' hlv' hFn' hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc' =>
      ih_lowerEnd_ok_err lay hL (a :: cenv) lv O passes R lb' st1 st1' blks' h' M' S' fn' hM' hlv' hFn'
        hCall' σ' ρ' m' rs' ks' dst' hR' hE' hW' hc')
    lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc

end Gabbro.Code.Lower
