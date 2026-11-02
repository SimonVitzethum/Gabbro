module
public import Grammatik.Code.Refine.Struct.Mono
@[expose] public section


/-
  File:      Grammatik/Code/Refine/Shape.lean
  Subject:   TRACK L, PHASE L1 -- THE SHAPE OF A LOWERING: the first block carries the entry label, no block has
             phis, the register counter does not fall (`Shape`), for every statement, block, end block and the arms
             of a `match` (mutual with the lowering, so by the same recursion).
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr Args)

variable {D : Deklaration}

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
      exact ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], Nat.le_refl _⟩
  | val e =>
      simp only [lowerErg] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp only [he, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv e st.r _ he
      simp only [he] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], m1⟩

theorem lowerErgF_shape (lay : Layout D) (cenv : List Reg) (n : Nat) {Γ : Ctx} {Λ : List (Res D)}
    {eo : Option GTy} (e : ErgExpr D Γ Λ eo) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerErgF lay cenv n e lb st = some (blks, st')) : Shape lb st st' blks := by
  cases e with
  | empty =>
      simp only [lowerErgF] at h
      split at h
      · have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        exact ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], Nat.le_refl _⟩
      · simp only [reduceCtorEq] at h
  | @val τ e =>
      cases τ with
      | int lo hi =>
          simp only [lowerErgF] at h
          rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
          · simp only [he, reduceCtorEq] at h
          have m1 := lowerE_mono lay cenv e st.r _ he
          simp only [he] at h
          split at h
          · rcases hnc : numCode lo hi (retW n (some (.int lo hi))) (n + 1) 0 oe r1 with ⟨cn, on, r2⟩
            have m2 := numCode_mono (lo := lo) (hi := hi) (W := retW n (some (.int lo hi))) (L := n + 1)
              (i := 0) (oe := oe) (r := r1)
            rw [hnc] at m2 h
            have := Option.some.inj h
            simp only [Prod.mk.injEq] at this
            obtain ⟨rfl, rfl⟩ := this
            simp only at m1 m2 ⊢
            exact ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], by show st.r ≤ r2; omega⟩
          · simp only [reduceCtorEq] at h
      | _ => simp only [lowerErgF, reduceCtorEq] at h

theorem lowerRet_shape (lay : Layout D) (cenv : List Reg) (n : Nat) {Γ : Ctx} {Λ : List (Res D)}
    {eo : Option GTy} (e : ErgExpr D Γ Λ eo) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerRet lay cenv n e lb st = some (blks, st')) : Shape lb st st' blks := by
  unfold lowerRet at h
  by_cases hn : n = 0
  · rw [if_pos hn] at h
    exact lowerErg_shape lay cenv e lb st st' blks h
  · rw [if_neg hn] at h
    exact lowerErgF_shape lay cenv n e lb st st' blks h

theorem lowerWhy_shape (n : Nat) (eo : Option GTy) (r : Nat) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerWhy n eo r lb st = some (blks, st')) : Shape lb st st' blks := by
  unfold lowerWhy at h
  split at h
  · have := Option.some.inj h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], Nat.le_refl _⟩
  · simp only [reduceCtorEq] at h

/-- A call with a failure channel: the shape of its lowering, given the shape of the two continuations. -/
theorem bindCallElse_shape (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : GTy} (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : Gabbro.Grammatik.RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (err : Gabbro.Grammatik.Endblock D V l (.why (D.gruende f) :: Γ) (Gabbro.Grammatik.nach D f Λ))
    (rest : Gabbro.Grammatik.Block D V l (τ :: Γ) (Gabbro.Grammatik.nach D f Λ) Λ') (lb k : Lbl)
    (st st' : St) (blks : List Block)
    (IHrest : ∀ a st1 s1 bo, lowerB lay (a :: cenv) lv rest (st.l + 2) k st1 = some (bo, s1) →
      Shape (st.l + 2) st1 s1 bo)
    (IHerr : ∀ a st1 s2 be, lowerEnd lay (a :: cenv) lv err (st.l + 3) st1 = some (be, s2) →
      Shape (st.l + 3) st1 s2 be)
    (h : lowerB lay cenv lv (Gabbro.Grammatik.Block.bindCallElse f args he hp hr err rest) lb k st
      = some (blks, st')) : Shape lb st st' blks := by
  unfold lowerB at h
  rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
  · simp only [hla, reduceCtorEq] at h
  have m1 := lowerArgs_mono lay cenv args st.r _ hla
  simp only [hla] at h
  unfold lowerElse at h
  cases τ with
  | int lo hi =>
      simp only at h
      split at h
      · rcases hp' : payCode (failTop (D.gruende f) (some (.int lo hi))) (retW (D.gruende f) (some (.int lo hi)))
            (D.gruende f + 1) lo hi (.reg r1) (r1 + 2) with _ | ⟨cp, op, r2⟩
        · simp only [hp', reduceCtorEq] at h
        have m2 := payCode_mono hp'
        simp only [hp'] at h
        rcases hb : bindCode (.int lo hi) op r2 with _ | ⟨cb, a, r3⟩
        · simp only [hb, reduceCtorEq] at h
        have m3 := bindCode_mono hb
        simp only [hb] at h
        rcases hb1 : lowerB lay (a :: cenv) lv rest (st.l + 2) k ⟨r3, st.l + 4⟩ with _ | ⟨bo, s1⟩
        · simp only [hb1, reduceCtorEq] at h
        have S1 := IHrest a _ _ _ hb1
        simp only [hb1] at h
        rcases hc : cvt (retW (D.gruende f) (some (.int lo hi))) (Ar.wid 0 ((D.gruende f : Int) - 1)) false
            (.reg s1.r) (s1.r + 1) with ⟨cv, ov, r4⟩
        have m4 := cvt_mono (retW (D.gruende f) (some (.int lo hi))) (Ar.wid 0 ((D.gruende f : Int) - 1)) false
          (.reg s1.r) (s1.r + 1)
        rw [hc] at m4 h
        simp only at m4 h
        rcases hb2 : bindCode (.why (D.gruende f)) ov r4 with _ | ⟨cb2, a2, r5⟩
        · simp only [hb2, reduceCtorEq] at h
        have m5 := bindCode_mono hb2
        simp only [hb2] at h
        rcases hb3 : lowerEnd lay (a2 :: cenv) lv err (st.l + 3) ⟨r5, s1.l⟩ with _ | ⟨be, s2⟩
        · simp only [hb3, reduceCtorEq] at h
        have S2 := IHerr a2 _ _ _ hb3
        simp only [hb3] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
        · intro b hb'
          simp only [List.mem_cons, List.mem_append] at hb'
          rcases hb' with rfl | rfl | rfl | hb' | hb'
          · rfl
          · rfl
          · rfl
          · exact S1.2.1 b hb'
          · exact S2.2.1 b hb'
        · have a1 := S1.2.2
          have a2' := S2.2.2
          simp only at m1 m2 m3 m4 m5 a1 a2' ⊢
          omega
      · simp only [reduceCtorEq] at h
  | _ => simp only [reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerS_shape_assignSlot (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (f)
    (i)
    (e)
    (zz1)
    (zz2)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.assignSlot t f i e zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ _) lb k st = some (blks, st'))
    : Shape lb st st' blks :=
  by
  simp only [lowerS] at h
  by_cases hs : supp (D.typ t f) = true
  · simp only [hs, if_true] at h
    rcases hi : lowerE lay cenv i st.r with _ | ⟨ci, oi, r1⟩
    · simp only [hi, reduceCtorEq] at h
    have m1 := lowerE_mono lay cenv i st.r _ hi
    simp only [hi] at h
    rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
    · simp only [he, reduceCtorEq] at h
    have m2 := lowerE_mono lay cenv e r1 _ he
    simp only [he] at h
    rcases hsa : slotAddr lay t f (.glob (lay.gblk t)) (.int 0 (D.count t - 1)) oi r2 with
      _ | ⟨ca, oa, r3⟩
    · simp only [hsa, reduceCtorEq] at h
    have m3 := slotAddr_mono hsa
    simp only [hsa] at h
    rcases hst : storeTo (D.typ t f) oe r3 oa with _ | ⟨cs, r4⟩
    · simp only [hst, reduceCtorEq] at h
    have m4 := storeTo_mono hst
    simp only [hst] at h
    have := Option.some.inj h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    refine ⟨⟨_, _, rfl, rfl⟩, by simp only [List.append_assoc, List.mem_cons, List.not_mem_nil, or_false, forall_eq], ?_⟩
    simp only at m1 m2 m3 ⊢
    omega
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerS_shape_assignThru (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_n}
    (p)
    (t)
    (zz1)
    (f)
    (i)
    (e)
    (zz2)
    (zz3)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t zz1 f i e zz2 zz3 : Gabbro.Grammatik.Stmt D V l Γ Λ _) lb k st = some (blks, st'))
    : Shape lb st st' blks :=
  by
  simp only [lowerS] at h
  by_cases hs : supp (D.typ t f) = true
  · simp only [hs, if_true] at h
    rcases hp : lowerE lay cenv p st.r with _ | ⟨cp, op, r1⟩
    · simp only [hp, reduceCtorEq] at h
    have m0 := lowerE_mono lay cenv p st.r _ hp
    simp only [hp] at h
    rcases hi : lowerE lay cenv i r1 with _ | ⟨ci, oi, r2⟩
    · simp only [hi, reduceCtorEq] at h
    have m1 := lowerE_mono lay cenv i r1 _ hi
    simp only [hi] at h
    rcases he : lowerE lay cenv e r2 with _ | ⟨ce, oe, r3⟩
    · simp only [he, reduceCtorEq] at h
    have m2 := lowerE_mono lay cenv e r2 _ he
    simp only [he] at h
    rcases hsa : slotAddr lay t f op (.int 0 (D.count t - 1)) oi r3 with _ | ⟨ca, oa, r4⟩
    · simp only [hsa, reduceCtorEq] at h
    have m3 := slotAddr_mono hsa
    simp only [hsa] at h
    rcases hst : storeTo (D.typ t f) oe r4 oa with _ | ⟨cs, r5⟩
    · simp only [hst, reduceCtorEq] at h
    have m4 := storeTo_mono hst
    simp only [hst] at h
    have := Option.some.inj h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    refine ⟨⟨_, _, rfl, rfl⟩, by simp only [List.append_assoc, List.mem_cons, List.not_mem_nil, or_false, forall_eq], ?_⟩
    simp only at m0 m1 m2 m3 ⊢
    omega
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerS_shape_assignGlob (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (e)
    (zz1)
    (zz2)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.assignGlob g e zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ _) lb k st = some (blks, st'))
    : Shape lb st st' blks :=
  by
  simp only [lowerS] at h
  by_cases hs : supp (D.gtyp g) = true
  · simp only [hs, if_true] at h
    rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
    · simp only [he, reduceCtorEq] at h
    have m1 := lowerE_mono lay cenv e st.r _ he
    simp only [he] at h
    rcases hst : storeTo (D.gtyp g) oe r1 (.glob (lay.ggblk g)) with _ | ⟨cs, r2⟩
    · simp only [hst, reduceCtorEq] at h
    have m2 := storeTo_mono hst
    simp only [hst] at h
    have := Option.some.inj h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    refine ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], ?_⟩
    simp only at m1 m2 ⊢
    omega
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerS_shape_GabbroGrammatikStmtassignVar (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (τ)
    (x)
    (e)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (Gabbro.Grammatik.Stmt.assignVar (τ := τ) x e : Gabbro.Grammatik.Stmt D V l Γ Λ _) lb k st = some (blks, st'))
    : Shape lb st st' blks :=
  by
  simp only [lowerS] at h
  rcases hc : cenv[varIdx x]? with _ | a
  · simp only [hc, reduceCtorEq] at h
  simp only [hc] at h
  by_cases hs : supp τ = true
  · simp only [hs, if_true] at h
    rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
    · simp only [he, reduceCtorEq] at h
    have m1 := lowerE_mono lay cenv e st.r _ he
    simp only [he] at h
    rcases hst : storeTo τ oe r1 (.reg a) with _ | ⟨cs, r2⟩
    · simp only [hst, reduceCtorEq] at h
    have m2 := storeTo_mono hst
    simp only [hst] at h
    have := Option.some.inj h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    refine ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], ?_⟩
    simp only at m1 m2 ⊢
    omega
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerS_shape_ite (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (tb)
    (eb)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.ite c tb eb : Gabbro.Grammatik.Stmt D V l Γ Λ Λ') lb k st = some (blks, st'))
    (ih_lowerB_shape_tb : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv tb lb k st = some (blks, st') → Shape lb st st' blks)
    (ih_lowerB_shape_eb : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerB lay cenv lv eb lb k st = some (blks, st') → Shape lb st st' blks)
    : Shape lb st st' blks :=
  by
  simp only [lowerS] at h
  rcases hc : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
  · simp only [hc, reduceCtorEq] at h
  have m1 := lowerE_mono lay cenv c st.r _ hc
  simp only [hc] at h
  rcases hb1 : lowerB lay cenv lv tb st.l k ⟨r1, st.l + 2⟩ with _ | ⟨bt, s1⟩
  · simp only [hb1, reduceCtorEq] at h
  have S1 := ih_lowerB_shape_tb st.l k ⟨r1, st.l + 2⟩ s1 bt hb1
  simp only [hb1] at h
  rcases hb2 : lowerB lay cenv lv eb (st.l + 1) k s1 with _ | ⟨be, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  have S2 := ih_lowerB_shape_eb (st.l + 1) k s1 s2 be hb2
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

set_option linter.unusedSectionVars false in
theorem lowerS_shape_onWhy (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (n)
    (r)
    (arms)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (h : lowerS lay cenv lv (.onWhy (n := n) r arms : Gabbro.Grammatik.Stmt D V l Γ Λ Λ') lb k st = some (blks, st'))
    (ih_lowerGA_shape_arms : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), lowerGA lay cenv lv arms lb k st = some (blks, st') → (∀ b ∈ blks, b.phis = []) ∧ st.r ≤ st'.r)
    : Shape lb st st' blks :=
  by
  simp only [lowerS] at h
  rcases hr : lowerE lay cenv r st.r with _ | ⟨cr, orr, r1⟩
  · simp only [hr, reduceCtorEq] at h
  have m1 := lowerE_mono lay cenv r st.r _ hr
  simp only [hr] at h
  split at h
  · rcases hga : lowerGA lay cenv lv arms (st.l + 1) k ⟨r1, st.l + 1 + n⟩ with _ | ⟨ba, s1⟩
    · simp only [hga, reduceCtorEq] at h
    have G := ih_lowerGA_shape_arms (st.l + 1) k ⟨r1, st.l + 1 + n⟩ s1 ba hga
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
  · simp only [reduceCtorEq] at h

end Gabbro.Code.Lower
