module
public import Grammatik.Code.Refine.Struct.Mono
public import Grammatik.Code.Refine.Struct.LblWf
@[expose] public section


/-
  File:      Grammatik/Code/Refine/Labels.lean
  Subject:   TRACK L, PHASE L1 -- THE LABELS OF A LOWERING ARE DISTINCT.

  `LblWf lb st st' blks`: the label counter did not fall, the labels of the blocks are pairwise
  distinct, and every label is the entry label `lb` or one the counter handed out (`st.l <= l <
  st'.l`). With `lb < st.l` (the entry label is not one the lowering allocates itself) this is
  what `blk_of_nodup` needs: the labels of a lowered function are distinct BY CONSTRUCTION, so
  the closing function theorem does not assume it.

  NOTE: labels are compared as `Nat` throughout (`omega` does not see through the abbreviation).
-/

namespace Gabbro.Code.Lower

open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr Args)

variable [Conf] {D : Deklaration}

theorem lowerErg_lbl (lay : Layout D) (cenv : List Reg) {Γ : Ctx} {Λ : List (Res D)} {eo : Option GTy}
    (e : ErgExpr D Γ Λ eo) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerErg lay cenv e lb st = some (blks, st')) : LblWf lb st st' blks := by
  cases e with
  | empty =>
      simp only [lowerErg, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)
  | val e =>
      simp only [lowerErg] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp only [he, reduceCtorEq] at h
      simp only [he, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lw_single rfl (Nat.le_refl _)

theorem lowerErgF_lbl (lay : Layout D) (cenv : List Reg) (n : Nat) {Γ : Ctx} {Λ : List (Res D)}
    {eo : Option GTy} (e : ErgExpr D Γ Λ eo) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerErgF lay cenv n e lb st = some (blks, st')) : LblWf lb st st' blks := by
  cases e with
  | empty =>
      simp only [lowerErgF] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact lw_single rfl (Nat.le_refl _)
      · simp only [reduceCtorEq] at h
  | @val τ e =>
      cases τ with
      | int lo hi =>
          simp only [lowerErgF] at h
          rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
          · simp only [he, reduceCtorEq] at h
          simp only [he] at h
          split at h
          · rcases hnc : numCode lo hi (retW n (some (.int lo hi))) (n + 1) 0 oe r1 with ⟨cn, on, r2⟩
            rw [hnc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact lw_single rfl (Nat.le_refl _)
          · simp only [reduceCtorEq] at h
      | _ => simp only [lowerErgF, reduceCtorEq] at h

theorem lowerRet_lbl (lay : Layout D) (cenv : List Reg) (n : Nat) {Γ : Ctx} {Λ : List (Res D)}
    {eo : Option GTy} (e : ErgExpr D Γ Λ eo) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerRet lay cenv n e lb st = some (blks, st')) : LblWf lb st st' blks := by
  unfold lowerRet at h
  by_cases hn : n = 0
  · rw [if_pos hn] at h
    exact lowerErg_lbl lay cenv e lb st st' blks h
  · rw [if_neg hn] at h
    exact lowerErgF_lbl lay cenv n e lb st st' blks h

theorem lowerWhy_lbl (n : Nat) (eo : Option GTy) (r : Nat) (lb : Lbl) (st st' : St) (blks : List Block)
    (h : lowerWhy n eo r lb st = some (blks, st')) : LblWf lb st st' blks := by
  unfold lowerWhy at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact lw_single rfl (Nat.le_refl _)
  · simp only [reduceCtorEq] at h

variable {V : Vertrag D}

/-- A call with a failure channel: its blocks' labels are distinct, given the continuations'. -/
theorem bindCallElse_lbl (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : GTy} (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
    (hp : Gabbro.Grammatik.RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
    (err : Gabbro.Grammatik.Endblock D V l (.why (D.gruende f) :: Γ) (Gabbro.Grammatik.nach D f Λ))
    (rest : Gabbro.Grammatik.Block D V l (τ :: Γ) (Gabbro.Grammatik.nach D f Λ) Λ') (lb k : Lbl)
    (st st' : St) (blks : List Block) (hlt : (lb : Nat) < st.l)
    (IHrest : ∀ a st1 s1 bo, (st.l + 2 : Nat) < st1.l →
      lowerB lay (a :: cenv) lv rest (st.l + 2) k st1 = some (bo, s1) → LblWf (st.l + 2) st1 s1 bo)
    (IHerr : ∀ a st1 s2 be, (st.l + 3 : Nat) < st1.l →
      lowerEnd lay (a :: cenv) lv err (st.l + 3) st1 = some (be, s2) → LblWf (st.l + 3) st1 s2 be)
    (h : lowerB lay cenv lv (Gabbro.Grammatik.Block.bindCallElse f args he hp hr err rest) lb k st
      = some (blks, st')) : LblWf lb st st' blks := by
  unfold lowerB at h
  rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
  · simp only [hla, reduceCtorEq] at h
  simp only [hla] at h
  unfold lowerElse at h
  cases τ with
  | int lo hi =>
      simp only at h
      split at h
      · rcases hp' : payCode (failTop (D.gruende f) (some (.int lo hi))) (retW (D.gruende f) (some (.int lo hi)))
            (D.gruende f + 1) lo hi (.reg r1) (r1 + 2) with _ | ⟨cp, op, r2⟩
        · simp only [hp', reduceCtorEq] at h
        simp only [hp'] at h
        rcases hb : bindCode (.int lo hi) op r2 with _ | ⟨cb, a, r3⟩
        · simp only [hb, reduceCtorEq] at h
        simp only [hb] at h
        rcases hb1 : lowerB lay (a :: cenv) lv rest (st.l + 2) k ⟨r3, st.l + 4⟩ with _ | ⟨bo, s1⟩
        · simp only [hb1, reduceCtorEq] at h
        have W1 := IHrest a _ _ _ (by show (st.l + 2 : Nat) < st.l + 4; omega) hb1
        simp only [hb1] at h
        rcases hc : cvt (retW (D.gruende f) (some (.int lo hi))) (Ar.wid 0 ((D.gruende f : Int) - 1)) false
            (.reg s1.r) (s1.r + 1) with ⟨cv, ov, r4⟩
        rw [hc] at h
        simp only at h
        rcases hb2 : bindCode (.why (D.gruende f)) ov r4 with _ | ⟨cb2, a2, r5⟩
        · simp only [hb2, reduceCtorEq] at h
        simp only [hb2] at h
        have m1' : st.l + 4 ≤ s1.l := W1.1
        rcases hb3 : lowerEnd lay (a2 :: cenv) lv err (st.l + 3) ⟨r5, s1.l⟩ with _ | ⟨be, s2⟩
        · simp only [hb3, reduceCtorEq] at h
        have W2 := IHerr a2 _ _ _ (by show (st.l + 3 : Nat) < s1.l; omega) hb3
        simp only [hb3, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact lw_else (b0 := ⟨lb, [], ca ++ [.call (some r1) (lay.fno f) ops,
              .bin (r1 + 1) .urem (retW (D.gruende f) (some (.int lo hi))) (.reg r1)
                (.int (retW (D.gruende f) (some (.int lo hi))) ((D.gruende f + 1 : Nat) : Int))],
            .brc .eq (retW (D.gruende f) (some (.int lo hi))) (.reg (r1 + 1))
              (.int (retW (D.gruende f) (some (.int lo hi))) 0) st.l (st.l + 1)⟩)
          (bA := ⟨st.l, [], cp ++ cb, .jmp (st.l + 2)⟩)
          (bB := ⟨st.l + 1, [], .bin s1.r .sub (retW (D.gruende f) (some (.int lo hi))) (.reg (r1 + 1))
            (.int (retW (D.gruende f) (some (.int lo hi))) 1) :: (cv ++ cb2), .jmp (st.l + 3)⟩)
          rfl rfl rfl hlt m1' W2.1 ⟨W1.2.1, W1.2.2⟩ ⟨W2.2.1, W2.2.2⟩
      · simp only [reduceCtorEq] at h
  | _ => simp only [reduceCtorEq] at h

set_option linter.unusedSectionVars false in
theorem lowerS_lbl_assignSlot (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
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
    (hlt : (lb : Nat) < st.l)
    (h : lowerS lay cenv lv (.assignSlot t f i e zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ _) lb k st = some (blks, st'))
    : LblWf lb st st' blks :=
  by
  simp only [lowerS] at h
  repeat (split at h <;> try (simp only [reduceCtorEq] at h; done))
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact lw_single rfl (Nat.le_refl _)

set_option linter.unusedSectionVars false in
theorem lowerS_lbl_assignThru (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
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
    (hlt : (lb : Nat) < st.l)
    (h : lowerS lay cenv lv (.assignThru (n := zi_n) (read := zi_read) (space := zi_space) p t zz1 f i e zz2 zz3 : Gabbro.Grammatik.Stmt D V l Γ Λ _) lb k st = some (blks, st'))
    : LblWf lb st st' blks :=
  by
  simp only [lowerS] at h
  repeat (split at h <;> try (simp only [reduceCtorEq] at h; done))
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact lw_single rfl (Nat.le_refl _)

set_option linter.unusedSectionVars false in
theorem lowerS_lbl_assignGlob (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
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
    (hlt : (lb : Nat) < st.l)
    (h : lowerS lay cenv lv (.assignGlob g e zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ _) lb k st = some (blks, st'))
    : LblWf lb st st' blks :=
  by
  simp only [lowerS] at h
  repeat (split at h <;> try (simp only [reduceCtorEq] at h; done))
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact lw_single rfl (Nat.le_refl _)

set_option linter.unusedSectionVars false in
theorem lowerS_lbl_GabbroGrammatikStmtassignVar (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
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
    (hlt : (lb : Nat) < st.l)
    (h : lowerS lay cenv lv (Gabbro.Grammatik.Stmt.assignVar (τ := τ) x e : Gabbro.Grammatik.Stmt D V l Γ Λ _) lb k st = some (blks, st'))
    : LblWf lb st st' blks :=
  by
  simp only [lowerS] at h
  repeat (split at h <;> try (simp only [reduceCtorEq] at h; done))
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact lw_single rfl (Nat.le_refl _)

set_option linter.unusedSectionVars false in
theorem lowerS_lbl_ite (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
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
    (hlt : (lb : Nat) < st.l)
    (h : lowerS lay cenv lv (.ite c tb eb : Gabbro.Grammatik.Stmt D V l Γ Λ Λ') lb k st = some (blks, st'))
    (ih_lowerB_lbl_tb : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), (lb : Nat) < st.l → lowerB lay cenv lv tb lb k st = some (blks, st') → LblWf lb st st' blks)
    (ih_lowerB_lbl_eb : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), (lb : Nat) < st.l → lowerB lay cenv lv eb lb k st = some (blks, st') → LblWf lb st st' blks)
    : LblWf lb st st' blks :=
  by
  simp only [lowerS] at h
  rcases hc : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
  · simp only [hc, reduceCtorEq] at h
  simp only [hc] at h
  rcases hb1 : lowerB lay cenv lv tb st.l k ⟨r1, st.l + 2⟩ with _ | ⟨bt, s1⟩
  · simp only [hb1, reduceCtorEq] at h
  simp only [hb1] at h
  rcases hb2 : lowerB lay cenv lv eb (st.l + 1) k s1 with _ | ⟨be, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  simp only [hb2, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨m1, n1, a1⟩ := ih_lowerB_lbl_tb st.l k ⟨r1, st.l + 2⟩ s1 bt
    (by show (st.l : Nat) < st.l + 2; omega) hb1
  have m1' : st.l + 2 ≤ s1.l := m1
  obtain ⟨m2, n2, a2⟩ := ih_lowerB_lbl_eb (st.l + 1) k s1 s2 be
    (by show (st.l + 1 : Nat) < s1.l; omega) hb2
  exact lw_two (b := ⟨lb, [], cc, .br oc st.l (st.l + 1)⟩) rfl hlt m1' m2 ⟨n1, a1⟩ ⟨n2, a2⟩

set_option linter.unusedSectionVars false in
theorem lowerS_lbl_call (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (f)
    (args)
    (zz1)
    (zz2)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (hlt : (lb : Nat) < st.l)
    (h : lowerS lay cenv lv (.call f args zz1 zz2 : Gabbro.Grammatik.Stmt D V l Γ Λ _) lb k st = some (blks, st'))
    : LblWf lb st st' blks :=
  by
  simp only [lowerS] at h
  rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
  · simp only [hla, reduceCtorEq] at h
  simp only [hla, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact lw_single rfl (Nat.le_refl _)

set_option linter.unusedSectionVars false in
theorem lowerB_lbl_nil (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (hlt : (lb : Nat) < st.l)
    (h : lowerB lay cenv lv (.nil : Gabbro.Grammatik.Block D V l Γ Λ _) lb k st = some (blks, st'))
    : LblWf lb st st' blks :=
  by
  simp only [lowerB, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact lw_single rfl (Nat.le_refl _)

set_option linter.unusedSectionVars false in
theorem lowerB_lbl_cons (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
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
    (hlt : (lb : Nat) < st.l)
    (h : lowerB lay cenv lv (.cons (Λ' := zi_Λ') s rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
    (ih_lowerS_lbl_s : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), (lb : Nat) < st.l → lowerS lay cenv lv s lb k st = some (blks, st') → LblWf lb st st' blks)
    (ih_lowerB_lbl_rest : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), (lb : Nat) < st.l → lowerB lay cenv lv rest lb k st = some (blks, st') → LblWf lb st st' blks)
    : LblWf lb st st' blks :=
  by
  simp only [lowerB] at h
  rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
  · simp only [hs, reduceCtorEq] at h
  simp only [hs] at h
  rcases hr : lowerB lay cenv lv rest st.l k s1 with _ | ⟨b2, s2⟩
  · simp only [hr, reduceCtorEq] at h
  simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨m1, n1, a1⟩ := ih_lowerS_lbl_s lb st.l ⟨st.r, st.l + 1⟩ s1 b1
    (Nat.lt_succ_of_lt hlt) hs
  have m1' : st.l + 1 ≤ s1.l := m1
  obtain ⟨m2, n2, a2⟩ := ih_lowerB_lbl_rest st.l k s1 s2 b2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) m1') hr
  exact lw_seq hlt m1' m2 ⟨n1, a1⟩ ⟨n2, a2⟩

set_option linter.unusedSectionVars false in
theorem lowerB_lbl_check (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (sonst)
    (rest)
    (lb : Lbl)
    (k : Lbl)
    (st : St)
    (st' : St)
    (blks : List Block)
    (hlt : (lb : Nat) < st.l)
    (h : lowerB lay cenv lv (.check c sonst rest : Gabbro.Grammatik.Block D V l Γ Λ Λ') lb k st = some (blks, st'))
    (ih_lowerB_lbl_rest : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), (lb : Nat) < st.l → lowerB lay cenv lv rest lb k st = some (blks, st') → LblWf lb st st' blks)
    (ih_lowerEnd_lbl_sonst : ∀ (lb : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), (lb : Nat) < st.l → lowerEnd lay cenv lv sonst lb st = some (blks, st') → LblWf lb st st' blks)
    : LblWf lb st st' blks :=
  by
  simp only [lowerB] at h
  rcases hc : lowerE lay cenv c st.r with _ | ⟨cc, oc, r1⟩
  · simp only [hc, reduceCtorEq] at h
  simp only [hc] at h
  rcases hb1 : lowerEnd lay cenv lv sonst st.l ⟨r1, st.l + 2⟩ with _ | ⟨be, s1⟩
  · simp only [hb1, reduceCtorEq] at h
  simp only [hb1] at h
  rcases hb2 : lowerB lay cenv lv rest (st.l + 1) k s1 with _ | ⟨br, s2⟩
  · simp only [hb2, reduceCtorEq] at h
  simp only [hb2, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨m1, n1, a1⟩ := ih_lowerEnd_lbl_sonst st.l ⟨r1, st.l + 2⟩ s1 be
    (by show (st.l : Nat) < st.l + 2; omega) hb1
  have m1' : st.l + 2 ≤ s1.l := m1
  obtain ⟨m2, n2, a2⟩ := ih_lowerB_lbl_rest (st.l + 1) k s1 s2 br
    (by show (st.l + 1 : Nat) < s1.l; omega) hb2
  exact lw_two (b := ⟨lb, [], cc, .br oc (st.l + 1) st.l⟩) rfl hlt m1' m2 ⟨n1, a1⟩ ⟨n2, a2⟩

set_option linter.unusedSectionVars false in
theorem lowerEnd_lbl_cons (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl)
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
    (hlt : (lb : Nat) < st.l)
    (h : lowerEnd lay cenv lv (.cons (Λ' := zi_Λ') s rest : Gabbro.Grammatik.Endblock D V l Γ Λ) lb st = some (blks, st'))
    (ih_lowerS_lbl_s : ∀ (lb : Lbl), ∀ (k : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), (lb : Nat) < st.l → lowerS lay cenv lv s lb k st = some (blks, st') → LblWf lb st st' blks)
    (ih_lowerEnd_lbl_rest : ∀ (lb : Lbl), ∀ (st : St), ∀ (st' : St), ∀ (blks : List Block), (lb : Nat) < st.l → lowerEnd lay cenv lv rest lb st = some (blks, st') → LblWf lb st st' blks)
    : LblWf lb st st' blks :=
  by
  simp only [lowerEnd] at h
  rcases hs : lowerS lay cenv lv s lb st.l ⟨st.r, st.l + 1⟩ with _ | ⟨b1, s1⟩
  · simp only [hs, reduceCtorEq] at h
  simp only [hs] at h
  rcases hr : lowerEnd lay cenv lv rest st.l s1 with _ | ⟨b2, s2⟩
  · simp only [hr, reduceCtorEq] at h
  simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨m1, n1, a1⟩ := ih_lowerS_lbl_s lb st.l ⟨st.r, st.l + 1⟩ s1 b1
    (Nat.lt_succ_of_lt hlt) hs
  have m1' : st.l + 1 ≤ s1.l := m1
  obtain ⟨m2, n2, a2⟩ := ih_lowerEnd_lbl_rest st.l s1 s2 b2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) m1') hr
  exact lw_seq hlt m1' m2 ⟨n1, a1⟩ ⟨n2, a2⟩

end Gabbro.Code.Lower
