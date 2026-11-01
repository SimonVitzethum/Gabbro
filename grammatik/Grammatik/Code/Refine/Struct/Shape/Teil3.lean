module

public import Grammatik.Code.Refine.Struct.Mono
public import Grammatik.Code.Refine.Struct.Shape.Teil2

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration Expr Ctx Var Res Vertrag ErgExpr Args)
variable {D : Deklaration}
variable {V : Vertrag D}

mutual

theorem lowerS_shape (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Gabbro.Grammatik.Stmt D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerS lay cenv lv s lb k st = some (blks, st') → Shape lb st st' blks
  | _, _, _, _, .assignSlot t f i e zz1 zz2, lb, k, st, st', blks, h =>
      lowerS_shape_assignSlot (lay := lay) (cenv := cenv) (lv := lv) (t := t) (f := f) (i := i) (e := e) (zz1 := zz1) (zz2 := zz2) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h)
  | _, _, _, _, .assignThru p t zz1 f i e zz2 zz3, lb, k, st, st', blks, h =>
      lowerS_shape_assignThru (lay := lay) (cenv := cenv) (lv := lv) (p := p) (t := t) (zz1 := zz1) (f := f) (i := i) (e := e) (zz2 := zz2) (zz3 := zz3) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h)
  | _, _, _, _, .assignGlob g e zz1 zz2, lb, k, st, st', blks, h =>
      lowerS_shape_assignGlob (lay := lay) (cenv := cenv) (lv := lv) (g := g) (e := e) (zz1 := zz1) (zz2 := zz2) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h)
  | _, _, _, _, Gabbro.Grammatik.Stmt.assignVar (τ := τ) x e, lb, k, st, st', blks, h =>
      lowerS_shape_GabbroGrammatikStmtassignVar (lay := lay) (cenv := cenv) (lv := lv) (τ := τ) (x := x) (e := e) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h)
  | _, _, _, _, .ite c tb eb, lb, k, st, st', blks, h =>
      lowerS_shape_ite (lay := lay) (cenv := cenv) (lv := lv) (c := c) (tb := tb) (eb := eb) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (ih_lowerB_shape_tb := lowerB_shape lay cenv lv tb) (ih_lowerB_shape_eb := lowerB_shape lay cenv lv eb)
  | _, _, _, _, .ret e _, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      exact lowerRet_shape lay cenv V.gruende e lb st st' blks h
  | _, _, _, _, .putBytes .., lb, k, st, st', blks, h => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .shift .., lb, k, st, st', blks, h => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .onOption (n := n) o p a, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      rcases ho : lowerE lay cenv o st.r with _ | ⟨co, oo, r1⟩
      · simp only [ho, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv o st.r _ ho
      simp only [ho] at h
      split at h
      · rcases hv : cvtG (.int (-1) (n - 1)) (.int 0 (n - 1)) oo r1 with _ | ⟨cv, ov, r2⟩
        · simp only [Int.reduceNeg, hv, reduceCtorEq] at h
        have m2 := cvtG_mono hv
        simp only [hv] at h
        rcases hb : bindCode (.int 0 (n - 1)) ov r2 with _ | ⟨cb, c, r3⟩
        · simp only [hb, reduceCtorEq] at h
        have m3 := bindCode_mono hb
        simp only [hb] at h
        rcases hb1 : lowerB lay cenv lv a st.l k ⟨r3, st.l + 3⟩ with _ | ⟨ba, s1⟩
        · simp only [hb1, reduceCtorEq] at h
        have S1 := lowerB_shape lay cenv lv a st.l k ⟨r3, st.l + 3⟩ s1 ba hb1
        simp only [hb1] at h
        rcases hb2 : lowerB lay (c :: cenv) lv p (st.l + 2) k s1 with _ | ⟨bp, s2⟩
        · simp only [hb2, reduceCtorEq] at h
        have S2 := lowerB_shape lay (c :: cenv) lv p (st.l + 2) k s1 s2 bp hb2
        simp only [hb2] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons, List.mem_append] at hb
          rcases hb with rfl | rfl | hb | hb
          · rfl
          · rfl
          · exact S1.2.1 b hb
          · exact S2.2.1 b hb
        · have a1 := S1.2.2
          have a2 := S2.2.2
          simp only at m1 m2 m3 a1 a2 ⊢
          omega
      · simp only [reduceCtorEq] at h
  | _, _, _, _, .onTag (cs := cs) v arms, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      rcases hv : lowerE lay cenv v st.r with _ | ⟨cv, ov, r1⟩
      · simp only [hv, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv v st.r _ hv
      simp only [hv] at h
      split at h
      · rcases hga : lowerAr lay cenv lv (sumTop cs) (Ar.wid 0 (sumTop cs)) cs.length ov arms (st.l + 1) k
            ⟨r1 + 1, st.l + 1 + cs.length⟩ with _ | ⟨ba, s1⟩
        · simp only [hga, reduceCtorEq] at h
        have G := lowerAr_shape lay cenv lv (sumTop cs) (Ar.wid 0 (sumTop cs)) cs.length ov arms
          (st.l + 1) k ⟨r1 + 1, st.l + 1 + cs.length⟩ s1 ba hga
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
  | _, _, _, _, .onWhy (n := n) r arms, lb, k, st, st', blks, h =>
      lowerS_shape_onWhy (lay := lay) (cenv := cenv) (lv := lv) (n := n) (r := r) (arms := arms) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (ih_lowerGA_shape_arms := lowerGA_shape lay cenv lv arms)
  | _, _, _, _, .call f args zz1 zz2, lb, k, st, st', blks, h =>
      lowerS_shape_call (lay := lay) (cenv := cenv) (lv := lv) (f := f) (args := args) (zz1 := zz1) (zz2 := zz2) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h)
  | _, _, _, _, .callInd .., lb, k, st, st', blks, h => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .locks .., lb, k, st, st', blks, h => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .breaking .., lb, k, st, st', blks, h => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .traverse t _ body, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      by_cases hc : 0 ≤ D.count t ∧ Ar.Fits 0 (D.count t) 128
      · simp only [hc, and_self, if_true] at h
        rcases hv : cvtG (.int 0 (D.count t)) (.int 0 (D.count t - 1)) (.reg st.r) (st.r + 1) with
          _ | ⟨cv, ov, r1⟩
        · simp only [hv, reduceCtorEq] at h
        have m1 := cvtG_mono hv
        simp only [hv] at h
        rcases hb : bindCode (.int 0 (D.count t - 1)) ov r1 with _ | ⟨cb, a, r2⟩
        · simp only [hb, reduceCtorEq] at h
        have m2 := bindCode_mono hb
        simp only [hb] at h
        rcases hb2 : lowerB lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) ⟨r2, st.l + 4⟩ with
          _ | ⟨bb, s1⟩
        · simp only [hb2, reduceCtorEq] at h
        have S2 := lowerB_shape lay (a :: cenv) (k, st.l + 2) body (st.l + 3) (st.l + 2) ⟨r2, st.l + 4⟩ s1 bb hb2
        simp only [hb2] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | rfl | rfl | rfl | hb
          · rfl
          · rfl
          · rfl
          · rfl
          · exact S2.2.1 b hb
        · have a2 := S2.2.2
          simp only at m1 m2 a2 ⊢
          omega
      · simp only [hc, ↓reduceIte, reduceCtorEq] at h
  | _, _, _, _, .retry n bis body ueb, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      by_cases hc : retryOk n = true
      · simp only [hc, if_true] at h
        rcases hcb : lowerE lay cenv bis (st.r + 1) with _ | ⟨cb, ob, r1⟩
        · simp only [hcb, reduceCtorEq] at h
        have m1 := lowerE_mono lay cenv bis (st.r + 1) _ hcb
        simp only [hcb] at h
        rcases hb1 : lowerB lay cenv (k, st.l + 3) body (st.l + 4) (st.l + 3) ⟨r1, st.l + 5⟩ with _ | ⟨bb, s1⟩
        · simp only [hb1, reduceCtorEq] at h
        have S1 := lowerB_shape lay cenv (k, st.l + 3) body (st.l + 4) (st.l + 3) ⟨r1, st.l + 5⟩ s1 bb hb1
        simp only [hb1] at h
        rcases hb2 : lowerB lay cenv lv ueb (st.l + 2) k s1 with _ | ⟨bo, s2⟩
        · simp only [hb2, reduceCtorEq] at h
        have S2 := lowerB_shape lay cenv lv ueb (st.l + 2) k s1 s2 bo hb2
        simp only [hb2] at h
        have := Option.some.inj h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
        · intro b hb
          simp only [List.mem_cons, List.mem_append] at hb
          rcases hb with rfl | rfl | rfl | rfl | hb | hb
          · rfl
          · rfl
          · rfl
          · rfl
          · exact S1.2.1 b hb
          · exact S2.2.1 b hb
        · have a1 := S1.2.2
          have a2 := S2.2.2
          simp only at m1 a1 a2 ⊢
          omega
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  | _, _, _, _, .forever _ _ body, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      exact lowerB_shape lay cenv (k, lb) body lb lb st st' blks h
  | _, _, _, _, .axiomCall .., lb, k, st, st', blks, h => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .regWrite .., lb, k, st, st', blks, h => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .transition .., lb, k, st, st', blks, h => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .publish .., lb, k, st, st', blks, h => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .advances .., lb, k, st, st', blks, h => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .retires .., lb, k, st, st', blks, h => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .retWhy r _, lb, k, st, st', blks, h => by
      simp only [lowerS] at h
      exact lowerWhy_shape V.gruende V.erg r.val lb st st' blks h
  | _, _, _, _, .leave .., lb, k, st, st', blks, h => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], Nat.le_refl _⟩
  | _, _, _, _, .next .., lb, k, st, st', blks, h => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], Nat.le_refl _⟩

theorem lowerB_shape (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Gabbro.Grammatik.Block D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerB lay cenv lv b lb k st = some (blks, st') → Shape lb st st' blks
  | _, _, _, _, .nil, lb, k, st, st', blks, h =>
      lowerB_shape_nil (lay := lay) (cenv := cenv) (lv := lv) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h)
  | _, _, _, _, .cons s rest, lb, k, st, st', blks, h =>
      lowerB_shape_cons (lay := lay) (cenv := cenv) (lv := lv) (s := s) (rest := rest) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (ih_lowerS_shape_s := lowerS_shape lay cenv lv s) (ih_lowerB_shape_rest := lowerB_shape lay cenv lv rest)
  | _, _, _, _, Gabbro.Grammatik.Block.bind (τ := τ) e rest, lb, k, st, st', blks, h => by
      simp only [lowerB] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp only [he, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv e st.r _ he
      simp only [he] at h
      rcases hb : bindCode τ oe r1 with _ | ⟨cb, a, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := bindCode_mono hb
      simp only [hb] at h
      rcases hr : lowerB lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp only [hr, reduceCtorEq] at h
      have S2 := lowerB_shape lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ s2 b2 hr
      simp only [hr] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · rfl
        · exact S2.2.1 b hb
      · have a2 := S2.2.2
        simp only at m1 m2 a2 ⊢
        omega
  | _, _, _, _, .check c sonst rest, lb, k, st, st', blks, h =>
      lowerB_shape_check (lay := lay) (cenv := cenv) (lv := lv) (c := c) (sonst := sonst) (rest := rest) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (ih_lowerB_shape_rest := lowerB_shape lay cenv lv rest) (ih_lowerEnd_shape_sonst := lowerEnd_shape lay cenv lv sonst)
  | _, _, _, _, Gabbro.Grammatik.Block.bindCall (τ := τ) f args _ _ _ rest, lb, k, st, st', blks, h => by
      simp only [lowerB] at h
      rcases hla : lowerArgs lay cenv args st.r with _ | ⟨ca, ops, r1⟩
      · simp only [hla, reduceCtorEq] at h
      have m1 := lowerArgs_mono lay cenv args st.r _ hla
      simp only [hla] at h
      rcases hb : bindCode τ (.reg r1) (r1 + 1) with _ | ⟨cb, a, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := bindCode_mono hb
      simp only [hb] at h
      rcases hr : lowerB lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp only [hr, reduceCtorEq] at h
      have S2 := lowerB_shape lay (a :: cenv) lv rest st.l k ⟨r2, st.l + 1⟩ s2 b2 hr
      simp only [hr] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · rfl
        · exact S2.2.1 b hb
      · have a2 := S2.2.2
        simp only at m1 m2 a2 ⊢
        omega
  | _, _, _, _, .bindCallInd .., lb, k, st, st', blks, h => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, Gabbro.Grammatik.Block.bindCallElse f args he hp hr err rest, lb, k, st, st', blks, h =>
      bindCallElse_shape lay cenv lv f args he hp hr err rest lb k st st' blks
        (fun a st1 s1 bo hk => lowerB_shape lay (a :: cenv) lv rest (st.l + 2) k st1 s1 bo hk)
        (fun a st1 s2 be hk => lowerEnd_shape lay (a :: cenv) lv err (st.l + 3) st1 s2 be hk) h
  | _, _, _, _, .bindAxiom .., lb, k, st, st', blks, h => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .bindAxiomElse .., lb, k, st, st', blks, h => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .regRead .., lb, k, st, st', blks, h => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .regReadElse .., lb, k, st, st', blks, h => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .awaits .., lb, k, st, st', blks, h => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .exchange .., lb, k, st, st', blks, h => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, Gabbro.Grammatik.Block.narrow (lo := lo) (hi := hi) e lo' hi' sonst rest, lb, k, st, st', blks,
      h => by
      simp only [lowerB] at h
      rcases hc : lowerE lay cenv (Expr.and (Expr.le (Expr.lit lo') e) (Expr.le e (Expr.lit hi'))) st.r with
        _ | ⟨cc, oc, r1⟩
      · simp only [hc, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv _ st.r _ hc
      simp only [hc] at h
      rcases he : lowerE lay cenv e r1 with _ | ⟨ce, oe, r2⟩
      · simp only [he, reduceCtorEq] at h
      have m2 := lowerE_mono lay cenv e r1 _ he
      simp only [he] at h
      rcases hv : cvtG (.int lo hi) (.int lo' hi') oe r2 with _ | ⟨cv, ov, r3⟩
      · simp only [hv, reduceCtorEq] at h
      have m3 := cvtG_mono hv
      simp only [hv] at h
      rcases hb : bindCode (.int lo' hi') ov r3 with _ | ⟨cb, a, r4⟩
      · simp only [hb, reduceCtorEq] at h
      have m4 := bindCode_mono hb
      simp only [hb] at h
      rcases hb1 : lowerEnd lay cenv lv sonst st.l ⟨r4, st.l + 3⟩ with _ | ⟨be, s1⟩
      · simp only [hb1, reduceCtorEq] at h
      have S1 := lowerEnd_shape lay cenv lv sonst st.l ⟨r4, st.l + 3⟩ s1 be hb1
      simp only [hb1] at h
      rcases hb2 : lowerB lay (a :: cenv) lv rest (st.l + 2) k s1 with _ | ⟨br, s2⟩
      · simp only [hb2, reduceCtorEq] at h
      have S2 := lowerB_shape lay (a :: cenv) lv rest (st.l + 2) k s1 s2 br hb2
      simp only [hb2] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons, List.mem_append] at hb
        rcases hb with rfl | rfl | hb | hb
        · rfl
        · rfl
        · exact S1.2.1 b hb
        · exact S2.2.1 b hb
      · have a1 := S1.2.2
        have a2 := S2.2.2
        simp only at m1 m2 m3 m4 a1 a2 ⊢
        omega
  | _, _, _, _, .float .., lb, k, st, st', blks, h => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .floatLit .., lb, k, st, st', blks, h => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .floatOf .., lb, k, st, st', blks, h => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .floatNarrow .., lb, k, st, st', blks, h => by
      simp only [lowerB, reduceCtorEq] at h

theorem lowerEnd_shape (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (b : Gabbro.Grammatik.Endblock D V l Γ Λ)
      (lb : Lbl) (st st' : St) (blks : List Block),
      lowerEnd lay cenv lv b lb st = some (blks, st') → Shape lb st st' blks
  | _, _, _, .ret e _, lb, st, st', blks, h => by
      simp only [lowerEnd] at h
      exact lowerRet_shape lay cenv V.gruende e lb st st' blks h
  | _, _, _, .cons s rest, lb, st, st', blks, h =>
      lowerEnd_shape_cons (lay := lay) (cenv := cenv) (lv := lv) (s := s) (rest := rest) (lb := lb) (st := st) (st' := st') (blks := blks) (h := h) (ih_lowerS_shape_s := lowerS_shape lay cenv lv s) (ih_lowerEnd_shape_rest := lowerEnd_shape lay cenv lv rest)
  | _, _, _, Gabbro.Grammatik.Endblock.bind (τ := τ) e rest, lb, st, st', blks, h => by
      simp only [lowerEnd] at h
      rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
      · simp only [he, reduceCtorEq] at h
      have m1 := lowerE_mono lay cenv e st.r _ he
      simp only [he] at h
      rcases hb : bindCode τ oe r1 with _ | ⟨cb, a, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := bindCode_mono hb
      simp only [hb] at h
      rcases hr : lowerEnd lay (a :: cenv) lv rest st.l ⟨r2, st.l + 1⟩ with _ | ⟨b2, s2⟩
      · simp only [hr, reduceCtorEq] at h
      have S2 := lowerEnd_shape lay (a :: cenv) lv rest st.l ⟨r2, st.l + 1⟩ s2 b2 hr
      simp only [hr] at h
      have := Option.some.inj h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      refine ⟨⟨_, _, rfl, rfl⟩, ?_, ?_⟩
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · rfl
        · exact S2.2.1 b hb
      · have a2 := S2.2.2
        simp only at m1 m2 a2 ⊢
        omega
  | _, _, _, .retWhy r _, lb, st, st', blks, h => by
      simp only [lowerEnd] at h
      exact lowerWhy_shape V.gruende V.erg r.val lb st st' blks h
  | _, _, _, .leave .., lb, st, st', blks, h => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], Nat.le_refl _⟩
  | _, _, _, .next .., lb, st, st', blks, h => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨_, _, rfl, rfl⟩, by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq], Nat.le_refl _⟩
  | _, _, _, .bindCall .., lb, st, st', blks, h => by
      simp only [lowerEnd, reduceCtorEq] at h
  | _, _, _, .bindAxiom .., lb, st, st', blks, h => by
      simp only [lowerEnd, reduceCtorEq] at h
  | _, _, _, .bindAxiomElse .., lb, st, st', blks, h => by
      simp only [lowerEnd, reduceCtorEq] at h

  | _, _, _, .regRead .., lb, st, st', blks, h => by
      simp only [lowerEnd, reduceCtorEq] at h

  | _, _, _, .regReadElse .., lb, st, st', blks, h => by
      simp only [lowerEnd, reduceCtorEq] at h

  | _, _, _, .awaits .., lb, st, st', blks, h => by
      simp only [lowerEnd, reduceCtorEq] at h

  | _, _, _, .bindCallInd .., lb, st, st', blks, h => by
      simp only [lowerEnd, reduceCtorEq] at h

/-- The arms of a `match` on a tagged value: no phis, the register counter does not fall. -/
theorem lowerAr_shape (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (top : Int) (W L : Nat)
    (ov : Opd) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
      (arms : Gabbro.Grammatik.Arms D V l Γ Λ Λ' cs) (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerAr lay cenv lv top W L ov arms lb k st = some (blks, st') →
      (∀ b ∈ blks, b.phis = []) ∧ st.r ≤ st'.r
  | _, _, _, _, _, .nil, lb, k, st, st', blks, h =>
      lowerAr_shape_nil (lay := lay) (cenv := cenv) (lv := lv) (top := top) (W := W) (L := L) (ov := ov) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h)
  | _, _, _, _, _, .cons (c := none) b rest, lb, k, st, st', blks, h => by
      simp only [lowerAr] at h
      rcases hb : lowerB lay cenv lv b lb k st with _ | ⟨b1, s1⟩
      · simp only [hb, reduceCtorEq] at h
      have S1 := lowerB_shape lay cenv lv b lb k st s1 b1 hb
      simp only [hb] at h
      rcases hr : lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp only [hr, reduceCtorEq] at h
      have S2 := lowerAr_shape lay cenv lv top W L ov rest (lb + 1) k s1 s2 b2 hr
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact S1.2.1 x hx
        · exact S2.1 x hx
      · have a1 := S1.2.2
        have a2 := S2.2
        omega
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, lb, k, st, st', blks, h => by
      simp only [lowerAr] at h
      rcases hp : payCode top W L lo hi ov st.r with _ | ⟨cp, op, r1⟩
      · simp only [hp, reduceCtorEq] at h
      have m1 := payCode_mono hp
      simp only [hp] at h
      rcases hb : bindCode (.int lo hi) op r1 with _ | ⟨cb, a, r2⟩
      · simp only [hb, reduceCtorEq] at h
      have m2 := bindCode_mono hb
      simp only [hb] at h
      rcases hb1 : lowerB lay (a :: cenv) lv b st.l k ⟨r2, st.l + 1⟩ with _ | ⟨bb, s1⟩
      · simp only [hb1, reduceCtorEq] at h
      have S1 := lowerB_shape lay (a :: cenv) lv b st.l k ⟨r2, st.l + 1⟩ s1 bb hb1
      simp only [hb1] at h
      rcases hr : lowerAr lay cenv lv top W L ov rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp only [hr, reduceCtorEq] at h
      have S2 := lowerAr_shape lay cenv lv top W L ov rest (lb + 1) k s1 s2 b2 hr
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · rfl
          · exact S1.2.1 x hx
        · exact S2.1 x hx
      · have a1 := S1.2.2
        have a2 := S2.2
        simp only at m1 m2 a1 a2 ⊢
        omega

/-- The arms of a `match` on a reason: no phis, the register counter does not fall. -/
theorem lowerGA_shape (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (arms : Gabbro.Grammatik.GrundArms D V l Γ Λ Λ' n) (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerGA lay cenv lv arms lb k st = some (blks, st') →
      (∀ b ∈ blks, b.phis = []) ∧ st.r ≤ st'.r
  | _, _, _, _, _, .nil, lb, k, st, st', blks, h =>
      lowerGA_shape_nil (lay := lay) (cenv := cenv) (lv := lv) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h)
  | _, _, _, _, _, .cons b rest, lb, k, st, st', blks, h => by
      simp only [lowerGA] at h
      rcases hb : lowerB lay cenv lv b lb k st with _ | ⟨b1, s1⟩
      · simp only [hb, reduceCtorEq] at h
      have S1 := lowerB_shape lay cenv lv b lb k st s1 b1 hb
      simp only [hb] at h
      rcases hr : lowerGA lay cenv lv rest (lb + 1) k s1 with _ | ⟨b2, s2⟩
      · simp only [hr, reduceCtorEq] at h
      have S2 := lowerGA_shape lay cenv lv rest (lb + 1) k s1 s2 b2 hr
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact S1.2.1 x hx
        · exact S2.1 x hx
      · have a1 := S1.2.2
        have a2 := S2.2
        omega

end

end Gabbro.Code.Lower
