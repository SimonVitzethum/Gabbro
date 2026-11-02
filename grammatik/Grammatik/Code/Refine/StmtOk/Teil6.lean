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
public import Grammatik.Code.Refine.StmtOk.Teil5
public import Grammatik.Code.Refine.StmtOk.Teil7
public import Grammatik.Code.Refine.StmtOk.Teil8

@[expose] public section

namespace Gabbro.Code.Lower
variable [Conf]
open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl alleIndizes evalArgs ergWert)
variable {D : Deklaration} {V : Vertrag D}

set_option maxHeartbeats 1000000 in
mutual

theorem lowerS_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Gabbro.Grammatik.Stmt D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerS lay cenv lv s lb k st = some (blks, st') →
      ∀ (M : Modl) (S : Sees) (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
        Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) →
        OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execStmt O passes R s σ ρ)
  | _, _, _, _, .assignSlotRef .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .assignGlob (Λ := Λ) g e zz1 zz2, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_assignGlob (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (g := g) (e := e) (zz1 := zz1) (zz2 := zz2) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, _, .ret (Λ := Λ) e zz1, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_ret (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (e := e) (zz1 := zz1) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, _, .leave .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW,
      hc => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execStmt, OutOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.1
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, ⟨hR, hE, hW, hc⟩, fr_regs (fun _ _ => rfl)⟩
  | _, _, _, _, .next .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW,
      hc => by
      simp only [lowerS, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execStmt, OutOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.2
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, ⟨hR, hE, hW, hc⟩, fr_regs (fun _ _ => rfl)⟩
  | _, _, _, _, .assignSlot (Λ := Λ) t f i e zz1 zz2, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_assignSlot (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (t := t) (f := f) (i := i) (e := e) (zz1 := zz1) (zz2 := zz2) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, _, .assignThru (Λ := Λ) p t ht f i e zz1 zz2, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_assignThru (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (p := p) (t := t) (ht := ht) (f := f) (i := i) (e := e) (zz1 := zz1) (zz2 := zz2) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, _, Gabbro.Grammatik.Stmt.assignVar (τ := τ) (Λ := Λ) x e, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_GabbroGrammatikStmtassignVar (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (τ := τ) (Λ := Λ) (x := x) (e := e) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, _, .ite (Λ := Λ) c tb eb, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_ite (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (c := c) (tb := tb) (eb := eb) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_tb := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R tb) (ih_lowerB_ok_eb := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R eb)
  | _, _, _, _, .putBytes .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .shift .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .onOption o p a, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_onOption (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (o := o) (p := p) (a := a) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_p := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R p) (ih_lowerB_ok_a := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R a)
  | _, _, _, _, .onTag v arms, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      onTag_ok lay hL cenv lv O passes R v arms (lowerAr_ok lay hL cenv lv O passes R arms) lb k st st' blks h M S fn
        hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc
  | _, _, _, _, .onWhy r arms, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      onWhy_ok lay hL cenv lv O passes R r arms (lowerGA_ok lay hL cenv lv O passes R arms) lb k st st' blks h M S fn
        hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc
  | _, _, _, _, .call (Λ := Λ) f args zz1 hr, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_call (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (f := f) (args := args) (zz1 := zz1) (hr := hr) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, _, .callInd .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .callIndElse .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .locks .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .breaking .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .traverse (Λ := Λ) t inv body, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_traverse (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (t := t) (inv := inv) (body := body) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_body := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R body)
  | _, _, _, _, .consumeTraverse (Λ := Λ) t member edge inv bound mass body, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      exact lowerS_ok_consumeTraverse (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_body := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R body)
  | _, _, _, _, .retry (Λ := Λ) n bis body ueb, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_retry (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (n := n) (bis := bis) (body := body) (ueb := ueb) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_body := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R body) (ih_lowerB_ok_ueb := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R ueb)
  | _, _, _, _, .forever (Λ := Λ) a inv body, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_forever (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (a := a) (inv := inv) (body := body) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_body := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R body)
  | _, _, _, _, .axiomCall .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .regWrite .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .transition .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .publish .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .advances .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .retires .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerS, reduceCtorEq] at h
  | _, _, _, _, .retWhy r zz1, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerS_ok_retWhy (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (r := r) (zz1 := zz1) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, _, .retScoped (Λ := Λ) e Rr, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      exact lowerS_ok_retScoped (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (e := e) (Rr := Rr) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, _, .retWhyScoped (Λ := Λ) r Rr, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      exact lowerS_ok_retWhyScoped (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (r := r) (Rr := Rr) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
theorem lowerB_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Gabbro.Grammatik.Block D V l Γ Λ Λ')
      (lb k : Lbl) (st st' : St) (blks : List Block),
      lowerB lay cenv lv b lb k st = some (blks, st') →
      ∀ (M : Modl) (S : Sees) (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M → CallRef lay M S R →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
        Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) →
        OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R b σ ρ)
  | _, _, _, _, .nil, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerB_ok_nil (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, _, .cons s rest, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerB_ok_cons (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (s := s) (rest := rest) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerS_ok_s := fun lay hL cenv lv O passes R => lowerS_ok lay hL cenv lv O passes R s) (ih_lowerB_ok_rest := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R rest)
  | _, _, _, _, Gabbro.Grammatik.Block.bind (τ := τ) (Λ := Λ) e rest, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerB_ok_GabbroGrammatikBlockbind (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (τ := τ) (Λ := Λ) (e := e) (rest := rest) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_rest := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R rest)
  | _, _, _, _, .check (Λ := Λ) c sonst rest, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerB_ok_check (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (c := c) (sonst := sonst) (rest := rest) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_rest := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R rest) (ih_lowerEnd_ok_sonst := fun lay hL cenv lv O passes R => lowerEnd_ok lay hL cenv lv O passes R sonst)
  | _, _, _, _, Gabbro.Grammatik.Block.bindCall (τ := τ) (Λ := Λ) f args he zz1 hr rest, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerB_ok_GabbroGrammatikBlockbindCall (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (τ := τ) (Λ := Λ) (f := f) (args := args) (he := he) (zz1 := zz1) (hr := hr) (rest := rest) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_rest := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R rest)
  | _, _, _, _, .bindCallInd .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .bindCallIndElse .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, Gabbro.Grammatik.Block.bindCallElse f args he hp hr err rest, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerB_ok_GabbroGrammatikBlockbindCallElse (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (f := f) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_rest := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R rest) (ih_lowerEnd_ok_err := fun lay hL cenv lv O passes R => lowerEnd_ok lay hL cenv lv O passes R err)
  | _, _, _, _, .bindAxiom .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .bindAxiomElse .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .regRead .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .regReadElse .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .awaits .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .exchange .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, Gabbro.Grammatik.Block.narrow (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' sonst rest, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerB_ok_GabbroGrammatikBlocknarrow (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (lo := lo) (hi := hi) (Λ := Λ) (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_rest := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R rest) (ih_lowerEnd_ok_sonst := fun lay hL cenv lv O passes R => lowerEnd_ok lay hL cenv lv O passes R sonst)
  | _, _, _, _, Gabbro.Grammatik.Block.narrowRequired (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' rest, lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      exact lowerB_ok_narrowRequired (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (lo := lo) (hi := hi) (Λ := Λ) (e := e) (lo' := lo') (hi' := hi') (rest := rest) (lb := lb) (k := k) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hk := hk) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerB_ok_rest := fun lay hL cenv lv O passes R => lowerB_ok lay hL cenv lv O passes R rest)
  | _, _, _, _, .float .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .floatLit .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .floatOf .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h
  | _, _, _, _, .floatNarrow .., lb, k, st, st', blks, h, M, S, fn, hM, hk, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerB, reduceCtorEq] at h

theorem lowerEnd_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Gabbro.Grammatik.Endblock D V l Γ Λ)
      (lb : Lbl) (st st' : St) (blks : List Block),
      lowerEnd lay cenv lv e lb st = some (blks, st') →
      ∀ (M : Modl) (S : Sees) (fn : Nat), InM M fn blks → LvOk M fn lv → FnOk lay M → CallRef lay M S R →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
        Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) →
        EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R e σ ρ)
  | _, _, _, .ret (Λ := Λ) e zz1, lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerEnd_ok_ret (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (e := e) (zz1 := zz1) (lb := lb) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, .retScoped (Λ := Λ) e Rr, lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      exact lowerEnd_ok_retScoped (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (Λ := Λ) (e := e) (Rr := Rr) (lb := lb) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, .leave .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execEnd, EndOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.1
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, ⟨hR, hE, hW, hc⟩, fr_regs (fun _ _ => rfl)⟩
  | _, _, _, .next .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execEnd, EndOk]
      have hb := hM _ (List.mem_singleton_self _)
      obtain ⟨bk, hbk, hkp⟩ := hlv.2
      exact ⟨m, rs, reach_block_jmp hb rfl hbk hkp rfl, ⟨hR, hE, hW, hc⟩, fr_regs (fun _ _ => rfl)⟩
  | _, _, _, .cons s rest, lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerEnd_ok_cons (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (s := s) (rest := rest) (lb := lb) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerS_ok_s := fun lay hL cenv lv O passes R => lowerS_ok lay hL cenv lv O passes R s) (ih_lowerEnd_ok_rest := fun lay hL cenv lv O passes R => lowerEnd_ok lay hL cenv lv O passes R rest)
  | _, _, _, Gabbro.Grammatik.Endblock.bind (τ := τ) (Λ := Λ) e rest, lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerEnd_ok_GabbroGrammatikEndblockbind (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (τ := τ) (Λ := Λ) (e := e) (rest := rest) (lb := lb) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerEnd_ok_rest := fun lay hL cenv lv O passes R => lowerEnd_ok lay hL cenv lv O passes R rest)
  | _, _, _, .retWhy r zz1, lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc =>
      lowerEnd_ok_retWhy (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (r := r) (zz1 := zz1) (lb := lb) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, .retWhyScoped (Λ := Λ) r Rr, lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      exact lowerEnd_ok_retWhyScoped (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (r := r) (Rr := Rr) (lb := lb) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc)
  | _, _, _, .bindCallElse .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h
  | _, _, _, .narrow .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h
  | _, _, _, .exchange .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h
  | _, _, _, .ite .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h
  | _, _, _, Gabbro.Grammatik.Endblock.narrowRequired (lo := lo) (hi := hi) (Λ := Λ) e lo' hi' rest, lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      exact lowerEnd_ok_narrowRequired (lay := lay) (hL := hL) (cenv := cenv) (lv := lv) (O := O) (passes := passes) (R := R) (lo := lo) (hi := hi) (Λ := Λ) (e := e) (lo' := lo') (hi' := hi') (rest := rest) (lb := lb) (st := st) (st' := st') (blks := blks) (h := h) (M := M) (S := S) (fn := fn) (hM := hM) (hlv := hlv) (hFn := hFn) (hCall := hCall) (σ := σ) (ρ := ρ) (m := m) (rs := rs) (ks := ks) (dst := dst) (hR := hR) (hE := hE) (hW := hW) (hc := hc) (ih_lowerEnd_ok_rest := fun lay hL cenv lv O passes R => lowerEnd_ok lay hL cenv lv O passes R rest)
  | _, _, _, .bindCall .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h
  | _, _, _, .bindAxiom .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h
  | _, _, _, .bindAxiomElse .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h
  | _, _, _, .bindCallIndElse .., lb, st, st', blks, hlt, h => by
      simp only [lowerEnd, reduceCtorEq] at h
  | _, _, _, .bindCallIndElse .., lb, st, st', blks, h => by
      simp only [lowerEnd, reduceCtorEq] at h

  | _, _, _, .regRead .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h

  | _, _, _, .regReadElse .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h

  | _, _, _, .awaits .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h

  | _, _, _, .bindCallInd .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h
  | _, _, _, .bindCallIndElse .., lb, st, st', blks, h, M, S, fn, hM, hlv, hFn, hCall, σ, ρ, m, rs, ks, dst, hR, hE, hW, hc => by
      simp only [lowerEnd, reduceCtorEq] at h

/-- Every arm body of a `match` on a tagged value refines (the structural companion of `lowerB_ok`). -/
theorem lowerAr_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Gabbro.Grammatik.Ty)}
      (arms : Gabbro.Grammatik.Arms D V l Γ Λ Λ' cs) (i : Fin cs.length),
      ArmBOk lay cenv lv O passes R (cs.get i) (garmT arms i)
  | _, _, _, _, _, .cons (c := none) b _, ⟨0, _⟩ =>
      fun lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc =>
        lowerB_ok lay hL cenv lv O passes R b lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst
          hR hE hW hc
  | _, _, _, _, _, .cons (c := some τ) b _, ⟨0, _⟩ =>
      fun a lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc =>
        lowerB_ok lay hL (a :: cenv) lv O passes R b lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs
          ks dst hR hE hW hc
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, hi⟩ =>
      lowerAr_ok lay hL cenv lv O passes R rest ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- Every arm of a `match` on a reason refines (the arms are subterms, so this is the structural
    companion of `lowerB_ok`). -/
theorem lowerGA_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f) :
    ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
      (arms : Gabbro.Grammatik.GrundArms D V l Γ Λ Λ' n) (i : Fin n),
      BOk lay cenv lv O passes R (garm arms i)
  | _, _, _, _, _, .cons b _, ⟨0, _⟩ =>
      fun lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst hR hE hW hc =>
        lowerB_ok lay hL cenv lv O passes R b lb k st st' blks h M S fn hM hk hlv hFn hCall σ ρ m rs ks dst
          hR hE hW hc
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, hi⟩ =>
      lowerGA_ok lay hL cenv lv O passes R rest ⟨i, Nat.lt_of_succ_lt_succ hi⟩

end

end Gabbro.Code.Lower
