/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
import Stage0.Senke.Anweisung.Faelle.Kontext

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem blockCons_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {Λmid : List (Res D)} {s : Stmt D (vertragVon D f) l Γ Λ Λmid} {rest : Block D (vertragVon D f) l Γ Λmid Λ'} :
    (∀ {pr ex}, StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex s) →
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .cons s rest) := by
  intro ihS ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs1, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  have ih := ihS (ex := exPlus ex cr.length) cs ts
    hs1 (by omega) (by omega) hW m pc σ ρ hp.left hlo hlo2 hu hk hWa hpr
  have hL : pc + BitVec.ofNat 64 (16 * cs.length) + BitVec.ofInt 64 (exPlus ex cr.length).1 =
      pc + BitVec.ofNat 64 (16 * (cs ++ cr).length) + BitVec.ofInt 64 ex.1 := by
    simp only [exPlus, List.length_append]; exact tgt_eq (by omega)
  have hN : pc + BitVec.ofNat 64 (16 * cs.length) + BitVec.ofInt 64 (exPlus ex cr.length).2 =
      pc + BitVec.ofNat 64 (16 * (cs ++ cr).length) + BitVec.ofInt 64 ex.2 := by
    simp only [exPlus, List.length_append]; exact tgt_eq (by omega)
  simp only [execBlock]
  generalize execStmt O passes R s σ ρ = o at ih ⊢
  cases o with
  | ok σ1 ρ1 =>
    obtain ⟨m1, s1, a1, e1, hw1, k1⟩ := ih
    have hf := codeFar_right (n := cs.length) (k := cr.length) (by simpa using hp.far)
    have hp1 : PreS m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K (frei Γ) cr ρ1 :=
      ⟨hp.ctx, hp.small, frameOK_agreeW hp.frame a1, codeAt_agreeWIn hW a1 (codeAt_right hp.code) hf, hf, e1, trivial,
        wstab_true _ _⟩
    have ih2 := ihRest (ex := ex) cr tr hr (by omega)
      (by omega) hW m1 _ σ1 ρ1 hp1 hlo hlo2 (hu.agreeW hW a1 hlo) (hk.agreeW hW a1 (by omega)) hw1 hpr
    rw [pc_add1]
    exact Sim.prefix hlo s1 a1 k1 ih2
  | zurueck | why | leave | next | logik | hardware => exact Sim.ziel ih (fun _ _ h => by cases h) hL hN

theorem blockBind_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {τ : Ty} {e : Expr D Γ Λ τ} {rest : Block D (vertragVon D f) l (τ :: Γ) Λ Λ'} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .bind e rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  simp only [execBlock]
  have hks := hW.ks
  have htop := lowE_top e _ _ _ he
  have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw, hen⟩ :=
    lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) e _ ce te he (by omega) m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
  have hf := codeFar_right (n := ce.length) (k := cr.length) (by simpa using hp.far)
  have hp1 : PreS m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (frei Γ + 1) cr
      (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) :=
    ⟨by simp only [frei, List.length_cons]; omega, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf,
     envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) hw hen, trivial, wstab_true _ _⟩
  have ih := ihRest (ex := ex) cr tr hr (by omega)
    (by omega) hW m1 _ (σ.lese Λ e.orte) _ hp1 hlo
    (by simp only [frei, List.length_cons] at hlo2 ⊢; omega) (hu.agreeW hW (agreeW_of (a1.mono hlo2)) hlo)
    (hk.agreeW hW (agreeW_of (a1.mono hlo2)) (by omega)) hWa1 (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
  rw [pc_add1]
  exact Sim.prefix hlo s1 (agreeW_of (a1.mono hlo2)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Sim.schrumpf ih)

end Gabbro.Stage0.Senke
