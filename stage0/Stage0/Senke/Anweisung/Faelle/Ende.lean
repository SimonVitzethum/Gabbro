/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
import Stage0.Senke.Anweisung.Faelle.Kontext

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem endRet_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {e : ErgExpr D Γ Λ (D.erg f)} {proof0 : _} :
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .ret e proof0) := by
  intro c top h hK _ hW m pc σ ρ hp hlo _ hk hWa hpr
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, he, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [execEnd, Ret]
  exact ret_ok hlo0 hens e he (by omega) m pc σ ρ hp hlo hk hW hWa

theorem endCons_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {Λmid : List (Res D)} {s : Stmt D (vertragVon D f) l Γ Λ Λmid} {rest : Endblock D (vertragVon D f) l Γ Λmid} :
    (∀ {pr ex}, StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex s) →
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .cons s rest) := by
  intro ihS ihRest c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs1, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  have hFB3 : FB = 4 := rfl
  have ih := ihS (ex := exPlus ex cr.length) cs ts
    hs1 (by omega) (by omega) hW m pc σ ρ hp.left (by omega) hlo hu hk hWa hpr
  have hL : pc + BitVec.ofNat 64 (16 * cs.length) + BitVec.ofInt 64 (exPlus ex cr.length).1 =
      pc + BitVec.ofNat 64 (16 * (cs ++ cr).length) + BitVec.ofInt 64 ex.1 := by
    simp only [exPlus, List.length_append]; exact tgt_eq (by omega)
  have hN : pc + BitVec.ofNat 64 (16 * cs.length) + BitVec.ofInt 64 (exPlus ex cr.length).2 =
      pc + BitVec.ofNat 64 (16 * (cs ++ cr).length) + BitVec.ofInt 64 ex.2 := by
    simp only [exPlus, List.length_append]; exact tgt_eq (by omega)
  simp only [execEnd]
  generalize execStmt O passes R s σ ρ = o at ih ⊢
  cases o with
  | ok σ1 ρ1 =>
    obtain ⟨m1, s1, a1, e1, hw1, k1⟩ := ih
    have hf := codeFar_right (n := cs.length) (k := cr.length) (by simpa using hp.far)
    have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K (frei Γ) cr ρ1 :=
      ⟨hp.ctx, hp.small, frameOK_agreeW hp.frame a1, codeAt_agreeWIn hW a1 (codeAt_right hp.code) hf, hf, e1, trivial,
        wstab_true _ _⟩
    have ih2 := ihRest (ex := ex) cr tr hr
      (by omega) (by omega) hW m1 _ σ1 ρ1 hp1 hlo (hu.agreeW hW a1 (by omega)) (hk.agreeW hW a1 (by omega)) hw1 hpr
    rw [pc_add1]
    exact Ret.prefix (by omega) s1 a1 k1 ih2
  | zurueck σ' v => exact ih
  | logik e => exact ih
  | leave _ σ' ρ' => exact (show Reach L fp lo K pr _ m _ σ' ρ' from hL ▸ ih)
  | next _ σ' ρ' => exact (show Reach L fp lo K pr _ m _ σ' ρ' from hN ▸ ih)
  | hardware e => exact ih
  | why => exact ih

theorem endBind_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} {e : Expr D Γ Λ τ} {rest : Endblock D (vertragVon D f) l (τ :: Γ) Λ} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .bind e rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  have hFB3 : FB = 4 := rfl
  simp only [execEnd]
  have htop := lowE_top e _ _ _ he
  have hks := hW.ks
  have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw, hen⟩ :=
    lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) e _ ce te he (by omega) m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
  have hf := codeFar_right (n := ce.length) (k := cr.length) (by simpa using hp.far)
  have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (frei Γ + 1) cr
      (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) :=
    ⟨by simp only [frei, List.length_cons]; omega, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf,
     envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) hw hen, trivial, wstab_true _ _⟩
  have ih := ihRest (ex := ex) cr tr hr (by omega) (by omega) hW m1 _ (σ.lese Λ e.orte) _ hp1
    (by simp only [frei, List.length_cons] at hlo ⊢; omega) (hu.agree a1 hp.frame (by omega))
    (hk.agree a1 hp.frame (by omega)) hWa1 (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
  rw [pc_add1]
  exact Ret.prefix (by omega) s1 (a1.mono (by omega)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Ret.schrumpf ih)

end Gabbro.Stage0.Senke
