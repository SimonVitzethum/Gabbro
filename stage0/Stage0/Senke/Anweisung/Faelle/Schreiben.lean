/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
import Stage0.Senke.Anweisung.Faelle.Kontext

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem assignVar_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} {x : Var Γ τ} {e : Expr D Γ Λ τ} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .assignVar x e) := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 _ _ hWa hpr
  simp only [lowS] at h
  split at h
  · next hlx =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [execStmt, Sim]
    have hks := hW.ks
    have htop := lowE_top e _ _ _ he
    have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, s1, a1s, w, hw, hen⟩ := lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) e _ ce te he (by omega)
      m pc ρ hpw
    have a1 := Agree.widen a1s hks
    have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
    have hxs := vslot_lt x
    have hsm := hp.small
    have s2 := mov_to hp1.code hp1.frame (j := vslot x) (by omega) (by omega) hsm hw
    have hF1 := hp1.frame
    have a2s : Agree fp lo Ks m1 _ := agree_write (frameOK_sub hF1 hks).room hlx.1 (by omega) w.toNat
    refine ⟨_, s1.trans (by rw [pc_add1]; exact s2), agreeW_of ((a1.mono hlo2).trans (Agree.widen a2s hks)), ?_,
      hpw.wstab m _ hWa ((a1s.mono (Nat.zero_le _)).trans (a2s.mono (Nat.zero_le _))),
      (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)).trans (keeps_write hF1.room (by omega) (fun j hj => by have := hpr j hj; omega) hlx.2 _)⟩
    refine envAt_set hp1.env (rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))) hen ?_
    intro τ' y hy
    have := vslot_lt y
    exact rd64_write_far (slot_far hF1.room (by omega) (by omega) (vslot_ne hy).symm)
  · simp at h

theorem call_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {callee : D.Fn} {args : Args D Γ Λ (D.params callee)} {proof0 : _} {proof1 : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ (nach D callee Λ) from .call callee args proof0 proof1) := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 hu hk hWa hpr
  simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ca, ta⟩, hca, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have hct : frei Γ + FB + (D.params callee).length + 1 ≤ callTop callee (frei Γ) ta := by simp only [callTop]; omega
  have hc := callC_ok hS (hA callee) args (σ.lese Λ args.orte) (σ.lese Λ args.orte) hca (by omega) hp hu hW hWa
  simp only [execStmt]
  generalize R callee (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = o at hc ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m1, s1, a1, _, hw1⟩ := hc
    have := hW.ks
    exact ⟨m1, s1, a1.mono hlo2, envAt_agreeWIn hW hp.env a1 (Nat.le_refl _) (by omega), hw1,
      keeps_of_agreeW hW a1 hpr (by omega)⟩
  | logik e => exact hc
  | why _ _ => exact hc.elim
  | hardware e => exact hc

theorem ret_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {e : ErgExpr D Γ Λ (D.erg f)} {proof0 : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .ret e proof0) := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 _ hk hWa hpr
  simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, he, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [execStmt, Sim]
  exact ret_ok hlo0 hens e he (by omega) m pc σ ρ hp hlo2 hk hW hWa

end Gabbro.Stage0.Senke
