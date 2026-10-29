/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
import Stage0.Senke.Anweisung.Simulation
import Stage0.Senke.Anweisung.Schreiben
import Stage0.Senke.Anweisung.Schleife
import Stage0.Senke.Anweisung.TorLauf
import Stage0.Senke.Sperre.Satz
import Stage0.Senke.Anweisung.Atomar
import Stage0.Senke.Anweisung.Wahl
import Stage0.Senke.Anweisung.Option
import Stage0.Senke.Anweisung.Tag

import Stage0.Senke.Anweisung.FehlerLauf
import Stage0.Senke.Anweisung.Faelle.Kontext

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem blockCall_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {τ : Ty} {callee : D.Fn} {args : Args D Γ Λ (D.params callee)} {he : D.erg callee = some τ} {proof0 : _} {proof1 : _} {rest : Block D (vertragVon D f) l (τ :: Γ) (nach D callee Λ) Λ'} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .bindCall callee args he proof0 proof1 rest) := by
    intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
    simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, hca, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hFB3 : FB = 3 := rfl
    have hks := hW.ks
    have hct : frei Γ + FB + (D.params callee).length + 1 ≤ callTop callee (frei Γ) ta := by simp only [callTop]; omega
    have hc := callC_ok hS (hA callee) args (σ.lese Λ args.orte) (σ.lese Λ args.orte) hca (by omega) hp.left.left hu hW hWa
    simp only [execBlock]
    generalize R callee (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = o at hc ⊢
    cases o with
    | ok σ' v =>
      obtain ⟨m1, s1, a1, ⟨w, hw, hew⟩, hw1⟩ := hc
      have hp1 := hp.left.nextW hW a1 (by have := hp.ctx; omega) (Nat.le_refl _) (by omega)
      have s2 := mov_to hp1.code hp1.frame (j := frei Γ) (s := frei Γ + 2) (by omega) (by omega) hp.small hw
      rw [← pc_add1] at s2
      let m2 := write m1 (slot fp (BitVec.ofNat 64 (frei Γ))) 8 w.toNat
      have a2s : Agree fp (frei Γ) Ks m1 m2 := agree_write (frameOK_sub hp1.frame hks).room (Nat.le_refl _) (by omega) _
      have a2 : Agree fp (frei Γ) K m1 m2 := Agree.widen a2s hks
      have hw2 : WeltAt m2 L σ' :=
        weltAt_stab hW.lay (by have := hW.lo; omega) m1 m2 hw1 (a2s.mono (Nat.zero_le _))
      have hq := hp.nextW hW (a1.trans (agreeW_of a2)) (d' := frei Γ + 1) (by have := hp.ctx; omega) (by omega)
        (by omega)
      have hp2 : PreS m2 _ fp K (frei Γ + 1) cr (Env.cons (ergWert he v) ρ) :=
        ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
         envAt_cons hq.env (rd_same hp1.frame (by omega) w) (encErg_wert he hew), trivial, wstab_true _ _⟩
      have ih := ihRest (ex := ex) cr tr hr (by omega)
        (by omega) hW m2 _ σ' _ hp2 hlo
        (by simp only [frei, List.length_cons] at hlo2 ⊢; omega)
        (hu.agreeW hW ((a1.trans (agreeW_of a2)).mono hlo2) hlo)
        (hk.agreeW hW ((a1.trans (agreeW_of a2)).mono hlo2) (by omega)) hw2
        (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
      rw [pc_add1 pc (callC A callee (frei Γ) ca ++ [ci 2 (frei Γ) (frei Γ + 2) 0]) cr]
      exact Sim.prefix hlo (s1.trans s2) ((a1.trans (agreeW_of a2)).mono hlo2)
        (keeps_of_agreeW hW (a1.trans (agreeW_of a2)) hpr (by have := hW.ks; omega)) (Sim.schrumpf ih)
    | logik e => exact hc
    | why _ _ => exact hc.elim
    | hardware e => exact hc

theorem blockAxiom_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {τ : Ty} {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {he : D.aerg a = some τ} {proof0 : _} {proof1 : _} {proof2 : _} {proof3 : _} {rest : Block D (vertragVon D f) l (τ :: Γ) Λ Λ'} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .bindAxiom a args he proof0 proof1 proof2 proof3 rest) := by
    intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
    simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ct, tt⟩, ht, ck, hck, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hks := hW.ks
    simp only [execBlock]
    rcases torBind_ok (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ) he ht hck (by omega) (by omega) hW hp hWa with
      ⟨v, m2, w, hAA, s12, a12, hw2, hen, hW2⟩ | ⟨hAA, hst⟩
    · rw [hAA]
      have hq := hp.nextW hW a12 (d' := frei Γ + 1) (by have := hp.ctx; omega) (by omega) (by omega)
      have hp2 : PreS m2 _ fp K (frei Γ + 1) cr (Env.cons (ergWert he v) ρ) :=
        ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
         envAt_cons hq.env hw2 hen, trivial, wstab_true _ _⟩
      have ih := ihRest (ex := ex) cr tr hr (by omega)
        (by omega) hW m2 _ _ _ hp2 hlo
        (by simp only [frei, List.length_cons] at hlo2 ⊢; omega)
        (hu.agreeW hW (a12.mono hlo2) hlo) (hk.agreeW hW (a12.mono hlo2) (by omega)) hW2
        (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
      rw [pc_add1 pc (ct ++ ck) cr]
      exact Sim.prefix hlo s12 (a12.mono hlo2) (keeps_of_agreeW hW a12 hpr (by omega)) (Sim.schrumpf ih)
    · rw [hAA]
      exact hst

end Gabbro.Stage0.Senke
