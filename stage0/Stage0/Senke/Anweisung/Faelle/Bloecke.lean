/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
import Stage0.Senke.Anweisung.Faelle.Binden

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

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
    have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K (frei Γ) cr ρ1 :=
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
  have ht := lowE_top e _ _ _ he
  simp only [execBlock]
  refine bindValue_ok hW hlo hlo0 hlo2 hpr (by omega)
    (fun m pc hp => lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) e _ ce te he (by omega) m pc ρ hp)
    ?_ hp hu hk hWa
  intro m pc hp hu hk hw
  exact ihRest (ex := ex) cr tr hr (by omega) (by omega) hW m pc _ _ hp hlo
    (by simp only [frei, List.length_cons] at hlo2 ⊢; omega) hu hk hw
    (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)

end Gabbro.Stage0.Senke
