/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
module
public import Stage0.Senke.Anweisung.Faelle.Kontext
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem assignVar_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowEns L (functionFrame P f) (P.ensures f) (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} {x : Var Γ τ} {e : Expr D Γ Λ τ} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .assignVar x e) reserved := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 _ _ hWa hpr
  simp only [lowS, ← hlo0, resultWords_vertragVon] at h
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
    obtain ⟨m1, s1, a1s, value⟩ := lowE_ok (reserved := reserved) (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) hW.lay e _ ce te he (by omega)
      m pc ρ hpw
    have a1 := Agree.widen a1s hks
    have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
    have placed : vslot x reserved + valueWords τ ≤ frei Γ reserved := by
      have bound := variableOffset_bound x
      unfold vslot frei
      omega
    have frame1 := frameOK_sub hp1.frame hks
    obtain ⟨m2, s2, exact2, output⟩ := copyValue_run frame1 (by have := hp.small; omega)
      (by omega) (by omega) (Or.inl (by omega)) hp1.code
      (by simpa only [copyWords_length] using codeFar_sub2 hp1.far hks) value
    have a2s : Agree fp lo Ks m1 m2 := (Agree.widen exact2 (by omega)).mono hlx.1
    have hprotected : ∀ j ∈ pr, j < vslot x reserved ∨ vslot x reserved + valueWords τ ≤ j := by
      intro j hj
      simpa only [decide_eq_true_eq] using (List.all_eq_true.mp hlx.2) j hj
    have copyKeeps : Keeps fp pr m1 m2 := by
      intro j hj
      rcases hprotected j hj with before | after
      · exact agree_rd_low exact2 (by have := frame1.room; omega) before (by omega)
      · exact agree_rd_above exact2 frame1.room after (by have := hpr j hj; omega)
    refine ⟨m2, ?_, agreeW_of ((a1.mono hlo2).trans (Agree.widen a2s hks)), ?_,
      hpw.wstab m m2 hWa ((a1s.mono (Nat.zero_le _)).trans (a2s.mono (Nat.zero_le _))),
      (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)).trans copyKeeps⟩
    · simpa only [List.length_append, copyWords_length, pc_add] using s1.trans s2
    · refine envAt_set hp1.env output ?_
      intro τ' y hy i hi
      have yBound : vslot y reserved + valueWords τ' ≤ frei Γ reserved := by
        have bound := variableOffset_bound y
        unfold vslot frei
        omega
      have separation := variableOffset_disjoint x y hy
      rcases separation with after | before
      · exact agree_rd_above exact2 frame1.room (by unfold vslot at *; omega) (by omega)
      · exact agree_rd_low exact2 (by have := frame1.room; omega) (by unfold vslot at *; omega) (by omega)
  · simp at h

theorem call_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowEns L (functionFrame P f) (P.ensures f) (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {callee : D.Fn} {args : Args D Γ Λ (D.params callee)} {proof0 : _} {proof1 : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ (nach D callee Λ) from .call callee args proof0 proof1) reserved := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 hu hk hWa hpr
  simp only [lowS, ← hlo0, resultWords_vertragVon, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ca, ta⟩, hca, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have hct : frei Γ reserved + FB + (contextWords (D.params callee)) + 1 ≤ callTop callee (frei Γ reserved) ta := by simp only [callTop]; omega
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
  | why _ r => exact (keinGrund proof1 r : False).elim
  | hardware e => exact hc

theorem ret_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowEns L (functionFrame P f) (P.ensures f) (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {e : ErgExpr D Γ Λ (D.erg f)} {proof0 : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .ret e proof0) reserved := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 _ hk hWa hpr
  simp only [lowS, ← hlo0, resultWords_vertragVon, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, he, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [execStmt, Sim]
  change max te (max tens (retTop (functionFrame P f))) + cap ≤ Ks at hK
  exact ret_ok (reserved := reserved) hlo0 hens e he (by omega) m pc σ ρ hp hlo2 hk hW hWa

end Gabbro.Stage0.Senke
