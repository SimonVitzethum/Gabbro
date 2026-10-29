/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
import Stage0.Senke.Anweisung.Faelle.Kontext
import Stage0.Senke.Anweisung.TorLauf

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem leave_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {proof0 : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .leave proof0) := by
  intro c top h _ _ _ m pc σ ρ hp _ _ _ _ hWa _
  simp only [lowS] at h
  split at h
  · next hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execStmt, Sim]
    exact jmp_reach hp.code hl hp.env hWa
  · cases h

theorem next_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {proof0 : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .next proof0) := by
  intro c top h _ _ _ m pc σ ρ hp _ _ _ _ hWa _
  simp only [lowS] at h
  split at h
  · next hl =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execStmt, Sim]
    exact jmp_reach hp.code hl hp.env hWa
  · cases h

theorem axiomCall_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {hn : _} {proof0 : _} {proof1 : _} {proof2 : _} {proof3 : _} :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .axiomCall a args hn proof0 proof1 proof2 proof3) := by
  intro c top h hK _ hW m pc σ ρ hp _ hlo2 _ _ hWa hpr
  simp only [lowS] at h
  have hks := hW.ks
  have h7 := torC_top h
  obtain ⟨m1, w, s1, a1, _, hw1, _⟩ := torC0_ok (O := O) (σ := σ.lese Λ args.orte) h (by omega) hW hp hWa
  obtain ⟨u, hu⟩ := einpassenErg_none (z := O.zeiger) hn
    (O.wirkt a ((σ.lese Λ args.orte).fragt (.inl a)) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2
  simp only [execStmt]
  rw [axiomAntwort_eq, hu]
  exact ⟨m1, s1, a1.mono hlo2, envAt_agreeWIn hW hp.env a1 (Nat.le_refl _) (by omega), hw1,
    keeps_of_agreeW hW a1 hpr (by omega)⟩

end Gabbro.Stage0.Senke
