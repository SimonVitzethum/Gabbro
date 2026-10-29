/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
import Stage0.Senke.Anweisung.Faelle.Kontext
import Stage0.Senke.Anweisung.Faelle.Wahl

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- End blocks have no normal fallthrough target. -/
theorem Ret.toSim {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {fp rp cfp : Runner.W} {lo K : Nat} {pr : List Nat}
    {t : T} {m : Runner.Mem} {e eL eN : Runner.W} {l : Bool} {Γ : Ctx}
    {o : EndAusgang (vertragVon D f) l Γ}
    (h : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr t m e eL eN o.zuAusgang := by
  cases o <;> exact h

theorem blockCheck_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cnd : Expr D Γ Λ .bool} {err : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Block D (vertragVon D f) l Γ Λ Λ'} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err) →
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (.check cnd err rest) := by
  intro ihErr ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, hce, ⟨cr, tr⟩, hr, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append, List.length_singleton] at hs
  have htop := lowE_top cnd (frei Γ) cc tc hcc
  simp only [execBlock]
  refine choice_ok (P := P) (σ0 := σ0) (ex := ex) (d := frei Γ)
    (b := wahr? (D := D) (eval (σ.lese Λ cnd.orte) cnd (σ.lese Λ cnd.orte) ρ))
    (Nat.le_refl _) (by have := hW.ks; omega) hs hW hlo hlo0 hlo2 hpr ?_ ?_ ?_ hp hu hk hWa
  · intro hpc
    have hks := hW.ks
    have hpw := PreS.welt hpc hks hWa hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, st, a1, w, hw, hen⟩ := lowE_ok (σ.lese Λ cnd.orte) (σ.lese Λ cnd.orte)
      (fun _ h => h) cnd (frei Γ) cc tc hcc (by omega) m pc ρ hpw
    exact ⟨m1, st, Agree.widen a1 hks, w, hw, hen⟩
  · intro _ m' pc' hp' _ hu' hk' hw'
    exact ihRest (ex := exPlus ex (ce.length + 1)) cr tr hr (by omega) (by omega) hW
      m' pc' _ ρ hp' hlo hlo2 hu' hk' hw' hpr
  · intro _ m' pc' hp' _ hu' hk' hw'
    exact Ret.toSim (ihErr (ex := ex) ce te hce (by omega) (by omega) hW
      m' pc' _ ρ hp' hlo2 hu' hk' hw' hpr)

end Gabbro.Stage0.Senke
