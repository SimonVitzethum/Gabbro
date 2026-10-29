/- Indirect-call binder cases; both continuations reuse the shared call-prefix proof. -/
import Stage0.Senke.Anweisung.Faelle.Kontext

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem blockInd_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} {τ : Ty} {p : Expr D Γ Λ (.fnptr n)}
    {args : Args D Γ Λ (D.sigNr n).params} {he : (D.sigNr n).erg = some τ}
    {proof0 : RufPasst D (vertragVon D f) (D.sigNr n) Λ} {proof1 : (D.sigNr n).gruende = 0}
    {rest : Block D (vertragVon D f) l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ'} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .bindCallInd p args he proof0 proof1 rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨cc, tc⟩, hc, ⟨cr, tr⟩, hrest, rfl, rfl⟩ := h
  simp only [List.length_append] at hs
  rw [execBlock_ind_eq, pc_add1 pc (cc ++ [ci 2 (frei Γ) (frei Γ + 2) 0]) cr]
  exact indBind_ok hS hA p args he proof1 (σ.lese Λ (p.orte ++ args.orte)) ρ hc (by omega) hp hW hlo0 hlo2 hu hk hWa hpr
    _ _ _ (fun t m o => Sim L P f σ0 ρ0 rp cfp fp lo K pr t m _ _ _ o)
    (Sim.prefix hlo) (fun _ _ _ h => h) (fun _ _ _ h => h)
    (fun m' σ' v hp' hu' hk' hw' => Sim.schrumpf (ihRest (ex := ex) cr tr hrest (by omega) (by omega) hW m' _ σ' _ hp' hlo
      (by simp only [frei, List.length_cons] at hlo2 ⊢; omega) hu' hk' hw'
      (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)))

theorem endInd_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {n : Nat} {τ : Ty} {p : Expr D Γ Λ (.fnptr n)}
    {args : Args D Γ Λ (D.sigNr n).params} {he : (D.sigNr n).erg = some τ}
    {proof0 : RufPasst D (vertragVon D f) (D.sigNr n) Λ} {proof1 : (D.sigNr n).gruende = 0}
    {rest : Endblock D (vertragVon D f) l (τ :: Γ) (nachSig D (D.sigNr n) Λ)} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .bindCallInd p args he proof0 proof1 rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨cc, tc⟩, hc, ⟨cr, tr⟩, hrest, rfl, rfl⟩ := h
  simp only [List.length_append] at hs
  rw [execEnd_ind_eq, pc_add1 pc (cc ++ [ci 2 (frei Γ) (frei Γ + 2) 0]) cr]
  exact indBind_ok hS hA p args he proof1 (σ.lese Λ (p.orte ++ args.orte)) ρ hc (by omega) hp hW hlo0 hlo hu hk hWa hpr
    _ _ _ (fun t m o => Ret L P f σ0 ρ0 fp lo K pr rp cfp t m _ _ o)
    (Ret.prefix (by simp only [FB] at hlo0; omega)) (fun _ _ _ h => h) (fun _ _ _ h => h)
    (fun m' σ' v hp' hu' hk' hw' => Ret.schrumpf (ihRest (ex := ex) cr tr hrest (by omega) (by omega) hW m' _ σ' _ hp'
      (by simp only [frei, List.length_cons] at hlo ⊢; omega) hu' hk' hw'
      (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)))

end Gabbro.Stage0.Senke
