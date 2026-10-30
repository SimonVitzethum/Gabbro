/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
import Stage0.Senke.Anweisung.Faelle.Kontext
import Stage0.Senke.Anweisung.Schleife

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem traverse_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {t : D.Tab} {inv : Expr D Γ Λ .bool} {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex body reserved) →
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Stmt D (vertragVon D f) l Γ Λ Λ from .traverse t inv body) reserved := by
  intro ihBody c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowS] at h
  split at h
  · next hn =>
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨ci', hci, cb, hcb, htr⟩ := h
    simp only [travC] at htr
    split at htr
    · next hlenc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at htr
      obtain ⟨rfl, rfl⟩ := htr
      have hlen := travCode_len (s := frei Γ reserved) (n := D.count t) (ci' := ci'.1) (cb := cb.1)
      simp only [execStmt]
      exact trav_ok hn hci hlenc hlo0 (by omega) hW hlo hlo2 hpr
        (fun m' pc' σ' ρ' hp' hu' hk' hw' => ihBody (ex := (48, 0)) (pr := frei Γ reserved :: pr) cb.1 cb.2 hcb (by omega) (by omega) hW m' pc' σ' ρ' hp' hlo
          (by have := hlo2; simp only [frei, List.length_cons] at this ⊢; omega) hu' hk' hw'
          (fun j hj => by
            simp only [List.mem_cons] at hj
            simp only [frei, List.length_cons]
            rcases hj with rfl | hj
            · simp only [frei]; omega
            · have := hpr j hj; simp only [frei] at this; omega)) hp hu hk hWa
    · cases htr
  · cases h

end Gabbro.Stage0.Senke
