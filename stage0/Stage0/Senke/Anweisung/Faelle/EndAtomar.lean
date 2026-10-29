/- Extracted lowering cases; recursive subterms are supplied as induction hypotheses. -/
import Stage0.Senke.Anweisung.Faelle.Kontext
import Stage0.Senke.Anweisung.Atomar

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem endAwaits_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {g : D.Glob} {proof0 : List D.Glob} {proof1 : _} {proof2 : _} {proof3 : _} {rest : Endblock D (vertragVon D f) l (D.gtyp g :: Γ) Λ} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .awaits g proof0 proof1 proof2 proof3 rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd] at h
  split at h
  · next hl =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hFB3 : FB = 4 := rfl
    have hks := hW.ks
    obtain ⟨m1, s1, A, hp1, hW1⟩ := awaits_head hl (by omega) hW hp hWa
    simp only [execEnd, SichtOK.sicht, ↓reduceIte]
    have ih := ihRest (ex := ex) cr tr hr (by omega)
      (by omega) hW m1 _ ((σ.fragt (.inr (.inr g))).lese Λ [.inr g]) _ hp1
      (by simp only [frei, List.length_cons] at hlo ⊢; omega) (hu.agreeW hW (A.mono hlo) (by omega))
      (hk.agreeW hW (A.mono hlo) (by omega)) hW1 (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
    rw [pc_add1]
    exact Ret.prefix (by omega) s1 (A.mono hlo) (keeps_of_agreeW hW A hpr (by omega)) (Ret.schrumpf ih)
  · cases h

theorem endExchange_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
     {g : D.Glob} {neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)} {proof0 : _} {proof1 : _} {rest : Endblock D (vertragVon D f) l (D.gtyp g :: Γ) Λ} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .exchange g neu proof0 proof1 rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  simp only [lowEnd] at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff, pure] at h
    obtain ⟨⟨cn, tn⟩, hn, ⟨cr, tr⟩, hr, h⟩ := h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hlen := exC_len (frei Γ) (L.ga g) cn
      simp only [List.length_append, hlen] at hs
      have hFB3 : FB = 4 := rfl
      have hks := hW.ks
      obtain ⟨m3, s3, A, hp3, hW3⟩ := exch_head (Λ := Λ) hn (by omega) (by omega) hW hp hWa
      simp only [execEnd]
      have ih := ihRest (ex := ex) cr tr hr (by omega)
        (by omega) hW m3 _ _ _ hp3
        (by simp only [frei, List.length_cons] at hlo ⊢; omega) (hu.agreeW hW (A.mono hlo) (by omega))
        (hk.agreeW hW (A.mono hlo) (by omega)) hW3 (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
      rw [pc_add1]
      exact Ret.prefix (by omega) s3 (A.mono hlo) (keeps_of_agreeW hW A hpr (by omega)) (Ret.schrumpf ih)
    · cases h
  · cases h

end Gabbro.Stage0.Senke
