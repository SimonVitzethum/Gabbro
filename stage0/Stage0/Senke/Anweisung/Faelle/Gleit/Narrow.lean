/- Float range narrowing with a terminating fallback, using the shared binding continuation. -/
import Stage0.Senke.Anweisung.Faelle.Binden
import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check
import Stage0.Senke.Ausdruck.Gleit.Test
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem blockFloatNarrow_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {low high low' high' : Int × Int} {e : Expr D Γ Λ (.fl low high)}
    {err : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Block D (vertragVon D f) l (.fl low' high' :: Γ) Λ Λ'} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err) →
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (.floatNarrow e low' high' err rest) := by
  intro ihErr ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB] at h
  split at h
  · next hfit =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfit
    obtain ⟨hl, hh⟩ := hfit
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, he, ⟨cr, tr⟩, hr, ⟨cx, tx⟩, hx, hc⟩ := h
    cases hc
    have hroom := floatRangeL_room hcc
    have het := lowE_top e _ _ _ he
    simp only [floatNarrowC, List.length_append, List.length_singleton] at hs
    simp only [execBlock]
    let σr := σ.lese Λ e.orte
    have hchoice := choice_ok (P := P) (σ0 := σ0) (ex := ex) (d := frei Γ) (cc := cc) (ct := cx) (ce := ce ++ cr)
      (b := floatOutside low' high' (eval σr e σr ρ).x)
      (ot := match gleitPasst low' high' (eval σr e σr ρ).x with
        | some v => (execBlock O passes R rest σr (Env.cons v ρ)).schrumpf
        | none => (execEnd O passes R err σr ρ).zuAusgang)
      (oe := match gleitPasst low' high' (eval σr e σr ρ).x with
        | some v => (execBlock O passes R rest σr (Env.cons v ρ)).schrumpf
        | none => (execEnd O passes R err σr ρ).zuAusgang)
      (Nat.le_refl _) (by have := hW.ks; omega) (by simpa only [List.length_append] using hs)
      hW hlo hlo0 hlo2 hpr (σ := σr) ?_ ?_ ?_
      (by simpa only [floatNarrowC, List.length_append, Int.natCast_add] using hp) hu hk hWa
    · cases hv : gleitPasst low' high' (eval σr e σr ρ).x <;>
        simpa only [ite_self, hv, floatNarrowC, List.length_append, Int.natCast_add] using hchoice
    · intro hpc
      have hks := hW.ks
      have hpw := PreS.welt hpc hks hWa hW.lay (by have := hW.lo; omega)
      obtain ⟨m1, st, a1, w, hw, hen⟩ := floatRangeL_ok σr σr e
        (fun d c top h hK m pc hp => lowE_ok σr σr (fun _ h => h) e d c top h hK m pc ρ hp)
        hl hh hcc (by omega) hpw
      exact ⟨m1, st, Agree.widen a1 hks, w, hw, by simpa only [bool_word] using hen⟩
    · intro hb m' pc' hp' _ hu' hk' hw'
      have hv := (floatOutside_none hl hh (eval σr e σr ρ).endlich).mpr hb
      rw [hv]
      exact Ret.toSim (ihErr (ex := exPlus ex ((ce ++ cr).length + 1)) cx tx (by simpa only [List.length_append] using hx) (by omega) (by omega) hW
        m' pc' σr ρ hp' hlo2 hu' hk' hw' hpr)
    · intro hb m' pc' hp' _ hu' hk' hw'
      cases hv : gleitPasst low' high' (eval σr e σr ρ).x with
      | none =>
        have hf := (floatOutside_none hl hh (eval σr e σr ρ).endlich).mp hv
        rw [hb] at hf
        cases hf
      | some v =>
        have hvx := floatPasst_x hv
        refine bindValue_ok (L := L) (τ := .fl low' high') (v := v) hW hlo hlo0 hlo2 hpr (by omega) ?_ ?_ hp' hu' hk' hw'
        · intro m pc hp
          exact (lowE_ok σr σr (fun _ h => h) e _ ce te he (by omega) m pc ρ hp).mono
            fun w hen => ⟨by simpa only [hvx] using hen.1, by simpa only [hvx] using hen.2⟩
        · intro m pc hp hu hk hw
          exact ihRest (ex := ex) cr tr hr (by omega) (by omega) hW m pc σr _ hp hlo
            (by simp only [frei, List.length_cons] at hlo2 ⊢; omega) hu hk hw
            (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
  · next hnan =>
    have hn : Gleitkomma.klasse Gleitkomma.f64 (bruch low') = .nan ∨
        Gleitkomma.klasse Gleitkomma.f64 (bruch high') = .nan := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hnan
      by_cases hl : Gleitkomma.klasse Gleitkomma.f64 (bruch low') = .nan
      · exact Or.inl hl
      · exact Or.inr (Classical.byContradiction fun hh => hnan ⟨hl, hh⟩)
    simp only [execBlock, floatPasst_nan_bound _ hn]
    exact Ret.toSim (ihErr (ex := ex) c top h hK hs hW m pc _ ρ hp hlo2 hu hk hWa hpr)


end Gabbro.Stage0.Senke
