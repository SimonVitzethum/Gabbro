/- Float range narrowing with a terminating fallback, using the shared binding continuation. -/
module
public import Stage0.Senke.Anweisung.Faelle.Gleit.EndSupport
public import Stage0.Senke.Anweisung.Faelle.Binden
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check
public import Stage0.Senke.Ausdruck.Gleit.Slots.Test
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}
variable {H : List D.Lock}
variable {sc : List D.Lock}

theorem endFloatNarrow_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {low high low' high' : Int × Int} {e : Expr D Γ Λ (.fl low high)}
    {err : Endblock D (vertragVon D f) l Γ Λ}
    {rest : Endblock D (vertragVon D f) l (.fl low' high' :: Γ) Λ} :
    (∀ {pr ex}, EndCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc err) →
    (∀ {pr ex}, EndFloatCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc rest) →
    EndFloatCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H sc (.floatNarrow e low' high' err rest) := by
  intro ihErr ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowEnd, ← hlo0] at h
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
    simp only [execEnd]
    let σr := σ.lese Λ e.orte
    have hchoice := choice_ok (sc := sc) (P := P) (σ0 := σ0) (ex := ex) (d := frei Γ reserved) (cc := cc) (ct := cx) (ce := ce ++ cr)
      (b := floatRangeReject low' high' (eval σr e σr ρ).x)
      (ot := match gleitPasst low' high' (eval σr e σr ρ).x with
        | some v => (execEnd O passes R rest σr (Env.cons v ρ)).zuAusgang.schrumpf
        | none => (execEnd O passes R err σr ρ).zuAusgang)
      (oe := match gleitPasst low' high' (eval σr e σr ρ).x with
        | some v => (execEnd O passes R rest σr (Env.cons v ρ)).zuAusgang.schrumpf
        | none => (execEnd O passes R err σr ρ).zuAusgang)
      (Nat.le_refl _) (by have := hW.ks; omega) (by simpa only [List.length_append] using hs)
      hW hlo hlo0 hlo2 hpr (σ := σr) ?_ ?_ ?_
      (by simpa only [floatNarrowC, List.length_append, Int.natCast_add] using hp) hu hk hWa
    · cases hv : gleitPasst low' high' (eval σr e σr ρ).x with
      | none =>
        simpa only [ite_self, hv, EndAusgang.zuAusgang, floatNarrowC,
          List.length_append, Int.natCast_add] using hchoice
      | some v =>
        simpa only [ite_self, hv, floatEnd_schrumpf, floatNarrowC,
          List.length_append, Int.natCast_add] using hchoice
    · intro hpc
      have hks := hW.ks
      have hpw := PreS.welt hpc hks hWa hW.lay (by have := hW.lo; omega)
      obtain ⟨m1, st, a1, w, hw, hen⟩ := floatRangeL_ok σr σr e
        (fun d c top h hK m pc hp => lowE_ok (same := by intro _; rfl) σr σr (fun _ h => h) hW.lay e d c top h hK m pc ρ hp |>.word trivial)
        hcc (by omega) hpw
      exact ⟨m1, st, Agree.widen a1 hks, w, hw, by simpa only [bool_word] using hen⟩
    · intro hb m' pc' hp' _ hu' hk' hw'
      have hv := (floatRangeReject_none).mpr hb
      rw [hv]
      exact Ret.toSim (ihErr (ex := exPlus ex ((ce ++ cr).length + 1)) cx tx (by simpa only [List.length_append] using hx) (by omega) (by omega) hW
        m' pc' σr ρ hp' hlo2 hu' hk' hw' hpr)
    · intro hb m' pc' hp' _ hu' hk' hw'
      cases hv : gleitPasst low' high' (eval σr e σr ρ).x with
      | none =>
        have hf := (floatRangeReject_none).mp hv
        rw [hb] at hf
        cases hf
      | some v =>
        have hvx := floatPasst_x hv
        have encoded : encodeWords L (.fl low' high') v =
            [v.x.hwToBits.toBitVec] := by
          rw [encodeWords.eq_def L (.fl low' high') v]
        have sourceEncoded : encodeWords L (.fl low high) (eval σr e σr ρ) =
            [(eval σr e σr ρ).x.hwToBits.toBitVec] := by
          rw [encodeWords.eq_def L (.fl low high) (eval σr e σr ρ)]
        refine bindValue_ok (L := L) (τ := .fl low' high') (v := v) hW hlo hlo0 hlo2 hpr (by omega) ?_ ?_ hp' hu' hk' hw'
        · intro m pc hp
          exact (lowE_ok (same := by intro _; rfl) σr σr (fun _ h => h) hW.lay e _ ce te he (by omega) m pc ρ hp).mono
            fun m hen => ⟨by simpa only [ValueValid, hvx] using hen.1,
              by rw [encoded, hvx]; simpa only [sourceEncoded] using hen.2⟩
        · intro m pc hp hu hk hw
          exact ihRest (ex := ex) cr tr hr (by omega) (by omega) hW m pc σr _ hp hlo
            (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega) hu hk hw
            (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega)
  · next hnan =>
    have hn : (bruch low').hwIsNaN = true ∨ (bruch high').hwIsNaN = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hnan
      apply Classical.byContradiction
      intro absent
      apply hnan
      constructor
      · exact Bool.eq_false_iff.mpr (fun h => absent (Or.inl h))
      · exact Bool.eq_false_iff.mpr (fun h => absent (Or.inr h))
    simp only [execEnd, EndAusgang.zuAusgang, floatPasst_nan_bound _ hn]
    exact Ret.toSim (ihErr (ex := ex) c top h hK hs hW m pc _ ρ hp hlo2 hu hk hWa hpr)



end Gabbro.Stage0.Senke
