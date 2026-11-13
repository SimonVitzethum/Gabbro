/- Connect native CPU arithmetic to the generic Block simulation theorem. -/
module
public import Stage0.Senke.Anweisung.Faelle.Binden
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check
public import Stage0.Senke.Anweisung.Faelle.Gleit.Bind
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}
variable {H : List D.Lock}

theorem blockFloatArithmetic_case (op : GleitOp) {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {l₁ h₁ l₂ h₂ low high : Int × Int}
    {a : Expr D Γ Λ (.fl l₁ h₁)} {b : Expr D Γ Λ (.fl l₂ h₂)}
    {rest : Block D (vertragVon D f) l (.fl low high :: Γ) Λ Λ'} :
    (∀ {pr ex}, BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H rest) →
    BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex H
      (.float op a b low high rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, floatArithmeticBlockL_eq op, ← hlo0] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, he, ⟨cc, tc⟩, hcc, ⟨cr, tr⟩, hr, hc⟩ := h
  cases hc
  let σr := σ.lese Λ (a.orte ++ b.orte)
  let x := gleitRechne op (eval σr a σr ρ).x (eval σr b σr ρ).x
  have result := nativeFloatBind_ok (P := P) (σ := σr) (x := x)
    (out := fun v => execBlock O passes R rest σr (Env.cons v ρ))
    hcc (by omega) (by simpa only [List.length_append] using hs)
    hW hlo hlo0 hlo2 hpr
    (fun m pc pre => floatWordsL_ok op (eval σr a σr ρ).x (eval σr b σr ρ).x
      (fun {fp K j c t} hc ht m pc pre =>
        (lowE_ok σr σr (fun _ h => h) hW.lay (same := fun _ => rfl)
          a j c t hc ht m pc ρ pre).word trivial)
      (fun {fp K j c t} hc ht m pc pre =>
        (lowE_ok σr σr (fun _ h => h) hW.lay (same := fun _ => rfl)
          b j c t hc ht m pc ρ pre).word trivial)
      he (by omega) m pc pre)
    (fun v m pc pre hu hk hw => ihRest (ex := ex) cr tr hr (by omega)
      (by simp only [floatNarrowC, List.length_append, List.length_nil, List.nil_append] at hs; omega)
      hW m pc σr _ pre hlo
      (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega) hu hk hw
      (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega))
    hp hu hk hWa
  have outcome : execBlock O passes R (.float op a b low high rest) σ ρ =
      (match gleitPasst low high x with
      | none => .logik .bereich
      | some v => (execBlock O passes R rest σr (Env.cons v ρ)).schrumpf) := by
    change (match gleitPasst low high x with
      | some v => (execBlock O passes R rest σr (Env.cons v ρ)).schrumpf
      | none => .logik .bereich) = _
    cases gleitPasst low high x <;> rfl
  rw [outcome]
  exact result


#print axioms blockFloatArithmetic_case
end Gabbro.Stage0.Senke
