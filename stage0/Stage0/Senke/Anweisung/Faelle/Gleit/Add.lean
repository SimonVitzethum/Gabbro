/- Connect shared integer-only arithmetic to the generic Block simulation theorem. -/
module
public import Stage0.Senke.Anweisung.Faelle.Binden
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check
public import Stage0.Senke.Anweisung.Faelle.Gleit.AddCode
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

private theorem finiteArithmeticWf (kind : SoftFloatKernel) (a b : GFloat)
    (af : gleitEndlich a = true) (bf : gleitEndlich b = true) :
    Gleitkomma.wf Gleitkomma.f64 (kind.apply a b) := by
  cases kind <;>
    cases ka : Gleitkomma.klasse Gleitkomma.f64 a <;>
    cases kb : Gleitkomma.klasse Gleitkomma.f64 b
  all_goals simp only [gleitEndlich, ka, kb, Bool.false_eq_true] at af bf
  all_goals simp only [SoftFloatKernel.apply, Gleitkomma.add, Gleitkomma.mul, Gleitkomma.wertExakt, ka, kb]
  all_goals first
    | exact Gleitkomma.wf_null _ _
    | exact Gleitkomma.rundeExakt_wf _ Gleitkomma.f64_p _

private theorem gleitRechneArithmetic (op : GleitOp) (supported : op ≠ .div) (a b : GFloat) :
    gleitRechne op a b = (softFloatKernel op).apply a
      (floatAddOperand (decide (op = .sub)) Gleitkomma.f64 b) := by
  cases op with
  | add => rfl
  | sub => rfl
  | mul => rfl
  | div => exact (supported rfl).elim

theorem blockFloatArithmetic_case (op : GleitOp) (supported : op ≠ .div) {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
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
    (∀ {pr ex}, BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex
      (.float op a b low high rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, floatArithmeticBlockL_supported op supported, ← hlo0] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
  cases hc
  let σr := σ.lese Λ (a.orte ++ b.orte)
  let x := (softFloatKernel op).apply (eval σr a σr ρ).x
    (floatAddOperand (decide (op = .sub)) Gleitkomma.f64 (eval σr b σr ρ).x)
  have finiteRight : gleitEndlich (floatAddOperand (decide (op = .sub)) Gleitkomma.f64
      (eval σr b σr ρ).x) = true := by
    cases op <;> simpa [floatAddOperand, gleitEndlich, Gleitkomma.klasse_neg] using
      (eval σr b σr ρ).endlich
  have hwf : Gleitkomma.wf Gleitkomma.f64 x :=
    finiteArithmeticWf (softFloatKernel op) _ _ (eval σr a σr ρ).endlich finiteRight
  let producer := fun j => softFloatWordsL (softFloatKernel op) j (lowE (reserved := reserved) L a)
    (fun k => softAddOperandL (decide (op = .sub)) k (lowE (reserved := reserved) L b))
  have conv : ∀ fp K j code t, producer j = some (code, t) → t ≤ K →
      ∀ m pc, Pre L m pc fp K j code ρ (fun m => WeltAt m L σr) reserved →
      Ok m pc fp K j code (fun w => Gleitkomma.wf Gleitkomma.f64 x ∧
        w = BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 x)) := by
    intro fp K j code t hc ht m pc pre
    exact softFloatWordsL_ok (softFloatKernel op) (eval σr a σr ρ).x
      (floatAddOperand (decide (op = .sub)) Gleitkomma.f64 (eval σr b σr ρ).x)
      (fun j c t hc ht m pc pre => (lowE_ok σr σr (fun _ h => h) hW.lay a j c t hc ht m pc ρ pre).word trivial)
      (softAddOperandL_ok (decide (op = .sub)) (eval σr b σr ρ).x
        (fun j c t hc ht m pc pre => (lowE_ok σr σr (fun _ h => h) hW.lay b j c t hc ht m pc ρ pre).word trivial))
      hc ht pre
  simp only [floatNarrowC, List.length_append, List.length_singleton] at hs
  simp only [execBlock, gleitRechneArithmetic op supported]
  have hchoice := choice_ok (P := P) (σ0 := σ0) (ex := ex) (d := frei Γ reserved)
    (cc := cc) (ct := stopC 107 (frei Γ reserved)) (ce := ce ++ cr)
    (b := softFloatReject low high x)
    (ot := match gleitPasst low high x with
      | some v => (execBlock O passes R rest σr (Env.cons v ρ)).schrumpf
      | none => .logik .bereich)
    (oe := match gleitPasst low high x with
      | some v => (execBlock O passes R rest σr (Env.cons v ρ)).schrumpf
      | none => .logik .bereich)
    (Nat.le_refl _) (by have := hW.ks; omega) (by simpa only [List.length_append] using hs)
    hW hlo hlo0 hlo2 hpr (σ := σr) ?_ ?_ ?_
    (by simpa only [floatNarrowC, List.length_append, Int.natCast_add] using hp) hu hk hWa
  · cases hv : gleitPasst low high x <;>
      simpa only [ite_self, hv, floatNarrowC, List.length_append, Int.natCast_add] using hchoice
  · intro hpc
    have hpw := PreS.welt hpc hW.ks hWa hW.lay (by have := hW.lo; omega)
    have guard := softFloatRangeL_ok (L := L) (ρ := ρ) (W := fun m => WeltAt m L σr)
      (reserved := reserved) low high x hwf
      (fun {fp K j code t} hc ht m pc pre => (conv fp K j code t hc ht m pc pre).mono (fun _ h => h.2))
    obtain ⟨m1, st, a1, w, hw, hen⟩ := guard hcc (by omega) m pc hpw
    exact ⟨m1, st, Agree.widen a1 hW.ks, w, hw, by simpa only [bool_word] using hen⟩
  · intro rejected m' pc' hp' _ hu' hk' hw'
    rw [(softFloatReject_none hwf).mpr rejected]
    change Stops ⟨pc', fp⟩ m' 107
    exact stop_ok hp'.code hp'.far hp'.frame (by have := hW.ks; omega) hp'.small (by decide)
  · intro accepted m' pc' hp' _ hu' hk' hw'
    cases hv : gleitPasst low high x with
    | none =>
      have failed := (softFloatReject_none hwf).mp hv
      rw [accepted] at failed
      cases failed
    | some v =>
      have hvx := floatPasst_x hv
      refine bindValue_ok (L := L) (τ := .fl low high) (v := v) hW hlo hlo0 hlo2 hpr (by omega) ?_ ?_ hp' hu' hk' hw'
      · intro m pc pre
        refine Ok.value (width := rfl) ?_
        exact (conv _ _ _ _ _ he (by omega) m pc pre).mono
          (fun w hw => ⟨by simpa only [hvx] using hw.1, by simpa only [hvx] using hw.2⟩)
      · intro m pc pre hu hk hw
        exact ihRest (ex := ex) cr tr hr (by omega) (by omega) hW m pc σr _ pre hlo
          (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega) hu hk hw
          (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega)

#print axioms blockFloatArithmetic_case
end Gabbro.Stage0.Senke
