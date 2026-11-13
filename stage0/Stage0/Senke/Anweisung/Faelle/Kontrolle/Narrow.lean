/- One signed interval test for block and end-block narrowing. -/
module
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Eng
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable [Kern] {D : Deklaration}
variable {H : List D.Lock}
variable {sc : List D.Lock}

/-- Evaluate once, preserve the value, and dispatch on the outside flag. -/
theorem narrow_ok {L : Lay D} {P : Programm D} {f : D.Fn} {fp : Runner.W}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W}
    {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)}
    {reserved : Nat} {pr : List Nat} {ex : Int × Int} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {low high low' high' : Int} {e : Expr D Γ Λ (.int low high)}
    {ce cx cr : List II} {te : Nat} {σ : World D} {ρ : Env D Γ}
    {out : Ausgang (vertragVon D f) l Γ}
    (he : lowE L (reserved := reserved) e (frei Γ reserved) = some (ce, te)) (hte : te ≤ Ks)
    (hd : narrowTop (frei Γ reserved) low high low' high' ≤ Ks)
    (hs : 16 * (narrowC (frei Γ reserved) low high low' high' ce cx cr).length < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = (functionFrame P f).internalResult)
    (hlo2 : lo ≤ frei Γ reserved) (hpr : ∀ j ∈ pr, j < frei Γ reserved)
    {m : Runner.Mem} {pc : Runner.W}
    (herr : ¬ (low' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ high') →
      ∀ m' pc', PreS L m' pc' fp K (frei Γ reserved) cx ρ reserved → Umf L A C dv m' fp Ks K H →
      Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * cx.length))
        (pc' + BitVec.ofNat 64 (16 * cx.length) + BitVec.ofInt 64 (exPlus ex (cr.length + 1)).1)
        (pc' + BitVec.ofNat 64 (16 * cx.length) + BitVec.ofInt 64 (exPlus ex (cr.length + 1)).2) out reserved sc)
    (hrest : ∀ hin : low' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ high',
      ∀ m' pc', PreS L m' pc' fp K (frei (.int low' high' :: Γ) reserved) cr (Env.cons (τ := .int low' high')
        ⟨(eval σ e σ ρ).n, hin.1, hin.2⟩ ρ) reserved → Umf L A C dv m' fp Ks K H →
      Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * cr.length))
        (pc' + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.1)
        (pc' + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.2) out reserved sc)
    (hp : PreS L m pc fp K (frei Γ reserved) (narrowC (frei Γ reserved) low high low' high' ce cx cr) ρ reserved)
    (hu : Umf L A C dv m fp Ks K H) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (narrowC (frei Γ reserved) low high low' high' ce cx cr).length))
      (pc + BitVec.ofNat 64 (16 * (narrowC (frei Γ reserved) low high low' high' ce cx cr).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (narrowC (frei Γ reserved) low high low' high' ce cx cr).length) + BitVec.ofInt 64 ex.2) out reserved sc := by
  let d := frei Γ reserved
  let k := narrowWords low high low' high'
  have signedX : signedWords low high ≤ k := narrowWords_source _ _ _ _
  have wordsX : integerWords low high ≤ k :=
    Nat.le_trans (integerWords_le_signedWords _ _) signedX
  have wordsB : integerWords low' high' ≤ k :=
    Nat.le_trans (integerWords_le_signedWords _ _) (narrowWords_target _ _ _ _)
  have positive : 1 ≤ k := Nat.le_trans (integerWords_pos' low high) wordsX
  have fits : d + 5 * k + 22 ≤ Ks := hd
  have hks := hW.ks
  have hq : PreS L m pc fp K d (ce ++
      (wideExtendC (extSigned low) (integerWords low high) k d ++
      (wideOutC k d low' high' ++
      ([ci 19 (d + k + 3) (16 * (cx.length + 2)) 0] ++ cx ++
        [ci 18 (16 * (cr.length + 1)) 0 0] ++ cr)))) ρ reserved := by
    simpa only [narrowC, List.append_assoc] using hp
  have hpw := PreS.welt hq.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1, v1⟩ := lowE_ok (same := by intro _; rfl) (reserved := reserved)
    σ σ (fun _ h => h) hW.lay e d ce te he hte m pc ρ hpw
  have h1 := hq.next (Agree.widen a1 hks) (Nat.le_refl _) (by omega)
  have sourceWords := v1.2
  rw [encodeWords_int L low high (eval σ e σ ρ)] at sourceWords
  obtain ⟨m2, s2, a2, v2⟩ := wideExtend_run (extSigned low) (eval σ e σ ρ).n
    (integerWords_pos' low high) wordsX (wideFits_zahl (eval σ e σ ρ))
    h1.frame h1.small (by omega) h1.left.code h1.left.far sourceWords
  have h2 := h1.next a2 (Nat.le_refl _) (by omega)
  have fx := signedFits_zahl (eval σ e σ ρ) signedX
  have fl := signedFits_zahl (⟨low', Int.le_refl _, Int.le_refl _⟩ : Zahl low' low')
    (narrowWords_low low high low' high')
  have fh := signedFits_zahl (⟨high', Int.le_refl _, Int.le_refl _⟩ : Zahl high' high')
    (narrowWords_high low high low' high')
  obtain ⟨m3, s3, a3, v3, flag⟩ := wideOut_run low' high' (eval σ e σ ρ).n
    h2.frame h2.small (by omega) positive h2.left.code h2.left.far
    fx.1 fx.2 fl.1 fl.2 fh.1 fh.2 v2
  have h3 := h2.next a3 (Nat.le_refl _) (by omega)
  have changed := (Agree.widen a1 hks).trans (a2.trans a3)
  have hw3 : WeltAt m3 L σ :=
    weltAt_stab hW.lay (by have := hW.top; omega) m m3 hWa (changed.mono (Nat.zero_le _))
  have branch := choice_ok (sc := sc) (reserved := reserved) (P := P) (σ0 := σ0) (ex := ex)
    (cc := []) (ct := cx) (ce := cr) (d := d + k + 3)
    (b := decide (¬ (low' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ high')))
    (ot := out) (oe := out) (by omega) (by omega)
    (by rw [narrowC_length] at hs; simp only [List.length_nil]; omega) hW hlo hlo0 hlo2 hpr
    (m := m3) (σ := σ) (ρ := ρ) ?_ ?_ ?_ h3
    (hu.agreeW hW (agreeW_of changed) (by omega))
    (hk.agreeW hW (agreeW_of changed) (by omega)) hw3
  · simp only [ite_self] at branch
    refine Sim.prefix hlo (s1.trans (s2.trans s3))
      (agreeW_of (changed.mono hlo2)) (keeps_of_agreeW hW changed hpr (by omega))
      (Sim.cast branch rfl ?_ ?_ ?_)
    all_goals simp only [narrowC, d, k, List.length_append, List.length_singleton,
      List.length_nil, List.nil_append, Nat.zero_add, Nat.add_zero, Nat.mul_zero,
      Nat.mul_add, BitVec.ofNat_add, BitVec.add_zero, BitVec.add_assoc]
  · intro _
    refine ⟨m3, by simpa using Star.refl _ m3, Agree.refl _ _ _ _, _, flag, ?_⟩
    have equivalent : ((eval σ e σ ρ).n < low' ∨ high' < (eval σ e σ ρ).n) ↔
        ¬ (low' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ high') := by omega
    simp only [Runner.IR.bool, equivalent]
  · intro hout m' pc' hp' _ hu' hk' hw'
    exact herr (of_decide_eq_true hout) m' pc' hp' hu' hk' hw'
  · intro hin m' pc' hp' keep hu' hk' hw'
    have inside : low' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ high' := by
      have := of_decide_eq_false hin
      exact Classical.byContradiction this
    have value : ValueAt L m' fp d (.int low' high')
        ⟨(eval σ e σ ρ).n, inside.1, inside.2⟩ :=
      valueAt_int_of_wide _ wordsB (v3.agree_low keep h3.frame.room
        (by rw [integerEncoding_length]; omega) (by omega))
    have pre : PreS L m' pc' fp K (frei (.int low' high' :: Γ) reserved) cr
        (Env.cons (τ := .int low' high') ⟨(eval σ e σ ρ).n, inside.1, inside.2⟩ ρ) reserved :=
      { hp' with
        ctx := by simp only [frei, contextWords_cons, valueWords]; omega
        env := envAt_cons hp'.env value }
    exact hrest inside m' pc' pre hu' hk' hw'

end Gabbro.Stage0.Senke
