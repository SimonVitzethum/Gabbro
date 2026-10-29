/- One signed interval test for block and end-block narrowing. -/
import Stage0.Senke.Anweisung.Faelle.Check
import Stage0.Senke.Ausdruck.Eng

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration}

/-- Evaluate once, preserve the value, and dispatch on the outside flag. -/
theorem narrow_ok {L : Lay D} {P : Programm D} {f : D.Fn} {fp : Runner.W}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W}
    {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)}
    {pr : List Nat} {ex : Int × Int} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {low high low' high' : Int} {e : Expr D Γ Λ (.int low high)}
    {ce cx cr : List II} {te : Nat} {σ : World D} {ρ : Env D Γ}
    {out : Ausgang (vertragVon D f) l Γ}
    (he : lowE L e (frei Γ) = some (ce, te)) (hte : te ≤ Ks)
    (hw : inW low high = true) (hl : lit32 low' = true) (hh : lit32 high' = true)
    (hd : frei Γ + 3 ≤ Ks)
    (hs : 16 * (narrowC (frei Γ) low' high' ce cx cr).length < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = FB + (D.params f).length)
    (hlo2 : lo ≤ frei Γ) (hpr : ∀ j ∈ pr, j < frei Γ)
    {m : Runner.Mem} {pc : Runner.W}
    (herr : ¬ (low' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ high') →
      ∀ m' pc', PreS L m' pc' fp K (frei Γ) cx ρ → Umf L A C dv m' fp Ks K →
      Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * cx.length))
        (pc' + BitVec.ofNat 64 (16 * cx.length) + BitVec.ofInt 64 (exPlus ex (cr.length + 1)).1)
        (pc' + BitVec.ofNat 64 (16 * cx.length) + BitVec.ofInt 64 (exPlus ex (cr.length + 1)).2) out)
    (hrest : ∀ hin : low' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ high',
      ∀ m' pc', PreS L m' pc' fp K (frei Γ + 1) cr (Env.cons (τ := .int low' high')
        ⟨(eval σ e σ ρ).n, hin.1, hin.2⟩ ρ) → Umf L A C dv m' fp Ks K →
      Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * cr.length))
        (pc' + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.1)
        (pc' + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.2) out)
    (hp : PreS L m pc fp K (frei Γ) (narrowC (frei Γ) low' high' ce cx cr) ρ)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (narrowC (frei Γ) low' high' ce cx cr).length))
      (pc + BitVec.ofNat 64 (16 * (narrowC (frei Γ) low' high' ce cx cr).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (narrowC (frei Γ) low' high' ce cx cr).length) + BitVec.ofInt 64 ex.2) out := by
  have hks := hW.ks
  have hq : PreS L m pc fp K (frei Γ) (ce ++ (engTest (frei Γ) low' high' ++
      [ci 19 (frei Γ + 1) (16 * (cx.length + 2)) 0] ++ cx ++ [ci 18 (16 * (cr.length + 1)) 0 0] ++ cr)) ρ := hp
  have hpw := PreS.welt hq.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, r1, hen⟩ := lowE_ok σ σ (fun _ h => h) e _ ce te he hte m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hn := hq.next a1 (Nat.le_refl _) (by omega)
  have hw1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
  have hx := inW_spec hw (eval σ e σ ρ).lo_le (eval σ e σ ρ).le_hi
  have hlW : -2^63 ≤ low' ∧ low' < 2^63 := by
    simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at hl; omega
  have hhW : -2^63 ≤ high' ∧ high' < 2^63 := by
    simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at hh; omega
  have hsim : Sim L P f σ0 ρ0 rp cfp fp lo K pr
      ⟨pc + BitVec.ofNat 64 (16 * ce.length), fp⟩ m1
      (pc + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofNat 64 (16 *
        (engTest (frei Γ) low' high' ++ [ci 19 (frei Γ + 1) (16 * (cx.length + 2)) 0] ++ cx ++
          [ci 18 (16 * (cr.length + 1)) 0 0] ++ cr).length))
      (pc + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofNat 64 (16 *
        (engTest (frei Γ) low' high' ++ [ci 19 (frei Γ + 1) (16 * (cx.length + 2)) 0] ++ cx ++
          [ci 18 (16 * (cr.length + 1)) 0 0] ++ cr).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofNat 64 (16 *
        (engTest (frei Γ) low' high' ++ [ci 19 (frei Γ + 1) (16 * (cx.length + 2)) 0] ++ cx ++
          [ci 18 (16 * (cr.length + 1)) 0 0] ++ cr).length) + BitVec.ofInt 64 ex.2) out := by
    have hs' : 16 * ((engTest (frei Γ) low' high').length + 1 + cx.length + 1 + cr.length) < 2 ^ 31 := by
      simp only [narrowC, List.length_append, List.length_singleton] at hs; omega
    have hc := choice_ok (P := P) (σ0 := σ0) (ex := ex) (d := frei Γ + 1)
      (b := decide (¬ (low' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ high')))
      (ot := out) (oe := out) (by omega) (by omega) hs' hW hlo hlo0 hlo2 hpr
      (m := m1) (σ := σ) (ρ := ρ) ?_ ?_ ?_ hn
      (hu.agreeW hW (agreeW_of a1) (by omega)) (hk.agreeW hW (agreeW_of a1) (by omega)) hw1
    · simpa only [ite_self, Int.natCast_add, Int.natCast_one] using hc
    · intro hpc
      obtain ⟨m2, s2, a2, w2, r2, hen2⟩ := eng_test_ok
        { hpc with ctx := by have := hp.ctx; omega } (by omega) hl hh r1
      refine ⟨m2, s2, a2, w2, r2, ?_⟩
      simp only [Enc] at hen
      subst w
      rw [hen2, slt_in hx hlW, slt_in hhW hx]
      by_cases hin : low' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ high'
      · have h1 : ¬ (eval σ e σ ρ).n < low' := by omega
        have h2 : ¬ high' < (eval σ e σ ρ).n := by omega
        simp [Runner.IR.bool, hin, h1, h2]
      · have hout : (eval σ e σ ρ).n < low' ∨ high' < (eval σ e σ ρ).n := by omega
        simp [Runner.IR.bool, hin, hout]
    · intro hout m' pc' hp' _ hu' hk' hw'
      exact herr (of_decide_eq_true hout) m' pc' hp' hu' hk' hw'
    · intro hin m' pc' hp' a2 hu' hk' hw'
      have hin' : low' ≤ (eval σ e σ ρ).n ∧ (eval σ e σ ρ).n ≤ high' := by
        have := of_decide_eq_false hin; exact Classical.byContradiction this
      have rv : m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some w := by
        rw [agree_rd_low a2 hn.frame.room (by omega) (by omega)]; exact r1
      have hp'2 : PreS L m' pc' fp K (frei Γ + 1) cr
          (Env.cons (τ := .int low' high') ⟨(eval σ e σ ρ).n, hin'.1, hin'.2⟩ ρ) :=
        { hp' with ctx := by simp only [frei, List.length_cons]; omega
                   env := envAt_cons hp'.env rv (by exact hen) }
      exact hrest hin' m' pc' hp'2 hu' hk' hw'
  refine Sim.prefix hlo s1 (agreeW_of (a1.mono hlo2))
    (keeps_of_agreeW hW a1 hpr (by omega)) (Sim.cast hsim rfl ?_ ?_ ?_)
  all_goals simp only [narrowC, List.length_append, List.length_singleton, Nat.mul_add,
    BitVec.ofNat_add, BitVec.add_assoc]

end Gabbro.Stage0.Senke
