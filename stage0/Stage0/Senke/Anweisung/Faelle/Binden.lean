/- One binding continuation for expression values and precomputed literals. -/
import Stage0.Senke.Anweisung.Faelle.Kontext
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem bindValue_ok {P : Programm D} {f : D.Fn} {fp : Runner.W}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W}
    {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)}
    {pr : List Nat} {ex : Int × Int} {l : Bool} {Γ : Ctx} {τ : Ty} {ρ : Env D Γ}
    {σ : World D} {v : Wert D τ} {ce cr : List II} {out : Ausgang (vertragVon D f) l (τ :: Γ)}
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = FB + (D.params f).length) (hlo2 : lo ≤ frei Γ) (hpr : ∀ j ∈ pr, j < frei Γ)
    (hd : frei Γ < Ks)
    (hcode : ∀ m pc, Pre L m pc fp Ks (frei Γ) ce ρ (fun m => WeltAt m L σ) →
      Ok m pc fp Ks (frei Γ) ce (Enc L τ v))
    (hrest : ∀ m' pc', PreS L m' pc' fp K (frei Γ + 1) cr (Env.cons v ρ) →
      Umf L A C dv m' fp Ks K → Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * cr.length))
        (pc' + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.1)
        (pc' + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.2) out)
    {m : Runner.Mem} {pc : Runner.W} (hp : PreS L m pc fp K (frei Γ) (ce ++ cr) ρ)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * (ce ++ cr).length))
      (pc + BitVec.ofNat 64 (16 * (ce ++ cr).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (ce ++ cr).length) + BitVec.ofInt 64 ex.2) out.schrumpf := by
  have hks := hW.ks
  have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw, hen⟩ := hcode m pc hpw
  have a1 := Agree.widen a1s hks
  have hf := codeFar_right (n := ce.length) (k := cr.length) (by simpa using hp.far)
  have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (frei Γ + 1) cr (Env.cons v ρ) :=
    ⟨by simp only [frei, List.length_cons]; omega, hp.small, hp.frame.agree a1,
     (codeAt_right hp.code).agree a1 hf, hf,
     envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) hw hen, trivial, wstab_true _ _⟩
  have ih := hrest m1 _ hp1 (hu.agreeW hW (agreeW_of (a1.mono hlo2)) hlo)
    (hk.agreeW hW (agreeW_of (a1.mono hlo2)) (by omega))
    (hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _)))
  rw [pc_add1]
  exact Sim.prefix hlo s1 (agreeW_of (a1.mono hlo2))
    (keeps_of_agreeW hW a1 hpr (by omega)) (Sim.schrumpf ih)

end Gabbro.Stage0.Senke
