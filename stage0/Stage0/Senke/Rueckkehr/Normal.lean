/- Evaluate the complete result, check ensures, then publish through the shared ABI. -/
module
public import Stage0.Senke.Rueckkehr.Publish
public import Stage0.Senke.Rueckkehr.Epilogue
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

theorem ret_ok0 {P : Programm D} {f : D.Fn} {fp : Runner.W} {K lo reserved : Nat}
    {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)}
    {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f
      (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {Γ : Ctx} {Λ : List (Res D)} (e : ErgExpr D Γ Λ (vertragVon D f).erg)
    {ce : List II} {te : Nat}
    (he : lowErg L e (frei Γ reserved) reserved = some (ce, te))
    (hK : max te (max tens (retTop (functionFrame P f))) ≤ K)
    (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved)
      (ce ++ retC (functionFrame P f) (frei Γ reserved) cens) ρ reserved)
    (hlo : lo ≤ frei Γ reserved) (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ) (hl : LayIn L) (hwl : fp.toNat + 8 * K ≤ L.lo) :
    RetZ0 L P f σ0 ρ0 fp K rp cfp ⟨pc, fp⟩ m (σ.lese Λ e.orte)
      (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  let layout := functionFrame P f
  let flag := lo + returnWords (D.erg f) (D.gruende f)
  have result : layout.result = D.erg f := rfl
  have internal : layout.internalResult = lo := hlo0.symm
  have status : layout.internalStatus = flag := by
    simp only [FrameLayout.internalStatus, internal, FrameLayout.returnSpan]
    rfl
  have parameterEnd : frei (D.params f) layout.ensReserved = lo := internal
  have lower : 4 ≤ lo := by
    rw [hlo0]
    simp only [functionFrame, FrameLayout.internalResult, FrameLayout.ensParams,
      FrameLayout.ensReserved, FrameLayout.parameterWords, FB]
    omega
  have area := resultWords_le_returnWords (D.erg f) (D.gruende f)
  have positive := resultWords_pos (D.erg f)
  have small := hp.small
  have topPublish : retTop layout ≤ K :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hK)
  have topReturn : flag + 8 ≤ K := by
    simpa only [retTop, status] using topPublish
  have hspan := lowErg_span (reserved := reserved) e _ _ _ he
  have hpw := PreS.welt hp.left (Nat.le_refl K) hWa hl hwl
  obtain ⟨m1, s1, a1, value1⟩ := lowErg_ok (same := rfl) (reserved := reserved)
    (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) hl e _ ce te he (by omega) m pc ρ hpw
  have world1 := hpw.wstab m m1 hWa (a1.mono (Nat.zero_le _))
  have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
  change PreS L m1 _ fp K (frei Γ reserved) (retC layout (frei Γ reserved) cens) ρ reserved at hp1
  have hq : PreS L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (frei Γ reserved)
      (copyWords (resultWords (D.erg f)) lo (frei Γ reserved) ++
        (cens ++ publishC layout)) ρ reserved := by
    simpa only [retC, result, internal, status, List.append_assoc] using hp1
  obtain ⟨m2, s2, a2exact, value2⟩ := copyResult_run (L := L) hq.frame hp.small
    (by omega) (by simpa only [resultWords_vertragVon] using (show frei Γ reserved + resultWords (vertragVon D f).erg ≤ K by omega))
    (Or.inl hlo) (codeAt_left hq.code)
    (by simpa only [copyWords_length] using hq.left.far) value1
  have a2 : Agree fp lo K m1 m2 := Agree.widen a2exact (by omega)
  have frame2 := hq.frame.agree a2
  have far2 := codeFar_tail (a := copyWords (resultWords (D.erg f)) lo (frei Γ reserved)) hq.far
  have code2 := (codeAt_right hq.code).agree a2 far2
  simp only [copyWords_length] at code2 far2
  have kept2 := hk.agree ((a1.mono hlo).trans a2) hp.frame (by omega)
  have world2 := weltAt_stab hl hwl m1 m2 world1 (a2.mono (Nat.zero_le _))
  have contextSize := frei_ergCtx (D.params f) layout.ensReserved (D.erg f)
  rw [parameterEnd] at contextSize
  have ensEnv := envAt_ergEnv kept2.env (by rw [parameterEnd]; exact value2)
  have ensPre : PreS L m2 _ fp K flag cens
      (ergEnv (D.erg f) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ0)
      layout.ensReserved :=
    ⟨by omega, hp.small, frame2, codeAt_left code2,
      codeFar_left (by rw [← List.length_append]; exact far2), ensEnv, trivial, wstab_true _ _⟩
  have postRun := lowPost_ok P f σ0 (σ.lese Λ e.orte) ρ0
    (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)
    hens (by omega) (by simp only [FB]; omega) hl hwl m2 _ ensPre world2 kept2.entry
  simp only [RetZ0]
  split
  · next failed =>
    rw [if_pos failed] at postRun
    exact Stops.prefix (s1.trans s2) postRun
  · next restored =>
    rw [if_neg restored] at postRun
    obtain ⟨m3, s3, a3⟩ := postRun
    have frame3 := frame2.agree a3
    have far3 := codeFar_tail (a := cens) far2
    have code3 := (codeAt_right code2).agree a3 far3
    have value3 := value2.agree a3 frame2 (by omega) (by omega)
    have kept3 := kept2.agree a3 frame2 (by omega)
    obtain ⟨m4, published, changed, returned, mirror, normal⟩ :=
      publishResult_run layout frame3 hp.small topPublish code3 far3
        (by rw [internal]; exact value3) kept3.r0 kept3.r1
    refine ⟨m4, s1.trans (s2.trans (s3.trans published)),
      (a1.mono (by omega)).trans ((a2.mono (by omega)).trans ((a3.mono (by omega)).trans changed)),
      returned, mirror, normal⟩

/-- The local return writes below Ks, preserving the world above the complete frame. -/
theorem ret_ok {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo reserved : Nat}
    {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f
      (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {Γ : Ctx} {Λ : List (Res D)} (e : ErgExpr D Γ Λ (vertragVon D f).erg)
    {ce : List II} {te : Nat}
    (he : lowErg L e (frei Γ reserved) reserved = some (ce, te))
    (hK : max te (max tens (retTop (functionFrame P f))) ≤ Ks)
    (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved)
      (ce ++ retC (functionFrame P f) (frei Γ reserved) cens) ρ reserved)
    (hlo : lo ≤ frei Γ reserved)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) :
    RetZ L P f σ0 ρ0 fp K rp cfp ⟨pc, fp⟩ m (σ.lese Λ e.orte)
      (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  have hks := hW.ks
  have hpS : PreS L m pc fp Ks (frei Γ reserved)
      (ce ++ retC (functionFrame P f) (frei Γ reserved) cens) ρ reserved :=
    ⟨hp.ctx, by have := hp.small; omega, frameOK_sub hp.frame hks, hp.code,
      codeFar_sub2 hp.far hks, hp.env, trivial, wstab_true _ _⟩
  have hkS : Kopf L f m fp Ks rp cfp ρ0 P σ0 := by
    refine ⟨hk.r0, hk.r1, hk.env, ?_, hk.entry⟩
    have := hK
    simp only [retTop, FrameLayout.internalStatus] at this
    omega
  have run := ret_ok0 (σ0 := σ0) hlo0 hens e he hK m pc σ ρ hpS hlo hkS hWa hW.lay hW.lo
  simp only [RetZ0] at run
  simp only [RetZ]
  split
  · next h => rw [if_pos h] at run; exact run
  · next h =>
    rw [if_neg h] at run
    obtain ⟨m', steps, changed, result⟩ := run
    exact ⟨m', steps, agreeW_of (Agree.widen changed hks), result,
      owedWorld_at P f _ m'
        (weltAt_stab hW.lay hW.lo m m' hWa (changed.mono (Nat.zero_le _)))⟩

end Gabbro.Stage0.Senke
