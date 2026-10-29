/-
  Subject: Indirect calls and their continuations, sharing the direct call's frame proof.
-/
import Stage0.Senke.Anweisung.Simulation

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Transport of the context preserves every encoded variable. -/
theorem envAt_cast {ts us : Ctx} (e : ts = us) {m : Runner.Mem} {fp : Runner.W} {ρ : Env D ts}
    (h : EnvAt L m fp ρ) : EnvAt L m fp ((congrArg (Env D) e).mp ρ) := by cases e; exact h

/-- Reindexing the parameter environment changes no value word or frame slot. -/
theorem envAt_umsig {f : D.Fn} {n : Nat} (hf : D.passt f n = true) {m : Runner.Mem} {fp : Runner.W}
    {ρ : Env D (D.sigNr n).params} (h : EnvAt L m fp ρ) : EnvAt L m fp (umsig hf ρ) := by
  exact envAt_cast (show (D.sigNr n).params = D.params f from (D.passt_sig hf).params.symm) h

/-- An indirect call evaluates the pointer and arguments once, resolves its signature witness,
    and invokes the same callee specification as a direct call. -/
theorem lowInd_ok {A : D.Fn → Nat} {C : D.Fn → List II}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {dv : Runner.W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {Λ : List (Res D)} {Γ : Ctx} {n : Nat} (p : Expr D Γ Λ (.fnptr n))
    (args : Args D Γ Λ (D.sigNr n).params) (σ₀ σ : World D) {c : List II} {top : Nat}
    {m : Runner.Mem} {pc fp : Runner.W} {K Ks : Nat} {ρ : Env D Γ}
    (hc : lowInd L p args = some (c, top)) (ht : top + cap ≤ Ks)
    (hp : PreS L m pc fp K (frei Γ) c ρ) (hu : Umf L A C dv m fp Ks K)
    (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) :
    let v := eval σ₀ p σ ρ
    match R v.1 σ (umsig v.2 (evalArgs σ₀ args σ ρ)) with
    | .ok σ' r => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
        AgreeW L fp (frei Γ) K m m' ∧
        (∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ + 2))) = some w ∧ EncErg L (D.erg v.1) r w) ∧
        WeltAt m' L σ'
    | .logik e => Stops ⟨pc, fp⟩ m (logikCode e)
    | .hardware h => Stops ⟨pc, fp⟩ m (hwCode h)
    | _ => False := by
  simp only [lowInd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨⟨cp, tp⟩, hcp, ⟨ca, ta⟩, hca, rfl, rfl⟩ := hc
  simp only [indTop] at ht
  have hFB3 : FB = 3 := rfl
  have hks := hW.ks
  have hFB : FB ≤ frei Γ := by simp only [frei]; omega
  have hpar := (D.passt_sig (eval σ₀ p σ ρ).2).params
  change D.params (eval σ₀ p σ ρ).1 = (D.sigNr n).params at hpar
  have hp0 : PreS L m pc fp K (frei Γ) (cp ++ (ca ++ callTailN (D.sigNr n).params.length 0 (frei Γ) true)) ρ := hp
  have hpw := PreS.welt hp0.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw, he⟩ := lowE_ok σ₀ σ (fun _ h => h) p _ cp tp hcp (by omega) m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hp1 := hp0.next (d' := frei Γ + FB) a1 (by omega) (by omega)
  have hpw1 := PreS.welt hp1.left hks (hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))) hW.lay (by have := hW.lo; omega)
  obtain ⟨m2, s2, a2s, e2⟩ := lowA_ok (F := frei Γ) σ₀ σ (fun _ h => h) args ca ta hca (by omega) (by omega) m1 _ ρ hpw1
  have a2 := Agree.widen a2s hks
  have hp2 := hp1.next a2 (Nat.le_refl _) (by omega)
  have hWa2 := hpw1.wstab m1 m2 hpw1.welt (a2s.mono (Nat.zero_le _))
  have hu2 := (hu.agree a1 hp.frame (by omega)).agree a2 hp1.frame (by omega)
  have htail : callTailN (D.sigNr n).params.length 0 (frei Γ) true =
      callTail A (eval σ₀ p σ ρ).1 (frei Γ) true := by simp only [callTail, callTailN, hpar, ↓reduceIte]
  rw [htail] at hp2
  have hr : m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 (A (eval σ₀ p σ ρ).1)) := by
    rw [agree_rd_low a2 hp1.frame.room (by omega) (by omega), hw]
    simp only [Enc, hS.addr] at he
    exact congrArg some he
  have hc2 := call_ok (indirect := true) (f := (eval σ₀ p σ ρ).1) (F := frei Γ) (Ks := Ks) hS hp2.code (by exact hp2.far) hp2.frame hp.small hFB
    (by rw [hpar]; omega) (by omega) (hA _) hu2.code hu2.depth (envAt_umsig (eval σ₀ p σ ρ).2 e2) hW hWa2 hu2.sync (fun _ => hr)
  dsimp only
  generalize R (eval σ₀ p σ ρ).1 σ (umsig (eval σ₀ p σ ρ).2 (evalArgs σ₀ args σ ρ)) = o at hc2 ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m3, s3, a3, w3, hw3⟩ := hc2
    refine ⟨m3, s1.trans (s2.trans ?_), (agreeW_of a1).trans ((agreeW_of (a2.mono (by omega))).trans a3), w3, hw3⟩
    simpa only [indC, List.length_append, callTail, callTailN, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_assoc, pc_add] using s3
  | logik e => exact Stops.prefix s1 (Stops.prefix s2 hc2)
  | hardware e => exact Stops.prefix s1 (Stops.prefix s2 hc2)
  | why _ _ => exact hc2.elim

end Gabbro.Stage0.Senke
