/-
  Subject: Fallible indirect calls (`callIndElse`, `bindCallIndElse`): the indirect
  dispatch of `lowInd` for signatures with a reason channel, joined with the
  else-branch handling of the direct fallible call.
-/
module
public import Stage0.Senke.Anweisung.Faelle.Kontext
public import Stage0.Senke.Anweisung.SchleifeTeile
public import Stage0.Senke.Anweisung.Bindung.Fnptr
public import Stage0.Senke.Anweisung.Faelle.CallElse
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
variable [Kern] {D : Deklaration} {L : Lay D}
variable {H : List D.Lock}

/-- Every fallible indirect call reserves the callee header, arguments and target temporary. -/
theorem lowIndElse_top {Λ : List (Res D)} {Γ : Ctx} {n : Nat} {p : Expr D Γ Λ (.fnptr n)}
    {args : Args D Γ Λ (D.sigNr n).params} {reserved : Nat} {c : List II} {top : Nat}
    (h : lowIndElse L p args reserved = some (c, top)) : frei Γ reserved + FB + (contextWords (D.sigNr n).params) + 1 ≤ top := by
  simp only [lowIndElse] at h
  split at h
  rotate_left
  · cases h
  next hr =>
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨cp, tp⟩, _, ⟨ca, ta⟩, _, _, rfl⟩ := h
  simp only [indTop]; omega

/-- A fallible indirect call evaluates the pointer and arguments once, resolves its
    signature witness, and invokes the same callee specification as a direct call --
    with both the value and the reason outcome. Mirrors `lowInd_ok`. -/
theorem lowIndElse_ok {A : D.Fn → Nat} {C : D.Fn → List II}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {reserved : Nat} {dv : Runner.W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {Λ : List (Res D)} {Γ : Ctx} {n : Nat} (p : Expr D Γ Λ (.fnptr n))
    (args : Args D Γ Λ (D.sigNr n).params) (σ₀ σ : World D) {same : σ₀ = σ} {c : List II} {top : Nat}
    {m : Runner.Mem} {pc fp : Runner.W} {K Ks : Nat} {ρ : Env D Γ}
    (hc : lowIndElse L p args reserved = some (c, top)) (ht : top + cap ≤ Ks)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved) (hu : Umf L A C dv m fp Ks K H)
    (hW : WIn L fp Ks K) (hWa : WeltAt m L σ)
    (hHs : HeldIn H (Signatur.anfang D (D.sigNr n)) (D.sigNr n).boden) :
    let v := eval σ₀ p σ ρ
    match R v.1 σ (umsig v.2 (evalArgs σ₀ args σ ρ)) with
    | .ok σ' r => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
        AgreeW L fp (frei Γ reserved) K m m' ∧
        (ResultAt L m' (slot fp (BitVec.ofNat 64 (frei Γ reserved)))
            (FB + contextWords (D.params v.1)) (D.erg v.1) r ∧
          ReturnMirror m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (FB + contextWords (D.params v.1)) ∧
          ReturnFlag m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (contextWords (D.params v.1)) true
            (returnWords (D.erg v.1) (D.gruende v.1))) ∧
        WeltAt m' L σ'
    | .why σ' r => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
        AgreeW L fp (frei Γ reserved) K m m' ∧
        (ValueAt L m' (slot fp (BitVec.ofNat 64 (frei Γ reserved)))
            (FB + contextWords (D.params v.1)) (.why (D.gruende v.1)) r ∧
          ReturnMirror m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (FB + contextWords (D.params v.1)) ∧
          ReturnFlag m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (contextWords (D.params v.1)) false
            (returnWords (D.erg v.1) (D.gruende v.1))) ∧
        WeltAt m' L σ'
    | .logik e => Stops ⟨pc, fp⟩ m (logikCode e)
    | .hardware h => Stops ⟨pc, fp⟩ m (hwCode h) := by
  simp only [lowIndElse] at hc
  split at hc
  rotate_left
  · cases hc
  next hzero =>
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨⟨cp, tp⟩, hcp, ⟨ca, ta⟩, hca, rfl, rfl⟩ := hc
  simp only [indTop] at ht
  have hFB3 : FB = 4 := rfl
  have hks := hW.ks
  have hFB : FB ≤ frei Γ reserved := by simp only [frei]; omega
  have hpar := (D.passt_sig (eval σ₀ p σ ρ).2).params
  change D.params (eval σ₀ p σ ρ).1 = (D.sigNr n).params at hpar
  have hp0 : PreS L m pc fp K (frei Γ reserved) (cp ++ (ca ++ callTailN (contextWords (D.sigNr n).params) 0 (frei Γ reserved) true)) ρ reserved := hp
  have hpw := PreS.welt hp0.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw, he⟩ := lowE_ok (same := by intro _; exact same) σ₀ σ (fun _ h => h) hW.lay p _ cp tp hcp (by omega) m pc ρ hpw |>.word trivial
  have a1 := Agree.widen a1s hks
  have hp1 := hp0.next (d' := frei Γ reserved + FB) a1 (by omega) (by omega)
  have hpw1 := PreS.welt hp1.left hks (hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))) hW.lay (by have := hW.lo; omega)
  obtain ⟨m2, s2, a2s, e2⟩ := lowA_ok (same := same) (F := frei Γ reserved) σ₀ σ (fun _ h => h) hW.lay args ca ta hca (by omega) (by omega) m1 _ ρ hpw1
  have a2 := Agree.widen a2s hks
  have hp2 := hp1.next a2 (Nat.le_refl _) (by omega)
  have hWa2 := hpw1.wstab m1 m2 hpw1.welt (a2s.mono (Nat.zero_le _))
  have hu2 := (hu.agree a1 hp.frame (by omega)).agree a2 hp1.frame (by omega)
  have htail : callTailN (contextWords (D.sigNr n).params) 0 (frei Γ reserved) true =
      callTail A (eval σ₀ p σ ρ).1 (frei Γ reserved) true := by simp only [callTail, callTailN, hpar, ↓reduceIte]
  rw [htail] at hp2
  have hr : m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some (BitVec.ofNat 64 (A (eval σ₀ p σ ρ).1)) := by
    rw [agree_rd_low a2 hp1.frame.room (by omega) (by omega), hw]
    simp only [Enc, hS.addr] at he
    exact congrArg some he
  have hc2 := call_ok (indirect := true) (f := (eval σ₀ p σ ρ).1) (F := (frei Γ reserved)) (Ks := Ks) hS hp2.code (by exact hp2.far) hp2.frame hp.small hFB
    (by rw [hpar]; omega) (by omega) (hA _) hu2.code hu2.depth (envAt_umsig (eval σ₀ p σ ρ).2 e2) hW hWa2 hu2.sync
    (hHs.passt (D.passt_sig (eval σ₀ p σ ρ).2)) (fun _ => hr)
  dsimp only
  generalize R (eval σ₀ p σ ρ).1 σ (umsig (eval σ₀ p σ ρ).2 (evalArgs σ₀ args σ ρ)) = o at hc2 ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m3, s3, a3, result, hw3⟩ := hc2
    refine ⟨m3, s1.trans (s2.trans ?_), (agreeW_of a1).trans ((agreeW_of (a2.mono (by omega))).trans a3), result, hw3⟩
    simpa only [indC, List.length_append, callTail, callTailN, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_assoc, pc_add] using s3
  | why σ' r =>
    obtain ⟨m3, s3, a3, value, mirror, flag, hw3⟩ := hc2
    refine ⟨m3, s1.trans (s2.trans ?_), (agreeW_of a1).trans ((agreeW_of (a2.mono (by omega))).trans a3), ⟨value, mirror, flag⟩, hw3⟩
    simpa only [indC, List.length_append, callTail, callTailN, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_assoc, pc_add] using s3
  | logik e => exact Stops.prefix s1 (Stops.prefix s2 hc2)
  | hardware e => exact Stops.prefix s1 (Stops.prefix s2 hc2)

/-- Reindex a complete reason value at an equal channel size, preserving its encoding. -/
private theorem valueAt_why_cast {a b : Nat} (h : a = b) {r : Fin a}
    {m : Runner.Mem} {fp : Runner.W} {base : Nat}
    (value : ValueAt L m fp base (.why a) r) :
    ValueAt L m fp base (.why b) (Fin.cast h r) := by
  cases h
  exact value

/-- A fallible indirect call followed by the common binder reaches precisely the
    continuation selected by G. Mirrors `callElse_ok` with the indirect dispatch. -/
theorem callIndElse_ok {A : D.Fn → Nat} {C : D.Fn → List II}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {dv : Runner.W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {reserved : Nat} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ)
    {cc cr ce : List II} {ta : Nat} {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem}
    {ρ : Env D Γ} (σ : World D)
    (hcc : lowIndElse L p args reserved = some (cc, ta))
    (ht : max ta (frei Γ reserved + FB + (contextWords (D.sigNr n).params) + returnWords (D.sigNr n).erg (D.sigNr n).gruende + 1) + cap ≤ Ks)
    (hp : PreS L m pc fp K (frei Γ reserved)
      (elseC (D.sigNr n) (frei Γ reserved) cc cr ce) ρ reserved)
    (hs : 16 * (elseC (D.sigNr n) (frei Γ reserved) cc cr ce).length < 2 ^ 31)
    (hu : Umf L A C dv m fp Ks K H) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ)
    (hHs : HeldIn H (Signatur.anfang D (D.sigNr n)) (D.sigNr n).boden) :
    (∃ σ' v m2, R (eval σ p σ ρ).1 σ (umsig (eval σ p σ ρ).2 (evalArgs σ args σ ρ)) = .ok σ' v ∧
      Star ⟨pc, fp⟩ m ⟨callBranchPC pc cc cr (returnWords (D.sigNr n).erg (D.sigNr n).gruende) true, fp⟩ m2 ∧
      AgreeW L fp (frei Γ reserved) K m m2 ∧
      PreS L m2 (callBranchPC pc cc cr (returnWords (D.sigNr n).erg (D.sigNr n).gruende) true) fp K (frei (τ :: Γ) reserved) cr (.cons (ergWert (ergSig (eval σ p σ ρ).2 he) v) ρ) reserved ∧ WeltAt m2 L σ') ∨
    (∃ σ' r m2, R (eval σ p σ ρ).1 σ (umsig (eval σ p σ ρ).2 (evalArgs σ args σ ρ)) = .why σ' r ∧
      Star ⟨pc, fp⟩ m ⟨callBranchPC pc cc cr (returnWords (D.sigNr n).erg (D.sigNr n).gruende) false, fp⟩ m2 ∧
      AgreeW L fp (frei Γ reserved) K m m2 ∧
      PreS L m2 (callBranchPC pc cc cr (returnWords (D.sigNr n).erg (D.sigNr n).gruende) false) fp K (frei (.why (D.sigNr n).gruende :: Γ) reserved) ce (Env.cons (τ := .why (D.sigNr n).gruende) (grundSig (eval σ p σ ρ).2 r) ρ) reserved ∧ WeltAt m2 L σ') ∨
    (∃ e, R (eval σ p σ ρ).1 σ (umsig (eval σ p σ ρ).2 (evalArgs σ args σ ρ)) = .logik e ∧ Stops ⟨pc, fp⟩ m (logikCode e)) ∨
    (∃ e, R (eval σ p σ ρ).1 σ (umsig (eval σ p σ ρ).2 (evalArgs σ args σ ρ)) = .hardware e ∧ Stops ⟨pc, fp⟩ m (hwCode e)) := by
  have hpc : PreS L m pc fp K (frei Γ reserved) (cc ++
      (receiveC (D.sigNr n) (frei Γ reserved) ++ [ci 19 (frei Γ reserved + FB + (contextWords (D.sigNr n).params) + returnWords (D.sigNr n).erg (D.sigNr n).gruende) (16 * (cr.length + 2)) 0] ++
      cr ++ [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce)) ρ reserved := by
    simpa only [Deklaration.params, Deklaration.erg, Deklaration.gruende, elseC, List.append_assoc, Int.natCast_add, Int.ofNat_one] using hp
  have hc := lowIndElse_ok (same := rfl) hS hA p args σ σ hcc (by omega) hpc.left hu hW hWa hHs
  generalize pointerEq : eval σ p σ ρ = pointer at hc ⊢
  obtain ⟨f, hf⟩ := pointer
  dsimp only at hc ⊢
  generalize R f σ (umsig hf (evalArgs σ args σ ρ)) = o at hc ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m1, sx, ax, ⟨result, mirror, flag⟩, hw1⟩ := hc
    have hsig : D.params f = (D.sigNr n).params := (D.passt_sig hf).params
    have herg : D.erg f = (D.sigNr n).erg := (D.passt_sig hf).erg
    have hgru : D.gruende f = (D.sigNr n).gruende := (D.passt_sig hf).gruende
    have mirror' : ReturnMirror m1 (slot fp (BitVec.ofNat 64 (frei Γ reserved)))
        (FB + contextWords (D.sigNr n).params) := by
      simpa only [hsig] using mirror
    have flag' : ReturnFlag m1 (slot fp (BitVec.ofNat 64 (frei Γ reserved)))
        (contextWords (D.sigNr n).params) true
        (returnWords (D.sigNr n).erg (D.sigNr n).gruende) := by
      simpa only [hsig, herg, hgru] using flag
    have hval' : ValueAt L m1 (slot fp (BitVec.ofNat 64 (frei Γ reserved)))
        (FB + contextWords (D.sigNr n).params) τ (ergWert (ergSig hf he) v) := by
      simpa only [hsig] using resultAt_wert (ergSig hf he) result
    obtain ⟨m2, sx2, ax2, hp2, hw2⟩ := callBranch_ok hp hs hW (by omega) sx ax
      hval' (by have width := resultWords_le_returnWords (D.sigNr n).erg (D.sigNr n).gruende; simpa only [he, resultWords] using width) flag' hw1
    exact .inl ⟨σ', v, m2, rfl, sx2, ax2, hp2, hw2⟩
  | why σ' r =>
    obtain ⟨m1, sx, ax, ⟨value, mirror, flag⟩, hw1⟩ := hc
    have hsig : D.params f = (D.sigNr n).params := (D.passt_sig hf).params
    have herg : D.erg f = (D.sigNr n).erg := (D.passt_sig hf).erg
    have hgru : D.gruende f = (D.sigNr n).gruende := (D.passt_sig hf).gruende
    have value' : ValueAt L m1 (slot fp (BitVec.ofNat 64 (frei Γ reserved)))
        (FB + contextWords (D.sigNr n).params) (.why (D.sigNr n).gruende) (grundSig (n := n) hf r) := by
      have transported := valueAt_why_cast hgru value
      rw [hsig] at transported
      exact (grundSig_eq_cast (n := n) hf hgru r).symm ▸ transported
    have mirror' : ReturnMirror m1 (slot fp (BitVec.ofNat 64 (frei Γ reserved)))
        (FB + contextWords (D.sigNr n).params) := by
      simpa only [hsig] using mirror
    have flag' : ReturnFlag m1 (slot fp (BitVec.ofNat 64 (frei Γ reserved)))
        (contextWords (D.sigNr n).params) false
        (returnWords (D.sigNr n).erg (D.sigNr n).gruende) := by
      simpa only [hsig, herg, hgru] using flag
    obtain ⟨m2, sx2, ax2, hp2, hw2⟩ := callBranch_ok (τ := .why (D.sigNr n).gruende) (v := grundSig (n := n) hf r)
      hp hs hW (by omega) sx ax value' (reasonWords_le_returnWords (D.sigNr n).erg (D.sigNr n).gruende) flag' hw1
    exact .inr (.inl ⟨σ', r, m2, rfl, sx2, ax2, hp2, hw2⟩)
  | logik e => exact .inr (.inr (.inl ⟨e, rfl, hc⟩))
  | hardware e => exact .inr (.inr (.inr ⟨e, rfl, hc⟩))

end Gabbro.Stage0.Senke
