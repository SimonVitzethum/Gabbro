/-
  File:      stage0/Stage0/Senke/Aufruf.lean
  Subject:   The call site: the depth one less, a constant or saved-slot target, `call` -- then the callee's `FunSpec`.
-/
module
public import Stage0.Senke.Rueckkehr.Calla
public import Stage0.Senke.Spez
public import Stage0.Senke.Anweisung.Hilfe
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-! ## The arguments, and a whole call -/

/-- What a function's code may rely on in its frame: every code at its address, the depth in slot 2. -/
structure Umf (L : Lay D) (A : D.Fn → Nat) (C : D.Fn → List II) (dv : Runner.W) (m : Runner.Mem) (fp : Runner.W)
    (Ks K : Nat) : Prop where
  code : PCode m A C fp K
  depth : m.rd64 (slot fp (BitVec.ofNat 64 2)) = some (dv + 1)
  big : FB ≤ K
  sync : SyncOK m L fp Ks
  hiK : fp.toNat + 8 * K ≤ L.hi

theorem Umf.agree {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {m m' : Runner.Mem} {fp : Runner.W}
    {Ks K lo : Nat} (h : Umf L A C dv m fp Ks K) (ha : Agree fp lo K m m') (hF : FrameOK m fp K) (hlo : FB ≤ lo) :
    Umf L A C dv m' fp Ks K :=
  ⟨pcode_agree h.code ha, by
    have hFB3 : FB = 4 := rfl
    have hb := h.big
    rw [agree_rd_low (ha.mono (Nat.min_le_left lo K)) hF.room (by omega) (Nat.min_le_right lo K)]
    exact h.depth, h.big, h.sync.agree ha h.hiK, h.hiK⟩

theorem Umf.mono {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {m : Runner.Mem} {fp : Runner.W}
    {Ks Ks' K : Nat} (h : Umf L A C dv m fp Ks K) (hs : Ks' ≤ Ks) : Umf L A C dv m fp Ks' K :=
  ⟨h.code, h.depth, h.big, h.sync.mono hs, h.hiK⟩

theorem Pre.up {m : Runner.Mem} {pc fp : Runner.W} {K d d' : Nat} {c : List II} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {reserved : Nat} (h : Pre L m pc fp K d c ρ W reserved) (hd : d ≤ d') : Pre L m pc fp K d' c ρ W reserved :=
  ⟨Nat.le_trans h.ctx hd, h.small, h.frame, h.code, h.far, h.env, h.welt, h.wstab⟩

/-- The arguments land in the parameter slots of the frame at slot `F`, and nothing below `F + FB` changes. -/
theorem lowA_ok {Λ : List (Res D)} {fp : Runner.W} {K F : Nat} {reserved : Nat} {W : Runner.Mem → Prop} (σ₀ σ : World D) {same : σ₀ = σ}
    (hWL : ∀ m, W m → WeltAt m L σ) (hLay : LayIn L) :
    {Γ : Ctx} → {τs : List Ty} → (args : Args D Γ Λ τs) → (c : List II) → (top : Nat) →
    lowA L args (F + FB) reserved = some (c, top) → top ≤ K → F + FB + contextWords τs ≤ K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ), Pre L m pc fp K (F + FB) c ρ W reserved →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧ Agree fp (F + FB) K m m' ∧
      EnvAt L m' (slot fp (BitVec.ofNat 64 F)) (evalArgs σ₀ args σ ρ)
  | _, _, .nil, c, top, h, _, _, m, pc, ρ, _ => by
    simp only [lowA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, fun _ x => nomatch x⟩
  | _, _ :: τs, .cons e rest, c, top, h, hK, hL, m, pc, ρ, hp => by
    simp only [lowA, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cr, tr⟩, hr, ⟨ce, te⟩, he, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [contextWords_cons] at hL
    obtain ⟨m1, s1, a1, e1⟩ := lowA_ok (same := same) (reserved := reserved) σ₀ σ hWL hLay rest cr tr hr (by omega) (by omega) m pc ρ hp.left
    have hp1 := (hp.next a1 (Nat.le_refl _) (by omega)).up (d' := F + FB + contextWords τs) (by omega)
    obtain ⟨m2, s2, a2, value⟩ := lowE_ok (same := by intro _; exact same) (fp := fp) (K := K) σ₀ σ hWL hLay e _ ce te he (by omega) m1 _ ρ hp1
    have hF1 := hp1.frame
    refine ⟨m2, s1.trans (by rw [pc_add1]; exact s2), a1.trans (a2.mono (by omega)), ?_⟩
    simp only [evalArgs]
    have hfr : F + frei τs = F + FB + contextWords τs := by simp only [frei]; omega
    refine envAt_cons (fp := slot fp (BitVec.ofNat 64 F)) ?_ ?_
    · intro τ' y
      obtain ⟨valid, words⟩ := e1 τ' y
      refine ⟨valid, ?_⟩
      intro i hi
      have bound := variableOffset_bound y
      have width := encodeWords_length L τ' ((evalArgs σ₀ rest σ ρ).get y)
      have read := words i hi
      rw [slot_slot] at read ⊢
      rw [agree_rd_low a2 hF1.room (by unfold vslot frei at *; omega) (by omega)]
      exact read
    · refine ⟨value.1, ?_⟩
      intro i hi
      rw [slot_slot]
      have read := value.2 i hi
      simpa only [frei, Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using read

/-- A whole call `callC`: the arguments, the call, the callee's contract; back with the result in slot
    `F + 2`, nothing below `F` changed. -/
theorem callC_ok {A : D.Fn → Nat} {C : D.Fn → List II} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {reserved : Nat} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) {Λ : List (Res D)} {Γ : Ctx} {f : D.Fn}
    (hA : A f < 2 ^ 31) (args : Args D Γ Λ (D.params f)) (σ₀ σ : World D) {same : σ₀ = σ} {ca : List II} {ta : Nat}
    {m : Runner.Mem} {pc fp : Runner.W} {K Ks : Nat} {ρ : Env D Γ}
    (hca : lowA L (reserved := reserved) args (frei Γ reserved + FB) = some (ca, ta)) (htop : callTop f (frei Γ reserved) ta + cap ≤ Ks)
    (hp : PreS L m pc fp K (frei Γ reserved) (callC A f (frei Γ reserved) ca) ρ reserved) (hu : Umf L A C dv m fp Ks K)
    (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) :
    match R f σ (evalArgs σ₀ args σ ρ) with
    | .ok σ' v => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (callC A f (frei Γ reserved) ca).length), fp⟩ m' ∧
        AgreeW L fp (frei Γ reserved) K m m' ∧
        (ResultAt L m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (FB + contextWords (D.params f)) (D.erg f) v ∧
          ReturnMirror m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (FB + contextWords (D.params f)) ∧
          ReturnFlag m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (contextWords (D.params f)) true (returnWords (D.erg f) (D.gruende f))) ∧
        WeltAt m' L σ'
    | .logik e => Stops ⟨pc, fp⟩ m (logikCode e)
    | .hardware h => Stops ⟨pc, fp⟩ m (hwCode h)
    | .why σ' r => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (callC A f (frei Γ reserved) ca).length), fp⟩ m' ∧
        AgreeW L fp (frei Γ reserved) K m m' ∧
        ValueAt L m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (FB + contextWords (D.params f)) (.why (D.gruende f)) r ∧
        ReturnMirror m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (FB + contextWords (D.params f)) ∧
        ReturnFlag m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (contextWords (D.params f)) false (returnWords (D.erg f) (D.gruende f)) ∧ WeltAt m' L σ' := by
  simp only [callTop] at htop
  have hFB : FB ≤ frei Γ reserved := by simp only [frei]; omega
  have hks := hW.ks
  have hp' : PreS L m pc fp K (frei Γ reserved + FB) (ca ++ callTail A f (frei Γ reserved)) ρ reserved := hp.up (by omega)
  have hpw := PreS.welt hp'.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, e1⟩ := lowA_ok (same := same) (reserved := reserved) (F := frei Γ reserved) σ₀ σ (fun _ h => h) hW.lay args ca ta hca (by omega) (by omega) m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
  have hp1 := hp'.next a1 (Nat.le_refl _) (by omega)
  have hl4 : (callTail A f (frei Γ reserved)).length = 4 := rfl
  have hu1 := hu.agree a1 hp.frame (by omega)
  have hc := call_ok (σ := σ) hS hp1.code (by rw [← hl4]; exact hp1.far) hp1.frame hp.small hFB (by omega)
    (by omega) hA hu1.code hu1.depth e1 hW hWa1 hu1.sync
  generalize R f σ (evalArgs σ₀ args σ ρ) = o at hc ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m2, s2, a2, hw, hw2⟩ := hc
    refine ⟨m2, s1.trans ?_, (agreeW_of (a1.mono (by omega))).trans a2, hw, hw2⟩
    simp only [callC]
    rw [pc_add1, hl4]
    exact s2
  | logik e => exact Stops.prefix s1 hc
  | why σ' r =>
    obtain ⟨m2, s2, a2, value, mirror, flag, hw2⟩ := hc
    refine ⟨m2, s1.trans ?_, (agreeW_of (a1.mono (by omega))).trans a2, value, mirror, flag, hw2⟩
    simp only [callC]
    rw [pc_add1, hl4]
    exact s2
  | hardware e => exact Stops.prefix s1 hc

end Gabbro.Stage0.Senke
