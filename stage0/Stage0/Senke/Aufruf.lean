/-
  File:      stage0/Stage0/Senke/Aufruf.lean
  Subject:   The call site: the depth one less, the address, `call` -- then the callee's `FunSpec`.
-/
import Stage0.Senke.Spez
import Stage0.Senke.Anweisung.Hilfe

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- A read of slot `b` after a write of slot `a ≠ b`. -/
theorem rd_other {m : Runner.Mem} {fp : Runner.W} {K a b : Nat} (hr : fp.toNat + 8 * K ≤ 2 ^ 64) (ha : a < K)
    (hb : b < K) (hne : a ≠ b) (v : Nat) :
    (write m (slot fp (BitVec.ofNat 64 a)) 8 v).rd64 (slot fp (BitVec.ofNat 64 b)) =
      m.rd64 (slot fp (BitVec.ofNat 64 b)) :=
  rd64_write_far (slot_far hr ha hb hne)

theorem rd_same {m : Runner.Mem} {fp : Runner.W} {K a : Nat} (hF : FrameOK m fp K) (ha : a < K) (v : Runner.W) :
    (write m (slot fp (BitVec.ofNat 64 a)) 8 v.toNat).rd64 (slot fp (BitVec.ofNat 64 a)) = some v :=
  rd64_wr64 (wr64_some (hF.wr a ha)) (hF.rd a ha)

theorem call_ok {A : D.Fn → Nat} {C : D.Fn → List II} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {dv : Runner.W} {c : Nat} (hS : FunSpec L A C R dv c)
    {m : Runner.Mem} {pc fp : Runner.W} {K Ks F : Nat} {f : D.Fn} {σ : World D} {ρa : Env D (D.params f)}
    (hc : CodeAt m pc (callTail A f F)) (hcf : CodeFar pc 4 fp K) (hF : FrameOK m fp K) (hK : K < 2 ^ 31)
    (hFB : FB ≤ F) (hT : F + FB + (D.params f).length + 1 ≤ Ks) (hcap : F + c ≤ Ks) (hA : A f < 2 ^ 31)
    (hP : PCode m A C fp K) (hdv : m.rd64 (slot fp (BitVec.ofNat 64 2)) = some (dv + 1))
    (hE : EnvAt m (slot fp (BitVec.ofNat 64 F)) ρa) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) :
    match R f σ ρa with
    | .ok σ' v => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 4), fp⟩ m' ∧ Agree fp F K m m' ∧
        (∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 (F + 2))) = some w ∧ EncErg (D.erg f) v w) ∧ WeltAt m' L σ'
    | .logik e => Stops ⟨pc, fp⟩ m (logikCode e)
    | .hardware h => Stops ⟨pc, fp⟩ m (hwCode h)
    | _ => False := by
  have hroom := hF.room
  have hlt := hF.lt
  have hFB3 : FB = 3 := rfl
  have hks := hW.ks
  have hroomS : fp.toNat + 8 * Ks ≤ 2 ^ 64 := by omega
  -- the four instructions, read where they lie
  have far : ∀ k, k < 4 → (pc + BitVec.ofNat 64 (16 * k)).toNat + 16 ≤ 2 ^ 64 ∧
      ((pc + BitVec.ofNat 64 (16 * k)).toNat + 16 ≤ fp.toNat ∨
        fp.toNat + 8 * K ≤ (pc + BitVec.ofNat 64 (16 * k)).toNat) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hcf
    have := pc.isLt
    have hx : (pc + BitVec.ofNat 64 (16 * k)).toNat = pc.toNat + 16 * k := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [hx]; omega
  have i0 := hc 0 (by simp [callTail])
  have i1 := hc 1 (by simp [callTail])
  have i2 := hc 2 (by simp [callTail])
  have i3 := hc 3 (by simp [callTail])
  simp only [callTail, ci, List.getElem_cons_zero, List.getElem_cons_succ] at i0 i1 i2 i3
  -- the writes
  let T := F + FB + (D.params f).length
  have hsT : sx (II.f (T : Int)) = BitVec.ofNat 64 T := sx_nat (by omega)
  have hs2 : sx (II.f ((F + 2 : Nat) : Int)) = BitVec.ofNat 64 (F + 2) := sx_nat (by omega)
  have hsF : sx (II.f (F : Int)) = BitVec.ofNat 64 F := sx_nat (by omega)
  let m1 := write m (slot fp (BitVec.ofNat 64 T)) 8 (BitVec.ofInt 64 1).toNat
  have a1s : Agree fp F Ks m m1 := agree_write hroomS (by omega) (by omega) _
  have a1 : Agree fp F K m m1 := Agree.widen a1s hks
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (F + 2))) 8 dv.toNat
  have a2s : Agree fp F Ks m1 m2 := agree_write hroomS (by omega) (by omega) _
  have a2 : Agree fp F K m1 m2 := Agree.widen a2s hks
  let m3 := write m2 (slot fp (BitVec.ofNat 64 T)) 8 (BitVec.ofInt 64 (A f)).toNat
  have a3s : Agree fp F Ks m2 m3 := agree_write hroomS (by omega) (by omega) _
  have a3 : Agree fp F K m2 m3 := Agree.widen a3s hks
  let m4 := write m3 (slot fp (BitVec.ofNat 64 F)) 8 (pc + BitVec.ofNat 64 (16 * 3) + 16).toNat
  have a4s : Agree fp F Ks m3 m4 := agree_write hroomS (by omega) (by omega) _
  have a4 : Agree fp F K m3 m4 := Agree.widen a4s hks
  let m5 := write m4 (slot fp (BitVec.ofNat 64 (F + 1))) 8 fp.toNat
  have a5s : Agree fp F Ks m4 m5 := agree_write hroomS (by omega) (by omega) _
  have a5 : Agree fp F K m4 m5 := Agree.widen a5s hks
  have hF1 := hF.agree a1
  have hF2 := hF1.agree a2
  have hF3 := hF2.agree a3
  have hF4 := hF3.agree a4
  have a15 : Agree fp F K m m5 := a1.trans (a2.trans (a3.trans (a4.trans a5)))
  have hF5 := hF4.agree a5
  -- the instructions in the memories they run in
  have j1 := i1.agree a1 (far 1 (by decide))
  have j2 := i2.agree (a1.trans a2) (far 2 (by decide))
  have j3 := i3.agree (a1.trans (a2.trans a3)) (far 3 (by decide))
  have e16 : ∀ k : Nat, pc + BitVec.ofNat 64 (16 * k) + 16 = pc + BitVec.ofNat 64 (16 * (k + 1)) := fun k => by
    rw [BitVec.add_assoc, Nat.mul_add, BitVec.ofNat_add (16 * k)]; rfl
  -- 1: const T 1
  have s1 : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m1 := by
    have := const_step (j := T) (k := 1) (codeAt_left (a := [ci 1 ((T : Nat) : Int) 1 0]) hc) hF (by omega) hK
      (by decide)
    exact this
  -- 2: sub (F+2) 2 T
  have s2 : Star ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m1 ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m2 := by
    refine Star.one ?_
    have r := run_step (t := ⟨_, fp⟩) j1 (by decide) (run_bin (t := ⟨_, fp⟩) j1 (m1 := m2) (va := dv + 1)
      (vb := BitVec.ofInt 64 1) (g := fun a b => some (a - b)) ?_ ?_
      (by show some (dv + 1 - BitVec.ofInt 64 1) = some dv
          rw [show BitVec.ofInt 64 1 = 1 by decide, BitVec.add_sub_cancel]) ?_)
    · simp only [nxt] at r; rw [e16] at r; exact r
    · rw [sx_lit (by decide), show BitVec.ofInt 64 2 = BitVec.ofNat 64 2 by decide]
      simp only [m1]; rw [rd_other hroom (by omega) (by omega) (by omega)]; exact hdv
    · rw [hsT]; exact rd_same hF (by omega) _
    · rw [hs2]; exact wr64_some (hF1.wr _ (by omega))
  -- 3: const T (A f)
  have s3 : Star ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m2 ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩ m3 := by
    refine Star.one ?_
    have r : Run (op 1 ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩) m2 (nxt ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩) m3 := by
      simp only [op]
      refine f2_run (t := ⟨_, fp⟩) j2 ?_
      simp only [ret1]
      refine f1_run (t := ⟨_, fp⟩) j2 ?_
      rw [hsT, sx_lit (n := ((A f : Nat) : Int)) (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)]
      exact run_wr64 (wr64_some (hF2.wr _ (by omega)))
    have r2 := run_step (t := ⟨_, fp⟩) j2 (by decide) r
    simp only [nxt] at r2; rw [e16] at r2; exact r2
  -- 4: call T F
  have s4 : Star ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩ m3 ⟨BitVec.ofNat 64 (A f), slot fp (BitVec.ofNat 64 F)⟩ m5 := by
    refine Star.one ?_
    have := run_call (t := ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩) (m1 := m4) (m2 := m5) j3
      (tg := BitVec.ofInt 64 (A f)) (by rw [hsT]; exact rd_same hF2 (by omega) _)
      (by rw [hsF]; exact wr64_some (hF3.wr _ (by omega)))
      (by rw [hsF, show (8 : Runner.W) = BitVec.ofNat 64 (8 * 1) by rfl, slot_plus]
          exact wr64_some (hF4.wr _ (by omega)))
    rw [hsF, show BitVec.ofInt 64 (A f : Int) = BitVec.ofNat 64 (A f) by simp] at this
    exact run_step (t := ⟨_, fp⟩) j3 (by decide) this
  -- the callee's frame
  have hFF : F ≤ K := by omega
  have g0 : m5.rd64 (slot (slot fp (BitVec.ofNat 64 F)) (BitVec.ofNat 64 0)) =
      some (pc + BitVec.ofNat 64 (16 * 3) + 16) := by
    rw [slot_slot, Nat.add_zero]
    simp only [m5]; rw [rd_other hroom (by omega) (by omega) (by omega)]
    exact rd_same hF3 (by omega) _
  have g1 : m5.rd64 (slot (slot fp (BitVec.ofNat 64 F)) (BitVec.ofNat 64 1)) = some fp := by
    rw [slot_slot]; exact rd_same hF4 (by omega) _
  have g2 : m5.rd64 (slot (slot fp (BitVec.ofNat 64 F)) (BitVec.ofNat 64 2)) = some dv := by
    rw [slot_slot]
    simp only [m5, m4, m3]
    rw [rd_other hroom (by omega) (by omega) (by omega), rd_other hroom (by omega) (by omega) (by omega),
      rd_other hroom (by omega) (by omega) (by omega)]
    exact rd_same hF1 (by omega) _
  have gE : EnvAt m5 (slot fp (BitVec.ofNat 64 F)) ρa := by
    intro τ x
    obtain ⟨w, hw, he⟩ := hE τ x
    refine ⟨w, ?_, he⟩
    have h1 := vslot_lt x
    have h2 : FB ≤ vslot x := by unfold vslot; omega
    simp only [frei] at h1
    rw [slot_slot] at hw ⊢
    simp only [m5, m4, m3, m2, m1]
    rw [rd_other hroom (by omega) (by omega) (by omega), rd_other hroom (by omega) (by omega) (by omega),
      rd_other hroom (by omega) (by omega) (by omega), rd_other hroom (by omega) (by omega) (by omega),
      rd_other hroom (by omega) (by omega) (by omega)]
    exact hw
  have hW5 : WeltAt m5 L σ := weltAt_stab hW.lay (by have := hW.lo; omega) m m5 hWa
    ((a1s.trans (a2s.trans (a3s.trans (a4s.trans a5s)))).mono (Nat.zero_le _))
  have hspec := hS f m5 (slot fp (BitVec.ofNat 64 F)) (K - F) (Ks - F) _ fp σ ρa (by omega)
    (hW.sub (by omega) hlt) (by omega)
    (frame_sub hF5 hFF) (pcode_sub (pcode_agree hP a15) hF5.lt hFF) g0 g1 g2 gE hW5
  have s14 := s1.trans (s2.trans (s3.trans s4))
  cases hR : R f σ ρa with
  | ok σ' v =>
    rw [hR] at hspec
    obtain ⟨m6, s6, a6, ⟨w, hw, he⟩, hw6⟩ := hspec
    refine ⟨m6, s14.trans ?_, a15.trans ((agree_sub hF5.lt hFF a6).mono (by omega)),
      ⟨w, by rw [← slot_slot]; exact hw, he⟩, hw6⟩
    rw [e16] at s6
    exact s6
  | logik e =>
    rw [hR] at hspec
    exact Stops.prefix s14 hspec
  | why σ' r => rw [hR] at hspec; exact hspec
  | hardware e =>
    rw [hR] at hspec
    exact Stops.prefix s14 hspec

/-! ## The arguments, and a whole call -/

/-- What a function's code may rely on in its frame: every code at its address, the depth in slot 2. -/
structure Umf (A : D.Fn → Nat) (C : D.Fn → List II) (dv : Runner.W) (m : Runner.Mem) (fp : Runner.W) (K : Nat) :
    Prop where
  code : PCode m A C fp K
  depth : m.rd64 (slot fp (BitVec.ofNat 64 2)) = some (dv + 1)
  big : FB ≤ K

theorem Umf.agree {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {m m' : Runner.Mem} {fp : Runner.W}
    {K lo : Nat} (h : Umf A C dv m fp K) (ha : Agree fp lo K m m') (hF : FrameOK m fp K) (hlo : FB ≤ lo) :
    Umf A C dv m' fp K :=
  ⟨pcode_agree h.code ha, by
    have hFB3 : FB = 3 := rfl
    have hb := h.big
    rw [agree_rd_low (ha.mono (Nat.min_le_left lo K)) hF.room (by omega) (Nat.min_le_right lo K)]
    exact h.depth, h.big⟩

theorem Pre.up {m : Runner.Mem} {pc fp : Runner.W} {K d d' : Nat} {c : List II} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (h : Pre m pc fp K d c ρ W) (hd : d ≤ d') : Pre m pc fp K d' c ρ W :=
  ⟨Nat.le_trans h.ctx hd, h.small, h.frame, h.code, h.far, h.env, h.welt, h.wstab⟩

/-- The arguments land in the parameter slots of the frame at slot `F`, and nothing below `F + FB` changes. -/
theorem lowA_ok {Λ : List (Res D)} {fp : Runner.W} {K F : Nat} {W : Runner.Mem → Prop} (σ₀ σ : World D)
    (hWL : ∀ m, W m → WeltAt m L σ) :
    {Γ : Ctx} → {τs : List Ty} → (args : Args D Γ Λ τs) → (c : List II) → (top : Nat) →
    lowA L args (F + FB) = some (c, top) → top ≤ K → F + FB + τs.length ≤ K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ), Pre m pc fp K (F + FB) c ρ W →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧ Agree fp (F + FB) K m m' ∧
      EnvAt m' (slot fp (BitVec.ofNat 64 F)) (evalArgs σ₀ args σ ρ)
  | _, _, .nil, c, top, h, _, _, m, pc, ρ, _ => by
    simp only [lowA, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, fun _ x => nomatch x⟩
  | _, _ :: τs, .cons e rest, c, top, h, hK, hL, m, pc, ρ, hp => by
    simp only [lowA, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cr, tr⟩, hr, ⟨ce, te⟩, he, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_cons] at hL
    obtain ⟨m1, s1, a1, e1⟩ := lowA_ok σ₀ σ hWL rest cr tr hr (by omega) (by omega) m pc ρ hp.left
    have hp1 := (hp.next a1 (Nat.le_refl _) (by omega)).up (d' := F + FB + τs.length) (by omega)
    obtain ⟨m2, s2, a2, w, hw, hen⟩ := lowE_ok (fp := fp) (K := K) σ₀ σ hWL e _ ce te he (by omega) m1 _ ρ hp1
    have hF1 := hp1.frame
    refine ⟨m2, s1.trans (by rw [pc_add1]; exact s2), a1.trans (a2.mono (by omega)), ?_⟩
    simp only [evalArgs]
    have hfr : F + frei τs = F + FB + τs.length := by simp only [frei]; omega
    refine envAt_cons (fp := slot fp (BitVec.ofNat 64 F)) ?_ (by rw [slot_slot, hfr]; exact hw) hen
    intro τ' y
    obtain ⟨w', hw', he'⟩ := e1 τ' y
    refine ⟨w', ?_, he'⟩
    have := vslot_lt y
    rw [slot_slot] at hw' ⊢
    rw [agree_rd_low a2 hF1.room (by simp only [frei] at this; omega) (by omega)]
    exact hw'

/-- A whole call `callC`: the arguments, the call, the callee's contract; back with the result in slot
    `F + 2`, nothing below `F` changed. -/
theorem callC_ok {A : D.Fn → Nat} {C : D.Fn → List II} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) {Λ : List (Res D)} {Γ : Ctx} {f : D.Fn}
    (hA : A f < 2 ^ 31) (args : Args D Γ Λ (D.params f)) (σ₀ σ : World D) {ca : List II} {ta : Nat}
    {m : Runner.Mem} {pc fp : Runner.W} {K Ks : Nat} {ρ : Env D Γ}
    (hca : lowA L args (frei Γ + FB) = some (ca, ta)) (htop : callTop f (frei Γ) ta + cap ≤ Ks)
    (hp : PreS m pc fp K (frei Γ) (callC A f (frei Γ) ca) ρ) (hu : Umf A C dv m fp K)
    (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) :
    match R f σ (evalArgs σ₀ args σ ρ) with
    | .ok σ' v => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (callC A f (frei Γ) ca).length), fp⟩ m' ∧
        Agree fp (frei Γ) K m m' ∧
        (∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ + 2))) = some w ∧ EncErg (D.erg f) v w) ∧
        WeltAt m' L σ'
    | .logik e => Stops ⟨pc, fp⟩ m (logikCode e)
    | .hardware h => Stops ⟨pc, fp⟩ m (hwCode h)
    | _ => False := by
  simp only [callTop] at htop
  have hFB : FB ≤ frei Γ := by simp only [frei]; omega
  have hks := hW.ks
  have hp' : PreS m pc fp K (frei Γ + FB) (ca ++ callTail A f (frei Γ)) ρ := hp.up (by omega)
  have hpw := PreS.welt hp'.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, e1⟩ := lowA_ok (F := frei Γ) σ₀ σ (fun _ h => h) args ca ta hca (by omega) (by omega) m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
  have hp1 := hp'.next a1 (Nat.le_refl _) (by omega)
  have hl4 : (callTail A f (frei Γ)).length = 4 := rfl
  have hu1 := hu.agree a1 hp.frame (by omega)
  have hc := call_ok (σ := σ) hS hp1.code (by rw [← hl4]; exact hp1.far) hp1.frame hp.small hFB (by omega)
    (by omega) hA hu1.code hu1.depth e1 hW hWa1
  generalize R f σ (evalArgs σ₀ args σ ρ) = o at hc ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m2, s2, a2, hw, hw2⟩ := hc
    refine ⟨m2, s1.trans ?_, (a1.mono (by omega)).trans a2, hw, hw2⟩
    simp only [callC]
    rw [pc_add1, hl4]
    exact s2
  | logik e => exact Stops.prefix s1 hc
  | why _ _ => exact hc.elim
  | hardware e => exact Stops.prefix s1 hc

end Gabbro.Stage0.Senke
