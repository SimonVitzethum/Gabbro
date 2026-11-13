/-
  File:      stage0/Stage0/Senke/Aufruf.lean
  Subject:   The call site: the depth one less, a constant or saved-slot target, `call` -- then the callee's `FunSpec`.
-/
module
public import Stage0.Senke.Spez
public import Stage0.Senke.Anweisung.Hilfe
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-- The actual caller receive code transports every allocated return word and
    preserves the following status slot, even when the normal value uses less
    than the shared normal/reason area. -/
theorem receive_run {m : Runner.Mem} {pc fp : Runner.W} {K F : Nat}
    (signature : Signatur D.Tab D.Glob D.Lock D.Marke)
    (frame : FrameOK m fp K) (small : K < 2 ^ 31)
    (fits : receiveTop signature F ≤ K)
    (code : CodeAt m pc (receiveC signature F))
    (far : CodeFar pc (receiveC signature F).length fp K) :
    ∃ m', Star ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (receiveC signature F).length), fp⟩ m' ∧
      Agree fp F K m m' ∧
      (∀ i, i < returnWords signature.erg signature.gruende →
        m'.rd64 (slot fp (BitVec.ofNat 64 (F + i))) =
          m.rd64 (slot fp (BitVec.ofNat 64 (F + FB + contextWords signature.params + i)))) ∧
      m'.rd64 (slot fp (BitVec.ofNat 64
        (F + FB + contextWords signature.params + returnWords signature.erg signature.gruende))) =
      m.rd64 (slot fp (BitVec.ofNat 64
        (F + FB + contextWords signature.params + returnWords signature.erg signature.gruende))) := by
  have fb : FB = 4 := rfl
  have bound : F + FB + contextWords signature.params + returnWords signature.erg signature.gruende + 1 ≤ K := fits
  obtain ⟨m', run, changed, copied⟩ := copyRegion_run frame small
    (by omega) (by omega) (Or.inl (by omega)) code
    (by simpa only [receiveC, copyWords_length] using far)
  refine ⟨m', ?_, Agree.widen changed (by omega), copied, ?_⟩
  · simpa only [receiveC, copyWords_length] using run
  · exact agree_rd_above changed frame.room (by omega) (by omega)

theorem call_ok {indirect : Bool} {A : D.Fn → Nat} {C : D.Fn → List II} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {dv : Runner.W} {c : Nat} (hS : FunSpec L A C R dv c)
    {m : Runner.Mem} {pc fp : Runner.W} {K Ks F : Nat} {f : D.Fn} {σ : World D} {ρa : Env D (D.params f)}
    (hc : CodeAt m pc (callTail A f F indirect)) (hcf : CodeFar pc 4 fp K) (hF : FrameOK m fp K) (hK : K < 2 ^ 31)
    (hFB : FB ≤ F) (hT : F + FB + (contextWords (D.params f)) + 1 ≤ Ks) (hcap : F + c ≤ Ks) (hA : A f < 2 ^ 31)
    (hP : PCode m A C fp K) (hdv : m.rd64 (slot fp (BitVec.ofNat 64 2)) = some (dv + 1))
    (hE : EnvAt L m (slot fp (BitVec.ofNat 64 F)) ρa) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ)
    {H : List D.Lock} (hy : TicketSync m L fp Ks H)
    (hH : HeldIn H (Signatur.anfang D (D.signatur f)) (D.signatur f).boden)
    (htarget : indirect = true → m.rd64 (slot fp (BitVec.ofNat 64 F)) = some (BitVec.ofNat 64 (A f)) := by simp) :
    match R f σ ρa with
    | .ok σ' v => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 4), fp⟩ m' ∧ AgreeW L fp F K m m' ∧
        (ResultAt L m' (slot fp (BitVec.ofNat 64 F)) (FB + contextWords (D.params f)) (D.erg f) v ∧
          ReturnMirror m' (slot fp (BitVec.ofNat 64 F)) (FB + contextWords (D.params f)) ∧
          ReturnFlag m' (slot fp (BitVec.ofNat 64 F)) (contextWords (D.params f)) true (returnWords (D.erg f) (D.gruende f))) ∧ WeltAt m' L σ'
    | .logik e => Stops ⟨pc, fp⟩ m (logikCode e)
    | .hardware h => Stops ⟨pc, fp⟩ m (hwCode h)
    | .why σ' r => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 4), fp⟩ m' ∧
        AgreeW L fp F K m m' ∧
        ValueAt L m' (slot fp (BitVec.ofNat 64 F)) (FB + contextWords (D.params f)) (.why (D.gruende f)) r ∧
        ReturnMirror m' (slot fp (BitVec.ofNat 64 F)) (FB + contextWords (D.params f)) ∧
        ReturnFlag m' (slot fp (BitVec.ofNat 64 F)) (contextWords (D.params f)) false (returnWords (D.erg f) (D.gruende f)) ∧ WeltAt m' L σ' := by
  have hroom := hF.room
  have hlt := hF.lt
  have hFB3 : FB = 4 := rfl
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
  have i0 := hc 0 (by simp [callTail, callTailN])
  have i1 := hc 1 (by simp [callTail, callTailN])
  have i2 := hc 2 (by simp [callTail, callTailN])
  have i3 := hc 3 (by simp [callTail, callTailN])
  simp only [callTail, callTailN, ci, List.getElem_cons_zero, List.getElem_cons_succ] at i0 i1 i2 i3
  -- the writes
  let T := F + FB + (contextWords (D.params f))
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
    cases indirect with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at j2
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
    | true =>
      simp only [↓reduceIte] at j2
      have hread : m2.rd64 (slot fp (BitVec.ofNat 64 F)) = some (BitVec.ofInt 64 (A f)) := by
        simp only [m2, m1]
        rw [rd_other hroom (by omega) (by omega) (by omega), rd_other hroom (by omega) (by omega) (by omega)]
        simpa only [BitVec.ofInt_natCast] using htarget rfl
      have hc2 : CodeAt m2 (pc + BitVec.ofNat 64 (16 * 2)) [ci 2 T F 0] := by
        intro k hk
        have : k = 0 := by simp only [List.length_singleton] at hk; omega
        subst k
        simpa only [ci, T, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] using j2
      have st := mov_to hc2 hF2 (j := T) (s := F) (by omega) (by omega) hK hread
      simpa only [List.length_singleton, show BitVec.ofNat 64 (16 * 1) = (16 : Runner.W) by decide, e16] using st
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
  have gE : EnvAt L m5 (slot fp (BitVec.ofNat 64 F)) ρa := by
    intro τ x
    have value := hE τ x
    refine ⟨value.1, ?_⟩
    intro i hi
    have hw := value.2 i hi
    have width := encodeWords_length L τ (ρa.get x)
    have h1 := variableOffset_bound x
    have h2 : FB ≤ vslot x := by unfold vslot; omega
    have bound : vslot x + i < FB + contextWords (D.params f) := by unfold vslot; omega
    rw [slot_slot] at hw ⊢
    simp only [m5, m4, m3, m2, m1]
    rw [rd_other hroom (by omega) (by omega) (by omega), rd_other hroom (by omega) (by omega) (by omega),
      rd_other hroom (by omega) (by omega) (by omega), rd_other hroom (by omega) (by omega) (by omega),
      rd_other hroom (by omega) (by omega) (by omega)]
    exact hw
  have hW5 : WeltAt m5 L σ := weltAt_stab hW.lay (by have := hW.lo; omega) m m5 hWa
    ((a1s.trans (a2s.trans (a3s.trans (a4s.trans a5s)))).mono (Nat.zero_le _))
  have hspec := hS.run f m5 (slot fp (BitVec.ofNat 64 F)) (K - F) (Ks - F) _ fp σ ρa H (by omega)
    (hW.sub (by omega) hlt) (by omega)
    (frame_sub hF5 hFF) (pcode_sub (pcode_agree hP a15) hF5.lt hFF) g0 g1 g2 gE hW5
    ((hy.agree a15 (by have := hW.top; have := hW.ord; omega)).call (by omega)) hH
  have s14 := s1.trans (s2.trans (s3.trans s4))
  cases hR : R f σ ρa with
  | ok σ' v =>
    rw [hR] at hspec
    obtain ⟨m6, s6, a6, value, hw6⟩ := hspec
    refine ⟨m6, s14.trans ?_, (agreeW_of a15).trans ((agreeW_sub hF5.lt hFF a6).mono (by omega)),
      value, hw6⟩
    rw [e16] at s6
    exact s6
  | logik e =>
    rw [hR] at hspec
    exact Stops.prefix s14 hspec
  | why σ' r =>
    rw [hR] at hspec
    obtain ⟨m6, s6, a6, value, mirror, flag, hw6⟩ := hspec
    refine ⟨m6, s14.trans ?_, (agreeW_of a15).trans ((agreeW_sub hF5.lt hFF a6).mono (by omega)),
      value, mirror, flag, hw6⟩
    rw [e16] at s6
    exact s6
  | hardware e =>
    rw [hR] at hspec
    exact Stops.prefix s14 hspec


end Gabbro.Stage0.Senke
