module

public import Stage0.Senke.Ausdruck.Arithmetik.Initialisierung.A.Teil8

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

set_option maxHeartbeats 6000000 in
theorem floatFiniteAddL_read_fields_align_branch {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (dst : ℕ) {top K reserved : ℕ} {fp pc : Runner.W} {m : Runner.Mem} (width : F.fracBits + F.ebits < 64) (lower : FB ≤ dst + 1) (frac : F.fracBits < 64) (mask : 2 ^ F.ebits - 1 < 2 ^ 64) (fracMask : 2 ^ F.fracBits - 1 < 2 ^ 64) (hiddenBound : 2 ^ F.fracBits < 2 ^ 64) (room : top ≤ K) (sortRoom : dst + 11 < K) (alignRoom : dst + 17 ≤ K) (executed : List II) (before : Runner.Mem) (tail : List II) (rest : Pre L before (pc + BitVec.ofNat 64 (16 * executed.length)) fp K (dst + 9)
      ([ci 13 ((↑dst : ℤ) + 9) ((↑dst : ℤ) + 5) ((↑dst : ℤ) + 6),
          ci 14 ((↑dst : ℤ) + 10) ((↑dst : ℤ) + 5) ((↑dst : ℤ) + 6),
          ci 13 ((↑dst : ℤ) + 11) ((↑dst : ℤ) + 7) ((↑dst : ℤ) + 8),
          ci 5 ((↑dst : ℤ) + 10) ((↑dst : ℤ) + 10) ((↑dst : ℤ) + 11),
          ci 9 ((↑dst : ℤ) + 9) ((↑dst : ℤ) + 9) ((↑dst : ℤ) + 10), ci 19 ((↑dst : ℤ) + 9) 176 0,
          ci 2 ((↑dst : ℤ) + 9) ((↑dst : ℤ) + 3) 0, ci 2 ((↑dst : ℤ) + 3) ((↑dst : ℤ) + 4) 0,
          ci 2 ((↑dst : ℤ) + 4) ((↑dst : ℤ) + 9) 0, ci 2 ((↑dst : ℤ) + 9) ((↑dst : ℤ) + 5) 0,
          ci 2 ((↑dst : ℤ) + 5) ((↑dst : ℤ) + 6) 0, ci 2 ((↑dst : ℤ) + 6) ((↑dst : ℤ) + 9) 0,
          ci 2 ((↑dst : ℤ) + 9) ((↑dst : ℤ) + 7) 0, ci 2 ((↑dst : ℤ) + 7) ((↑dst : ℤ) + 8) 0,
          ci 2 ((↑dst : ℤ) + 8) ((↑dst : ℤ) + 9) 0, ci 18 16 0 0] ++
        tail)
      ρ W reserved) (aligned : List II × ℕ) (final : Runner.Mem) :
    let vs := fun i => (final.rd64 (slot fp (BitVec.ofNat 64 i))).getD 0;
  ∀ (signedOut : Runner.Mem),
    Runner.IR.Star
        { pc := pc + BitVec.ofNat 64 (16 * executed.length) + 256 + BitVec.ofNat 64 (16 * aligned.1.length), fp := fp }
        final
        { pc := pc + BitVec.ofNat 64 (16 * executed.length) + 256 + BitVec.ofNat 64 (16 * aligned.1.length) + 96,
          fp := fp }
        signedOut →
      Runner.IR.Star { pc := pc, fp := fp } m
          { pc := pc + BitVec.ofNat 64 (16 * executed.length) + 256 + BitVec.ofNat 64 (16 * aligned.1.length),
            fp := fp }
          final →
        ∀ (normalization : List II) (zeroMem : Runner.Mem),
          Runner.IR.Star
              { pc := pc + BitVec.ofNat 64 (16 * executed.length) + 256 + BitVec.ofNat 64 (16 * aligned.1.length) + 96,
                fp := fp }
              signedOut
              {
                pc :=
                  pc + BitVec.ofNat 64 (16 * executed.length) + 256 + BitVec.ofNat 64 (16 * aligned.1.length) + 96 +
                    BitVec.ofNat 64 (16 * [ci 1 ((dst + 10 : ℕ) : ℤ) 0 0].length),
                fp := fp }
              zeroMem →
            ∀ (tested : Runner.Mem),
              Runner.IR.Star
                  {
                    pc :=
                      pc + BitVec.ofNat 64 (16 * executed.length) + 256 + BitVec.ofNat 64 (16 * aligned.1.length) + 96 +
                        BitVec.ofNat 64 (16 * [ci 1 ((↑dst : ℤ) + 10) 0 0].length),
                    fp := fp }
                  zeroMem
                  {
                    pc :=
                      pc + BitVec.ofNat 64 (16 * executed.length) + 256 + BitVec.ofNat 64 (16 * aligned.1.length) + 96 +
                          BitVec.ofNat 64 (16 * [ci 1 ((↑dst : ℤ) + 10) 0 0].length) +
                        BitVec.ofNat 64 (16 * [ci 14 ((dst + 9 : ℕ) : ℤ) ((dst + 7 : ℕ) : ℤ) ((dst + 10 : ℕ) : ℤ)].length),
                    fp := fp }
                  tested →
                ∀ (endJump : II) (normalRest : List II),
                  normalization =
                      [ci 19 ((↑dst : ℤ) + 9) 64 0, ci 5 ((↑dst : ℤ) + 3) ((↑dst : ℤ) + 3) ((↑dst : ℤ) + 4),
                          ci 1 ((↑dst : ℤ) + 7) 0 0, endJump] ++
                        normalRest →
                    Pre L tested
                        (pc + BitVec.ofNat 64 (16 * executed.length) + 256 + BitVec.ofNat 64 (16 * aligned.1.length) +
                              96 +
                            BitVec.ofNat 64 (16 * [ci 1 ((↑dst : ℤ) + 10) 0 0].length) +
                          BitVec.ofNat 64 (16 * [ci 14 ((↑dst : ℤ) + 9) ((↑dst : ℤ) + 7) ((↑dst : ℤ) + 10)].length))
                        fp K (dst + 7)
                        ([ci 19 ((↑dst : ℤ) + 9) 64 0, ci 5 ((↑dst : ℤ) + 3) ((↑dst : ℤ) + 3) ((↑dst : ℤ) + 4),
                            ci 1 ((↑dst : ℤ) + 7) 0 0, endJump] ++
                          normalRest)
                        ρ W reserved →
                      InsAt tested
                          (pc + BitVec.ofNat 64 (16 * executed.length) + 256 + BitVec.ofNat 64 (16 * aligned.1.length) +
                                96 +
                              16 +
                            16)
                          19 (II.f ((dst + 9 : ℕ) : ℤ)) (II.f 64) (II.f 0) →
                        tested.rd64 (slot fp (sx (II.f ((dst + 9 : ℕ) : ℤ)))) =
                            some
                              (Runner.IR.bool
                                ((if (vs (dst + 3) == vs (dst + 4)) = true then vs (dst + 7) + vs (dst + 16)
                                  else vs (dst + 7) - vs (dst + 16)) ==
                                  0)) →
                          ∃ branchTail,
                            Runner.IR.Star { pc := pc, fp := fp } m
                                {
                                  pc :=
                                    pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                          BitVec.ofNat 64 (16 * aligned.1.length) +
                                        128 +
                                      if
                                          ((if (vs (dst + 3) == vs (dst + 4)) = true then vs (dst + 7) + vs (dst + 16)
                                              else vs (dst + 7) - vs (dst + 16)) ==
                                              0) =
                                            true then
                                        16
                                      else 64,
                                  fp := fp }
                                tested ∧
                              Pre L tested
                                  (pc + BitVec.ofNat 64 (16 * executed.length) + 256 +
                                        BitVec.ofNat 64 (16 * aligned.1.length) +
                                      128 +
                                    if
                                        ((if (vs (dst + 3) == vs (dst + 4)) = true then vs (dst + 7) + vs (dst + 16)
                                            else vs (dst + 7) - vs (dst + 16)) ==
                                            0) =
                                          true then
                                      16
                                    else 64)
                                  fp K (dst + 7) branchTail ρ W reserved ∧
                                branchTail =
                                  List.drop
                                    (if
                                        ((if (vs (dst + 3) == vs (dst + 4)) = true then vs (dst + 7) + vs (dst + 16)
                                            else vs (dst + 7) - vs (dst + 16)) ==
                                            0) =
                                          true then
                                      1
                                    else 4)
                                    normalization := by
  intro vs signedOut signedRun wholeRun normalization zeroMem zeroRun tested testRun endJump normalRest branchEq bp branchIns branchRead
  cases hz : ((if vs (dst+3) == vs (dst+4) then vs (dst+7)+vs (dst+16)
    else vs (dst+7)-vs (dst+16)) == 0) with
  | false =>
    rw [hz] at branchRead
    have step := run_step (t := ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.1.length)+96+16+16,fp⟩) branchIns (by decide) (run_brz_zero (t := ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.1.length)+96+16+16,fp⟩) branchIns branchRead)
    have off : sx (II.f 64) = (64 : Runner.W) := by
      rw [sx_lit (by decide : lit32 64 = true)]; rfl
    rw [off] at step
    have rest := bp.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    refine ⟨normalRest,?_,?_,?_⟩
    · simpa [hz, BitVec.add_assoc] using
        (wholeRun.trans (signedRun.trans (zeroRun.trans testRun))).trans (Star.one step)
    · simpa [hz, BitVec.add_assoc] using rest
    · simp [branchEq, hz]
  | true =>
    rw [hz] at branchRead
    have step := run_step (t := ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.1.length)+96+16+16,fp⟩) branchIns (by decide)
      (run_brz_ne (t := ⟨pc+BitVec.ofNat 64 (16*executed.length)+256+BitVec.ofNat 64 (16*aligned.1.length)+96+16+16,fp⟩) (v := 1) branchIns branchRead (by decide))
    have short : Pre L tested _ fp K (dst+7)
        ([ci 19 (dst+9) 64 0] ++
          ([ci 5 (dst+3) (dst+3) (dst+4), ci 1 (dst+7) 0 0,endJump] ++ normalRest))
        ρ W reserved := bp
    have rest := short.next (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    refine ⟨[ci 5 (dst+3) (dst+3) (dst+4), ci 1 (dst+7) 0 0,endJump] ++ normalRest,?_,?_,?_⟩
    · simpa [hz, nxt, BitVec.add_assoc] using
        (wholeRun.trans (signedRun.trans (zeroRun.trans testRun))).trans (Star.one step)
    · simpa [hz, BitVec.add_assoc] using rest
    · simp [branchEq, hz]

end Gabbro.Stage0.Senke
