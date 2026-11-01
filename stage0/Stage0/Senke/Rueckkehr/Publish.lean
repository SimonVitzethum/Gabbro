/- Publish a checked complete result through the canonical call ABI. -/
import Stage0.Senke.Rueckkehr.Context

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}
set_option maxHeartbeats 1000000

theorem publishResult_run (layout : FrameLayout) {v : ErgVal D layout.result}
    {m : Runner.Mem} {pc fp rp cfp : Runner.W} {K : Nat}
    (frame : FrameOK m fp K) (small : K < 2 ^ 31) (fits : retTop layout ≤ K)
    (code : CodeAt m pc (publishC layout)) (far : CodeFar pc (publishC layout).length fp K)
    (value : ResultAt L m fp layout.internalResult layout.result v)
    (head0 : m.rd64 (slot fp (BitVec.ofNat 64 0)) = some rp)
    (head1 : m.rd64 (slot fp (BitVec.ofNat 64 1)) = some cfp) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨rp, cfp⟩ m' ∧ Agree fp 2 K m m' ∧
      ResultAt L m' fp layout.canonicalResult layout.result v ∧
      ReturnMirror m' fp layout.canonicalResult ∧
      ReturnFlag m' fp layout.parameterWords true layout.returnSpan := by
  have lower : 4 ≤ layout.canonicalResult := by
    simp only [FrameLayout.canonicalResult, FB]; omega
  have offsets := layout.internal_offsets
  have width : resultWords layout.result ≤ layout.returnSpan :=
    resultWords_le_returnWords layout.result layout.reasons
  have positive := resultWords_pos layout.result
  have status : layout.canonicalStatus = layout.canonicalResult + layout.returnSpan := rfl
  have internal : layout.internalStatus = layout.internalResult + layout.returnSpan := rfl
  simp only [retTop] at fits
  obtain ⟨m1, copyRun, copied, value1⟩ := copyResult_run frame small
    (by omega) (by omega) (Or.inl (by omega)) (codeAt_left code)
    (by simpa only [publishC, copyWords_length] using (codeFar_left
      (n := (copyWords (resultWords layout.result) layout.canonicalResult layout.internalResult).length)
      (k := 3) (by simpa only [publishC, List.length_append, List.length_cons, List.length_nil] using far))) value
  have first : Agree fp layout.canonicalResult K m m1 := Agree.widen copied (by omega)
  have frame1 := frame.agree first
  have far1 := codeFar_tail
    (a := copyWords (resultWords layout.result) layout.canonicalResult layout.internalResult) far
  have code1 := (codeAt_right code).agree first far1
  simp only [copyWords_length] at code1 far1
  obtain ⟨w, read1⟩ := ResultAt.first value1
  have setStatus := const_to (codeAt_left (a := [ci 1 layout.canonicalStatus 1 0]) code1)
    frame1 (j := layout.canonicalStatus) (k := 1) (by omega) small (by decide)
  let m2 := write m1 (slot fp (BitVec.ofNat 64 layout.canonicalStatus)) 8 1
  have second : Agree fp layout.canonicalResult K m1 m2 :=
    agree_write frame1.room (by omega) (by omega) _
  have frame2 := frame1.agree second
  have value2 := ResultAt.write_slot (j := layout.canonicalStatus) value1 frame1.room (by omega) (by omega)
    (Or.inr (by omega)) (1 : Runner.W)
  have far2 := codeFar_tail (a := [ci 1 layout.canonicalStatus 1 0]) far1
  have code2 := (codeAt_right (a := [ci 1 layout.canonicalStatus 1 0]) code1).agree second far2
  have read2 : m2.rd64 (slot fp (BitVec.ofNat 64 layout.canonicalResult)) = some w := by
    dsimp only [m2]
    rw [rd_other frame1.room (by omega) (by omega) (by omega)]
    exact read1
  have mirrorRun := mov_to (codeAt_left (a := [ci 2 2 layout.canonicalResult 0]) code2)
    frame2 (j := 2) (s := layout.canonicalResult) (by omega) (by omega) small read2
  let m3 := write m2 (slot fp (BitVec.ofNat 64 2)) 8 w.toNat
  have third : Agree fp 2 K m2 m3 := agree_write frame2.room (Nat.le_refl _) (by omega) _
  have far3 := codeFar_tail (a := [ci 2 2 layout.canonicalResult 0]) far2
  have code3 := (codeAt_right (a := [ci 2 2 layout.canonicalResult 0]) code2).agree third far3
  have ret := code3 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ret
  have beforeMirror := first.trans second
  have r0 : m3.rd64 fp = some rp := by
    rw [← slot_zero fp]
    dsimp only [m3]
    rw [rd_other frame2.room (by omega) (by omega) (by omega),
      agree_rd_low beforeMirror frame.room (by omega) (by omega)]
    exact head0
  have r1 : m3.rd64 (fp + 8) = some cfp := by
    rw [← slot_one fp]
    dsimp only [m3]
    rw [rd_other frame2.room (by omega) (by omega) (by omega),
      agree_rd_low beforeMirror frame.room (by omega) (by omega)]
    exact head1
  have returned := Star.one (run_step (t := ⟨_, fp⟩) ret (by decide)
    (run_ret (t := ⟨_, fp⟩) r0 r1))
  refine ⟨m3, copyRun.trans (setStatus.trans (mirrorRun.trans returned)),
    (beforeMirror.mono (by omega)).trans third, ?_, ?_, ?_⟩
  · exact ResultAt.write_slot (j := 2) value2 frame2.room (by omega) (by omega) (Or.inl (by omega)) w
  · change m3.rd64 (slot fp (BitVec.ofNat 64 2)) =
      m3.rd64 (slot fp (BitVec.ofNat 64 layout.canonicalResult))
    dsimp only [m3]
    rw [rd_same frame2 (by omega) w,
      rd_other frame2.room (by omega) (by omega) (by omega), read2]
  · change m3.rd64 (slot fp (BitVec.ofNat 64 layout.canonicalStatus)) = some 1
    dsimp only [m3, m2]
    rw [rd_other frame2.room (by omega) (by omega) (by omega)]
    exact rd_same frame1 (by omega) 1

end Gabbro.Stage0.Senke
