/- Reason publication uses the same complete canonical return span. -/
module
public import Stage0.Senke.Rueckkehr.Context
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- Reason returns bypass the normal postcondition and preserve the world and frame header. -/
theorem retWhy_ok {P : Programm D} {σ0 : World D} {reserved : Nat} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {ρ0 : Env D (D.params f)} {Γ : Ctx} {m : Runner.Mem} {pc : Runner.W}
    {σ : World D} {ρ : Env D Γ} (r : Fin (D.gruende f))
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hK : retTop (functionFrame P f) ≤ Ks)
    (hp : PreS L m pc fp K (frei Γ reserved) (retWhyC (functionFrame P f) r.val) ρ reserved)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) :
    RetWhy L f fp K rp cfp ⟨pc, fp⟩ m σ r := by
  let q := (functionFrame P f).canonicalResult
  have hq0 : q = FB + contextWords (D.params f) := rfl
  have offsets := (functionFrame P f).internal_offsets
  have status : (functionFrame P f).canonicalStatus = q + returnWords (D.erg f) (D.gruende f) := rfl
  have topInternal : (functionFrame P f).internalResult +
      returnWords (D.erg f) (D.gruende f) + 8 ≤ Ks := hK
  have hFB : FB = 4 := rfl
  have hks := hW.ks
  have area := reasonWords_le_returnWords (D.erg f) (D.gruende f)
  have positive := valueWords_pos (.why (D.gruende f))
  have small := hp.small
  have topBound : q + returnWords (D.erg f) (D.gruende f) + 8 ≤ Ks := by omega
  have frame := frameOK_sub hp.frame hks
  have room := frame.room
  let words := encodeWords L (.why (D.gruende f)) r
  let material := constWords words q
  have width : words.length = valueWords (.why (D.gruende f)) := encodeWords_length L _ _
  have bound := constWords_bound words q
  have emitted : retWhyC (functionFrame P f) r.val =
      material.1 ++ [ci 2 2 q 0,
        ci 1 (q + returnWords (D.erg f) (D.gruende f)) 0 0, ci 21 0 0 0] := by
    simp only [retWhyC, status, Int.natCast_add]
    simp only [material, words]
    rw [encodeWords.eq_def L (.why (D.gruende f)) r]
    rfl
  have pre : PreS L m pc fp Ks q
      (material.1 ++ [ci 2 2 q 0, ci 1 (q + returnWords (D.erg f) (D.gruende f)) 0 0, ci 21 0 0 0]) (Env.nil : Env D []) :=
    ⟨by simp only [frei, contextWords_nil, Nat.add_zero]; omega, by omega, frame,
      by simpa only [emitted] using hp.code,
      by simpa only [emitted] using codeFar_sub2 hp.far hks,
      (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  obtain ⟨m1, s1, a1, value1⟩ := constValue_ok (L := L) (τ := .why (D.gruende f)) (c := material.1) (top := material.2) r trivial rfl
    (by change (constWords words q).2 ≤ Ks; omega) pre.left
  have frame1 := frame.agree a1
  have far1 := codeFar_tail (a := material.1) pre.far
  have code1 := (codeAt_right pre.code).agree a1 far1
  let w := words[0]'(by omega)
  have read1 : m1.rd64 (slot fp (BitVec.ofNat 64 q)) = some w := value1.2 0 (by change 0 < words.length; omega)
  have s2 := mov_to (codeAt_left (a := [ci 2 2 q 0]) code1) frame1
    (j := 2) (s := q) (by omega) (by omega)
    (by omega) read1
  let m2 := write m1 (slot fp (BitVec.ofNat 64 2)) 8 w.toNat
  have a2 : Agree fp 2 Ks m1 m2 := agree_write room (Nat.le_refl _) (by omega) _
  have frame2 := frame1.agree a2
  have far2 := codeFar_tail (a := [ci 2 2 q 0]) far1
  have code2 := (codeAt_right (a := [ci 2 2 q 0]) code1).agree a2 far2
  have value2 := ValueAt.write_slot (j := 2) value1 frame1.room (by omega)
    (by omega) (Or.inl (by omega)) w
  have s3 := const_to (j := q + returnWords (D.erg f) (D.gruende f)) (k := 0)
    (codeAt_left (a := [ci 1 (q + returnWords (D.erg f) (D.gruende f)) 0 0]) code2)
    frame2 (by omega) (by omega) (by decide)
  let m3 := write m2 (slot fp (BitVec.ofNat 64 (q + returnWords (D.erg f) (D.gruende f)))) 8 0
  have a3 : Agree fp 2 Ks m2 m3 := agree_write room (by omega) (by omega) _
  have far3 := codeFar_tail (a := [ci 1 (q + returnWords (D.erg f) (D.gruende f)) 0 0]) far2
  have code3 := (codeAt_right (a := [ci 1 (q + returnWords (D.erg f) (D.gruende f)) 0 0]) code2).agree a3 far3
  have ret := code3 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ret
  have head0 : m3.rd64 fp = some rp := by
    rw [← slot_zero fp]
    dsimp only [m3, m2]
    rw [rd_other frame2.room (by omega) (by omega) (by omega),
      rd_other frame1.room (by omega) (by omega) (by omega)]
    rw [agree_rd_low a1 frame.room (by omega) (by omega)]
    exact hk.r0
  have head1 : m3.rd64 (fp + 8) = some cfp := by
    rw [← slot_one fp]
    dsimp only [m3, m2]
    rw [rd_other frame2.room (by omega) (by omega) (by omega),
      rd_other frame1.room (by omega) (by omega) (by omega)]
    rw [agree_rd_low a1 frame.room (by omega) (by omega)]
    exact hk.r1
  have sr := Star.one (run_step (t := ⟨_, fp⟩) ret (by decide) (run_ret (t := ⟨_, fp⟩) head0 head1))
  have changed := (a1.mono (by omega : 2 ≤ q)).trans (a2.trans a3)
  refine ⟨m3, s1.trans (s2.trans (s3.trans sr)), agreeW_of (Agree.widen changed hks), ?_, ?_, ?_,
    weltAt_stab hW.lay hW.lo m m3 hWa (changed.mono (Nat.zero_le _))⟩
  · rw [← hq0]
    exact ValueAt.write_slot (j := q + returnWords (D.erg f) (D.gruende f)) value2 frame2.room (by omega)
      (by omega) (Or.inr (by omega)) 0
  · change m3.rd64 (slot fp (BitVec.ofNat 64 2)) = m3.rd64 (slot fp (BitVec.ofNat 64 (FB + contextWords (D.params f))))
    rw [← hq0]
    dsimp only [m3]
    rw [rd_other (a := q + returnWords (D.erg f) (D.gruende f)) (b := 2)
        frame2.room (by omega) (by omega) (by omega),
      rd_other (a := q + returnWords (D.erg f) (D.gruende f)) (b := q)
        frame2.room (by omega) (by omega) (by omega)]
    dsimp only [m2]
    rw [rd_same frame1 (by omega) w,
      rd_other (a := 2) (b := q) frame1.room (by omega) (by omega) (by omega), read1]
  · change m3.rd64 (slot fp (BitVec.ofNat 64 (FB + contextWords (D.params f) + returnWords (D.erg f) (D.gruende f)))) = some 0
    rw [← hq0]
    exact rd_same frame2 (by omega) 0


end Gabbro.Stage0.Senke
