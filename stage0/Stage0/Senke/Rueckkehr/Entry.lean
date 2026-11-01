/- The checked function-entry frame protocol: preserve parameters, capture complete
   entry values, then establish the writable lexical parameter environment. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Relocate
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}
set_option maxHeartbeats 2000000

theorem entryFrame_run (P : Programm D) (f : D.Fn)
    {snap : List II} {m : Runner.Mem} {pc fp : Runner.W} {K : Nat} {σ : World D}
    {ρ : Env D (D.params f)}
    (emitted : EntrySnapshots.capture L (oldCells (P.ensures f)) FB = some snap)
    (frame : FrameOK m fp K) (small : K < 2 ^ 31)
    (fits : frei (D.params f) (functionFrame P f).bodyReserved ≤ K)
    (code : CodeAt m pc
      (relocateC FB (functionFrame P f).ensReserved (contextWords (D.params f)) ++
        (snap ++ relocateC (functionFrame P f).ensParams
          ((functionFrame P f).bodyReserved - (functionFrame P f).ensReserved)
          (contextWords (D.params f)))))
    (far : CodeFar pc
      (relocateC FB (functionFrame P f).ensReserved (contextWords (D.params f)) ++
        (snap ++ relocateC (functionFrame P f).ensParams
          ((functionFrame P f).bodyReserved - (functionFrame P f).ensReserved)
          (contextWords (D.params f)))).length fp K)
    (env : EnvAt L m fp ρ) (world : WeltAt m L σ) (layoutIn : LayIn L)
    (separated : fp.toNat + 8 * K ≤ L.lo) :
    ∃ m', Star ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (2 * contextWords (D.params f) + snap.length)), fp⟩ m' ∧
      Agree fp FB K m m' ∧
      EnvAt L m' fp ρ (functionFrame P f).ensReserved ∧
      EnvAt L m' fp ρ (functionFrame P f).bodyReserved ∧
      EntrySnapshots.At L σ m' fp (oldCells (P.ensures f)) FB ∧ WeltAt m' L σ := by
  let layout := functionFrame P f
  change frei (D.params f) layout.bodyReserved ≤ K at fits
  change CodeAt m pc (relocateC FB layout.ensReserved (contextWords (D.params f)) ++
    (snap ++ relocateC layout.ensParams (layout.bodyReserved - layout.ensReserved)
      (contextWords (D.params f)))) at code
  change CodeFar pc (relocateC FB layout.ensReserved (contextWords (D.params f)) ++
    (snap ++ relocateC layout.ensParams (layout.bodyReserved - layout.ensReserved)
      (contextWords (D.params f)))).length fp K at far
  have reserve : layout.ensReserved ≤ layout.bodyReserved := by
    simp only [FrameLayout.ensReserved, FrameLayout.bodyReserved]
    omega
  have snapshotEnd : FB + EntrySnapshots.words (oldCells (P.ensures f)) = layout.ensParams := rfl
  have paramEnd : frei (D.params f) layout.ensReserved = layout.internalResult := rfl
  have bodyEnd : frei (D.params f) layout.bodyReserved =
      layout.bodyParams + layout.parameterWords := rfl
  have bodyFits : layout.bodyParams ≤ K := by
    have endFits : layout.bodyParams + layout.parameterWords ≤ K := fits
    omega
  have prefixOrder := layout.protected_prefix
  have internalStatus : layout.internalResult ≤ layout.internalStatus := by
    simp only [FrameLayout.internalStatus]; omega
  have ensFits : frei (D.params f) layout.ensReserved ≤ K := by
    simp only [frei] at fits ⊢
    omega
  obtain ⟨m1, moved1, changed1, env1⟩ := relocate_env frame small
    (by simpa only [Nat.zero_add] using ensFits) env (codeAt_left code)
    (by simpa only [relocateC_length] using (codeFar_left
      (n := (relocateC FB layout.ensReserved (contextWords (D.params f))).length)
      (k := (snap ++ relocateC layout.ensParams (layout.bodyReserved - layout.ensReserved)
        (contextWords (D.params f))).length) (by simpa only [List.length_append] using far)))
  have first := Agree.widen changed1 (by simpa only [Nat.zero_add] using ensFits)
  have frame1 := frame.agree first
  have world1 := weltAt_stab layoutIn separated m m1 world (first.mono (Nat.zero_le _))
  have far1 := codeFar_tail (a := relocateC FB layout.ensReserved (contextWords (D.params f))) far
  have code1 := (codeAt_right code).agree first far1
  simp only [relocateC_length] at code1 far1
  obtain ⟨m2, captured, changed2, saved⟩ := EntrySnapshots.capture_world_ok emitted frame1 small
    (by rw [snapshotEnd]; have := ensFits; unfold frei at this; omega)
    (codeAt_left code1) (codeFar_left (by rw [← List.length_append]; exact far1))
    world1 layoutIn separated
  have second : Agree fp FB K m1 m2 := Agree.widen changed2
    (by rw [snapshotEnd]; have := ensFits; unfold frei at this; omega)
  have frame2 := frame1.agree second
  have env2 : EnvAt L m2 fp ρ layout.ensReserved :=
    EntrySnapshots.envAt_above (by simpa only [Nat.zero_add] using env1)
      changed2 frame1 (by rw [snapshotEnd]; rfl) ensFits
  have world2 := weltAt_stab layoutIn separated m1 m2 world1 (second.mono (Nat.zero_le _))
  have far2 := codeFar_tail (a := snap) far1
  have code2 := (codeAt_right code1).agree second far2
  have shift : layout.ensReserved + (layout.bodyReserved - layout.ensReserved) =
      layout.bodyReserved := by omega
  obtain ⟨m3, moved3, changed3, lexical⟩ := relocate_env frame2 small
    (by rw [shift]; exact fits) env2 code2
    (by simpa only [relocateC_length] using far2)
  have third : Agree fp layout.bodyParams K m2 m3 := by
    simpa only [shift, FrameLayout.bodyParams, Nat.add_assoc] using
      (Agree.widen (K := K) changed3 (by rw [shift]; exact fits))
  have original := envAt_agree env2 third frame2 (by rw [paramEnd]; exact internalStatus.trans (Nat.le_of_lt prefixOrder.2)) bodyFits
  have saved3 := saved.agree frame2 third
    (by rw [snapshotEnd]; exact prefixOrder.1.trans (internalStatus.trans (Nat.le_of_lt prefixOrder.2)))
    bodyFits
  have world3 := weltAt_stab layoutIn separated m2 m3 world2 (third.mono (Nat.zero_le _))
  refine ⟨m3, ?_, (first.mono (by unfold FB; omega)).trans
    (second.trans (third.mono (by unfold FrameLayout.bodyParams; omega))),
    original, by simpa only [shift] using lexical, saved3, world3⟩
  have sizes : contextWords (D.params f) + (snap.length + contextWords (D.params f)) =
      2 * contextWords (D.params f) + snap.length := by omega
  simpa only [Nat.zero_add, relocateC_length, pc_add, Nat.add_assoc, sizes]
    using moved1.trans (captured.trans moved3)

end Gabbro.Stage0.Senke
