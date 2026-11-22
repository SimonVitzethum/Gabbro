module

public import Stage0.Senke.Bild.ImageAddress
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- The last immediate of the child's call tail materializes the actual
    lowered address in its scratch slot, with code and frame rights intact. -/
theorem Emitted.root_call_target [Kern] (output : Emitted src reserve options)
    {before : Cfg imageTSO (Res T)} {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root)
    (bytes : BytesAt (before.ms.1.view (index + 1)) codeBase (output.image.code.flatMap encII)) :
    let entry := BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index))
    let fp := BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))
    let pointer : T := ⟨entry + BitVec.ofNat 64 (16 * 3), fp⟩
    let scratch := FB + FB + contextWords ((declOf output.compiled.unit).params root.1)
    before.ths[index + 1]? = some (some (.next pointer)) →
    FrameOK (before.ms.1.view (index + 1)) fp output.image.Ks →
    ∃ after : imageTSO.St,
      ProcessPrefix imageTSO actI before [] 5
        ⟨after, before.ths.set (index + 1) (some (.next (nxt pointer)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      (∀ other, other ≠ index + 1 → after.1.view other = before.ms.1.view other) ∧
      after.1.view (index + 1) =
        Mem.write (before.ms.1.view (index + 1)) (slot fp (BitVec.ofNat 64 scratch)) 8 (output.image.A root.1) ∧
      BytesAt (after.1.view (index + 1)) codeBase (output.image.code.flatMap encII) ∧
      FrameOK (after.1.view (index + 1)) fp output.image.Ks ∧
      (after.1.view (index + 1)).rd64 (slot fp (BitVec.ofNat 64 scratch)) =
        some (BitVec.ofNat 64 (output.image.A root.1)) := by
  intro entry fp pointer scratch running frame
  obtain ⟨stub, _, _, exitRoom, signed⟩ := output.root_stub_code bytes declared
  obtain ⟨_, _, _, _, _, targetFits⟩ := output.relocated_function_code bytes root.1
  have callRoom : scratch < output.image.Ks := by
    have margin := startScratch_ge root.1
    dsimp only [scratch]
    omega
  have instruction : InsAt (before.ms.1.view (index + 1)) pointer.pc 1
      (II.f (scratch : Int)) (II.f ((output.image.A root.1 : Nat) : Int)) (II.f 0) := by
    have immediate := stub 3 (by rw [startC_len]; decide)
    simpa only [pointer, entry, scratch, startC, callTail, callTailN, ci, List.singleton_append, List.cons_append,
      List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero, Bool.false_eq_true, ↓reduceIte] using immediate
  have dest : sx (II.f (scratch : Int)) = BitVec.ofNat 64 scratch := sx_nat (callRoom.trans signed)
  have target : sx (II.f ((output.image.A root.1 : Nat) : Int)) = BitVec.ofNat 64 (output.image.A root.1) :=
    sx_nat targetFits
  have writable : Mem.all before.ms.1.m.wr (slot fp (sx (II.f (scratch : Int)))) 8 = true := by
    rw [dest, ← foldl_wr (before.ms.1.buf (index + 1)) before.ms.1.m]
    exact frame.wr _ callRoom
  obtain ⟨after, run, memory, view, others⟩ :=
    tso_const_prefix (before := imageToTSO before) running instruction writable
  have small := targetFits.trans (by decide : 2 ^ 31 < 2 ^ 64)
  have written : after.1.view (index + 1) =
      Mem.write (before.ms.1.view (index + 1)) (slot fp (BitVec.ofNat 64 scratch)) 8 (output.image.A root.1) := by
    rw [view, dest, target, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] <;> rfl
  refine ⟨after, tso_silent_prefix_image run rfl, memory, others, written, ?_, ?_, ?_⟩ <;> rw [written]
  · apply output.code_survives_writes (write_nurIn _ _ _) _ bytes
    intro byte touched
    have declaredThread := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp declared).1
    have reserved := imageStackFootprint_slot (output := output) (i := index + 1) declaredThread callRoom touched
    exact (Nat.le_add_right _ _).trans reserved.2.1
  · exact ⟨frame.lt, frame.rd, frame.wr⟩
  · have exactWord := rd64_write_same (w := BitVec.ofNat 64 (output.image.A root.1)) (frame.rd scratch callRoom)
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using exactWord

/-- The child's actual call enters the relocated body. The two return
    header stores preserve its serialized arguments and model depth. -/
theorem Emitted.root_call_enter [Kern] (output : Emitted src reserve options)
    {before : Cfg imageTSO (Res T)} {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root)
    (bytes : BytesAt (before.ms.1.view (index + 1)) codeBase (output.image.code.flatMap encII)) :
    let entry := BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index))
    let fp := BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))
    let pointer : T := ⟨entry + BitVec.ofNat 64 (16 * 4), fp⟩
    let scratch := FB + FB + contextWords ((declOf output.compiled.unit).params root.1)
    let target := BitVec.ofNat 64 (output.image.A root.1)
    let frame := slot fp (BitVec.ofNat 64 FB)
    let words := encodeEnv output.image.Y root.2
    before.ths[index + 1]? = some (some (.next pointer)) →
    FrameOK (before.ms.1.view (index + 1)) fp output.image.Ks →
    (before.ms.1.view (index + 1)).rd64 (slot fp (BitVec.ofNat 64 scratch)) = some target →
    (before.ms.1.view (index + 1)).rd64 (slot fp (BitVec.ofNat 64 (FB + 2))) =
      some (BitVec.ofNat 64 output.image.depth) →
    WordsAt (before.ms.1.view (index + 1)) fp (FB + FB) words →
    ∃ after : imageTSO.St,
      ProcessPrefix imageTSO actI before [] 7
        ⟨after, before.ths.set (index + 1) (some (.next ⟨target, frame⟩))⟩ ∧
      after.1.m = before.ms.1.m ∧
      (∀ other, other ≠ index + 1 → after.1.view other = before.ms.1.view other) ∧
      Agree fp 0 output.image.Ks (before.ms.1.view (index + 1)) (after.1.view (index + 1)) ∧
      FrameOK (after.1.view (index + 1)) frame (output.image.Ks - FB) ∧
      WordsAt (after.1.view (index + 1)) frame FB words ∧
      (after.1.view (index + 1)).rd64 (slot frame (BitVec.ofNat 64 0)) = some (nxt pointer).pc ∧
      (after.1.view (index + 1)).rd64 (slot frame (BitVec.ofNat 64 1)) = some fp ∧
      (after.1.view (index + 1)).rd64 (slot frame (BitVec.ofNat 64 2)) =
        some (BitVec.ofNat 64 output.image.depth) ∧
      ∃ code top, lowFun output.image.passes output.compiled.program output.image.A output.image.Y root.1 =
        some (code, top) ∧ CodeAt (after.1.view (index + 1)) target code := by
  intro entry fp pointer scratch target frame words running frameOK loadedTarget depth args
  obtain ⟨stub, _, _, exitRoom, signed⟩ := output.root_stub_code bytes declared
  have margin := startScratch_ge root.1
  have scratchRoom : scratch < output.image.Ks := by dsimp only [scratch]; omega
  have headRoom : FB + 2 < output.image.Ks := by dsimp only [scratch] at scratchRoom; simp only [FB] at *; omega
  have instruction : InsAt (before.ms.1.view (index + 1)) pointer.pc 20
      (II.f (scratch : Int)) (II.f (FB : Int)) (II.f 0) := by
    have call := stub 4 (by rw [startC_len]; decide)
    simpa only [pointer, entry, scratch, startC, callTail, callTailN, ci, List.singleton_append, List.cons_append,
      List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero] using call
  have targetSlot : sx (II.f (scratch : Int)) = BitVec.ofNat 64 scratch := sx_nat (scratchRoom.trans signed)
  have frameSlot : sx (II.f (FB : Int)) = BitVec.ofNat 64 FB := sx_nat (by omega)
  have writablePC : Mem.all before.ms.1.m.wr (slot pointer.fp (sx (II.f (FB : Int)))) 8 = true := by
    rw [frameSlot, ← foldl_wr (before.ms.1.buf (index + 1)) before.ms.1.m]
    exact frameOK.wr FB (by omega)
  have writableFP : Mem.all before.ms.1.m.wr (slot pointer.fp (sx (II.f (FB : Int))) + 8) 8 = true := by
    rw [frameSlot, slot_plus8, ← foldl_wr (before.ms.1.buf (index + 1)) before.ms.1.m]
    exact frameOK.wr (FB + 1) (by omega)
  obtain ⟨after, run, shared, view, others⟩ := tso_call_prefix (before := imageToTSO before)
    running instruction (by rw [targetSlot]; exact loadedTarget) writablePC writableFP
  rw [frameSlot] at run view
  rw [slot_plus8] at view
  have frameAfter : FrameOK (after.1.view (index + 1)) fp output.image.Ks := by
    rw [view]
    exact ⟨frameOK.lt, frameOK.rd, frameOK.wr⟩
  have unchanged (i : Nat) (inside : i < output.image.Ks) (below : FB + 2 ≤ i) :
      (after.1.view (index + 1)).rd64 (slot fp (BitVec.ofNat 64 i)) =
        (before.ms.1.view (index + 1)).rd64 (slot fp (BitVec.ofNat 64 i)) := by
    rw [view, Mem.rd64_write_far (slot_far frameOK.room (by omega) inside (by omega)),
      Mem.rd64_write_far (slot_far frameOK.room (by omega) inside (by omega))]
    rfl
  have updatedCode : BytesAt (after.1.view (index + 1)) codeBase (output.image.code.flatMap encII) := by
    have above (slotNo : Nat) (inside : slotNo < output.image.Ks)
        (byte : W) (touched : fenster (slot fp (BitVec.ofNat 64 slotNo)) byte) :
        output.image.fp0 ≤ byte.toNat := by
      have declaredThread := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp declared).1
      have reserved := imageStackFootprint_slot (output := output) (i := index + 1) declaredThread inside touched
      exact (Nat.le_add_right _ _).trans reserved.2.1
    rw [view]
    exact output.code_survives_writes (write_nurIn _ _ _) (above (FB + 1) (by omega))
      (output.code_survives_writes (write_nurIn _ _ _) (above FB (by omega)) bytes)
  have confined : Agree fp 0 output.image.Ks (before.ms.1.view (index + 1)) (after.1.view (index + 1)) := by
    rw [view]
    exact (agree_write frameOK.room (Nat.zero_le FB) (by omega) _).trans
      (agree_write frameOK.room (Nat.zero_le (FB + 1)) (by omega) _)
  refine ⟨after, tso_silent_prefix_image run rfl, shared, others, confined,
    frame_sub frameAfter (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro i inWords
    have within : FB + FB + i < output.image.Ks := by
      have count : words.length = contextWords ((declOf output.compiled.unit).params root.1) := encodeEnv_length _ _
      dsimp only [scratch] at scratchRoom
      omega
    change (after.1.view (index+1)).rd64 (slot (slot fp (BitVec.ofNat 64 FB)) (BitVec.ofNat 64 (FB + i))) = _
    rw [slot_slot, ← Nat.add_assoc, unchanged _ within (by simp only [FB]; omega)]
    exact args i inWords
  · change (after.1.view (index + 1)).rd64 (slot (slot fp (BitVec.ofNat 64 FB)) (BitVec.ofNat 64 0)) = _
    rw [slot_slot, Nat.add_zero, view]
    change (Mem.write (Mem.write (before.ms.1.view (index + 1)) (slot fp (BitVec.ofNat 64 FB)) 8
      (nxt pointer).pc.toNat) (slot fp (BitVec.ofNat 64 (FB + 1))) 8 fp.toNat).rd64
        (slot fp (BitVec.ofNat 64 FB)) = _
    rw [Mem.rd64_write_far (slot_far frameOK.room (i := FB + 1) (j := FB) (by omega) (by omega) (by omega))]
    exact rd64_write_same (frameOK.rd FB (by omega))
  · change (after.1.view (index + 1)).rd64 (slot (slot fp (BitVec.ofNat 64 FB)) (BitVec.ofNat 64 1)) = _
    rw [slot_slot, view]
    exact rd64_write_same (frameOK.rd (FB + 1) (by omega))
  · change (after.1.view (index+1)).rd64 (slot (slot fp (BitVec.ofNat 64 FB)) (BitVec.ofNat 64 2)) = _
    rw [slot_slot, unchanged _ headRoom (Nat.le_refl _)]
    exact depth
  · obtain ⟨code, top, lowered, exactCode, _, _⟩ := output.relocated_function_code updatedCode root.1
    exact ⟨code, top, lowered, exactCode⟩

private theorem child_store_preserves [Kern] (output : Emitted src reserve options)
    {index slotNo value : Nat} {memory : Mem} {words : List W}
    (declared : index + 1 ≤ output.starts.length) (inside : slotNo < output.image.Ks)
    (fits : FB + FB + words.length ≤ output.image.Ks)
    (outsideArgs : slotNo < FB + FB ∨ FB + FB + words.length ≤ slotNo)
    (loaded : BytesAt memory codeBase (output.image.code.flatMap encII)) :
    let fp := BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))
    let after := Mem.write memory (slot fp (BitVec.ofNat 64 slotNo)) 8 value
    FrameOK memory fp output.image.Ks →
    WordsAt memory fp (FB + FB) words →
    BytesAt after codeBase (output.image.code.flatMap encII) ∧
      FrameOK after fp output.image.Ks ∧ WordsAt after fp (FB + FB) words := by
  intro fp after frame args
  refine ⟨output.code_survives_writes (write_nurIn _ _ _) ?_ loaded, ⟨frame.lt, frame.rd, frame.wr⟩, ?_⟩
  · intro byte touched
    have reserved := imageStackFootprint_slot (output := output) (i := index + 1) declared inside touched
    exact (Nat.le_add_right _ _).trans reserved.2.1
  · intro i present
    change (Mem.write memory (slot fp (BitVec.ofNat 64 slotNo)) 8 value).rd64
      (slot fp (BitVec.ofNat 64 (FB + FB + i))) = _
    have different : slotNo ≠ FB + FB + i := by rcases outsideArgs with lower | upper <;> omega
    rw [Mem.rd64_write_far (slot_far frame.room inside (by omega) different)]
    exact args i present

/-- From its serialized entry, the actual child stub reaches the exact
    emitted function body with the declared arguments and depth. This
    prefix only schedules the child and leaves other views untouched. -/
theorem Emitted.child_body_prefix [Kern] (output : Emitted src reserve options)
    {before : Cfg imageTSO (Res T)} {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root)
    (bytes : BytesAt (before.ms.1.view (index + 1)) codeBase (output.image.code.flatMap encII)) :
    let entry : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))⟩
    let target := BitVec.ofNat 64 (output.image.A root.1)
    let frame := slot entry.fp (BitVec.ofNat 64 FB)
    let words := encodeEnv output.image.Y root.2
    before.ths[index + 1]? = some (some (.next entry)) →
    FrameOK (before.ms.1.view (index + 1)) entry.fp output.image.Ks →
    WordsAt (before.ms.1.view (index + 1)) entry.fp (FB + FB) words →
    ∃ after : imageTSO.St,
      ProcessPrefix imageTSO actI before [] 30
        ⟨after, before.ths.set (index + 1) (some (.next ⟨target, frame⟩))⟩ ∧
      after.1.m = before.ms.1.m ∧
      (∀ other, other ≠ index + 1 → after.1.view other = before.ms.1.view other) ∧
      Agree entry.fp 0 output.image.Ks (before.ms.1.view (index + 1)) (after.1.view (index + 1)) ∧
      FrameOK (after.1.view (index + 1)) frame (output.image.Ks - FB) ∧
      WordsAt (after.1.view (index + 1)) frame FB words ∧
      (after.1.view (index + 1)).rd64 (slot frame (BitVec.ofNat 64 0)) =
        some (nxt ⟨entry.pc + BitVec.ofNat 64 (16 * 4), entry.fp⟩).pc ∧
      (after.1.view (index + 1)).rd64 (slot frame (BitVec.ofNat 64 1)) = some entry.fp ∧
      (after.1.view (index + 1)).rd64 (slot frame (BitVec.ofNat 64 2)) =
        some (BitVec.ofNat 64 output.image.depth) ∧
      ∃ code top, lowFun output.image.passes output.compiled.program output.image.A output.image.Y root.1 =
        some (code, top) ∧ CodeAt (after.1.view (index + 1)) target code := by
  intro entry target frame words running frameOK arguments
  let scratch := FB + FB + contextWords ((declOf output.compiled.unit).params root.1)
  have wordCount : FB + FB + words.length = scratch := by simp only [words, scratch, encodeEnv_length]
  obtain ⟨_, two, _, room, _⟩ := output.root_stub_code bytes declared
  have declaredThread := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp declared).1
  have scratchRoom : scratch < output.image.Ks := by
    have margin := startScratch_ge root.1
    dsimp only [scratch]
    omega
  have calleeRoom : FB + 2 < output.image.Ks := by dsimp only [scratch] at scratchRoom; simp only [FB] at *; omega
  have fits : FB + FB + words.length ≤ output.image.Ks := by rw [wordCount]; exact scratchRoom.le
  obtain ⟨first, depthRun, shared₁, others₁, code₁, frame₁, args₁, depth₁, writes₁⟩ :=
    output.root_depth_preserves_frame declared bytes running frameOK fits arguments
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have onThread (control : Res T) : (before.ths.set (index + 1) (some control))[index + 1]? = some (some control) :=
    List.getElem?_set_self inside
  obtain ⟨second, operandRun, shared₂, write₂, others₂⟩ :=
    output.root_call_decrement_operand (before := ⟨first, before.ths.set (index + 1) (some (.next (nxt entry)))⟩)
      declared code₁ (onThread (.next (nxt entry))) frame₁
  have preserved₂ := child_store_preserves output (value := 1)
    declaredThread scratchRoom fits (Or.inr wordCount.le) code₁ frame₁ args₁
  rw [← write₂] at preserved₂
  obtain ⟨code₂, frame₂, args₂⟩ := preserved₂
  have writes₂ : Agree entry.fp 0 output.image.Ks (first.1.view (index + 1)) (second.1.view (index + 1)) := by
    rw [write₂]
    exact agree_write frame₁.room (Nat.zero_le scratch) scratchRoom _
  have depth₂ : (second.1.view (index + 1)).rd64 (slot entry.fp (BitVec.ofNat 64 2)) =
      some (BitVec.ofNat 64 (output.image.depth + 1)) := by
    have separate : scratch ≠ 2 := by simp only [scratch, FB]; omega
    rw [write₂, Mem.rd64_write_far (slot_far frame₁.room scratchRoom two separate)]
    exact depth₁
  have one : (second.1.view (index + 1)).rd64 (slot entry.fp (BitVec.ofNat 64 scratch)) = some 1 := by
    rw [write₂]
    exact rd64_write_same (w := 1) (frame₁.rd scratch scratchRoom)
  simp only [List.set_set] at operandRun
  obtain ⟨third, subRun, shared₃, write₃, others₃⟩ :=
    output.root_call_depth (before := ⟨second, before.ths.set (index + 1) (some (.next (nxt (nxt entry))))⟩)
      declared code₂ (onThread (.next (nxt (nxt entry)))) frame₂ depth₂ one
  simp only [List.set_set] at subRun
  have preserved₃ := child_store_preserves output (value := output.image.depth) declaredThread calleeRoom fits
    (Or.inl (by simp only [FB]; decide)) code₂ frame₂ args₂
  rw [← write₃] at preserved₃
  obtain ⟨code₃, frame₃, args₃⟩ := preserved₃
  have writes₃ : Agree entry.fp 0 output.image.Ks (second.1.view (index + 1)) (third.1.view (index + 1)) := by
    rw [write₃]
    exact agree_write frame₂.room (Nat.zero_le (FB + 2)) calleeRoom _
  have depth₃ : (third.1.view (index + 1)).rd64 (slot entry.fp (BitVec.ofNat 64 (FB + 2))) =
      some (BitVec.ofNat 64 output.image.depth) := by
    obtain ⟨_, _, bound, _, _⟩ := output.root_stub_code bytes declared
    have small := (Nat.lt_succ_self _).trans (bound.trans (by decide : 2 ^ 31 < 2 ^ 64))
    have exactWord := rd64_write_same (w := BitVec.ofNat 64 output.image.depth) (frame₂.rd _ calleeRoom)
    rw [write₃]
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using exactWord
  let callConst : T := ⟨entry.pc + BitVec.ofNat 64 (16 * 3), entry.fp⟩
  have samePC : nxt (nxt (nxt entry)) = callConst := by
    change (⟨entry.pc + 16 + 16 + 16, entry.fp⟩ : T) = callConst
    rw [BitVec.add_assoc, BitVec.add_assoc] <;> rfl
  rw [samePC] at subRun
  obtain ⟨fourth, targetRun, shared₄, others₄, write₄, code₄, frame₄, targetWord⟩ :=
    output.root_call_target (before := ⟨third, before.ths.set (index + 1) (some (.next callConst))⟩)
      declared code₃ (onThread (.next callConst)) frame₃
  simp only [List.set_set] at targetRun
  have callPC : nxt callConst = ⟨entry.pc + BitVec.ofNat 64 (16 * 4), entry.fp⟩ := by
    change (⟨entry.pc + BitVec.ofNat 64 (16 * 3) + 16, entry.fp⟩ : T) = _
    rw [BitVec.add_assoc] <;> rfl
  rw [callPC] at targetRun
  have preserved₄ := child_store_preserves output (value := output.image.A root.1)
    declaredThread scratchRoom fits (Or.inr wordCount.le) code₃ frame₃ args₃
  rw [← write₄] at preserved₄
  have writes₄ : Agree entry.fp 0 output.image.Ks (third.1.view (index + 1)) (fourth.1.view (index + 1)) := by
    rw [write₄]
    exact agree_write frame₃.room (Nat.zero_le scratch) scratchRoom _
  have depth₄ : (fourth.1.view (index + 1)).rd64 (slot entry.fp (BitVec.ofNat 64 (FB + 2))) =
      some (BitVec.ofNat 64 output.image.depth) := by
    have separate : scratch ≠ FB + 2 := by simp only [scratch, FB]; omega
    rw [write₄, Mem.rd64_write_far (slot_far frame₃.room scratchRoom calleeRoom separate)]
    exact depth₃
  let call : T := ⟨entry.pc + BitVec.ofNat 64 (16 * 4), entry.fp⟩
  obtain ⟨after, callRun, shared₅, others₅, writes₅, body⟩ :=
    output.root_call_enter (before := ⟨fourth, before.ths.set (index + 1) (some (.next call))⟩)
      declared code₄ (onThread (.next call)) frame₄ targetWord depth₄ preserved₄.2.2
  simp only [List.set_set] at callRun
  refine ⟨after, ?_, shared₅.trans (shared₄.trans (shared₃.trans (shared₂.trans shared₁))), ?_,
    writes₁.trans (writes₂.trans (writes₃.trans (writes₄.trans writes₅))), body⟩
  · simpa only [List.nil_append] using (((depthRun.trans operandRun).trans subRun).trans targetRun).trans callRun
  · intro other different
    exact (others₅ other different).trans ((others₄ other different).trans
      ((others₃ other different).trans ((others₂ other different).trans (others₁ other different))))

/-- The root phase of the actual image supplies the serialized inputs
    for the complete silent prefix into its lowered function. -/
theorem Emitted.child_body_from_root_phase [Kern] (output : Emitted src reserve options)
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    {before : Cfg imageTSO (Res T)} {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root) {history : List Ev}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} :
    let entry : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))⟩
    let target := BitVec.ofNat 64 (output.image.A root.1)
    let frame := slot entry.fp (BitVec.ofNat 64 FB)
    before.ths[index + 1]? = some (some (.next entry)) →
    ImageRootPhase output E history (before.ms.1.view (index + 1)) (index + 1) (.next entry) state →
    ∃ after : imageTSO.St,
      ProcessPrefix imageTSO actI before [] 30
        ⟨after, before.ths.set (index + 1) (some (.next ⟨target, frame⟩))⟩ ∧
      after.1.m = before.ms.1.m ∧
      (∀ other, other ≠ index + 1 → after.1.view other = before.ms.1.view other) ∧
      (∀ world, WeltAt (before.ms.1.view (index + 1)) output.image.Y world →
        WeltAt (after.1.view (index + 1)) output.image.Y world) ∧
      FrameOK (after.1.view (index + 1)) frame (output.image.Ks - FB) ∧
      EnvAt output.image.Y (after.1.view (index + 1)) frame root.2 ∧
      (after.1.view (index + 1)).rd64 (slot frame (BitVec.ofNat 64 0)) =
        some (nxt ⟨entry.pc + BitVec.ofNat 64 (16 * 4), entry.fp⟩).pc ∧
      (after.1.view (index + 1)).rd64 (slot frame (BitVec.ofNat 64 1)) = some entry.fp ∧
      (after.1.view (index + 1)).rd64 (slot frame (BitVec.ofNat 64 2)) =
        some (BitVec.ofNat 64 output.image.depth) ∧
      ∃ code top, lowFun output.image.passes output.compiled.program output.image.A output.image.Y root.1 =
        some (code, top) ∧ CodeAt (after.1.view (index + 1)) target code := by
  intro entry target frame running phase
  obtain ⟨bytes, permissions, arguments⟩ := output.child_phase_payload unit declared phase
  obtain ⟨after, executed, shared, others, writes, frameOK, words, returnPC, callerFrame, depth, body⟩ :=
    output.child_body_prefix declared bytes running permissions arguments
  have valid := output.startPlan.starts_valid (initialWorld _ output.initialValid) output.image.Y root
    (List.mem_of_getElem? declared)
  have environment := (envAt_encoding (reserved := 0) (L := output.image.Y) root.2).mpr ⟨valid, words⟩
  have thread := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp declared).1
  exact ⟨after, executed, shared, others, fun _ stored => output.world_survives_stack thread stored writes,
    frameOK, environment, returnPC, callerFrame, depth, body⟩

end Gabbro.Stage0
