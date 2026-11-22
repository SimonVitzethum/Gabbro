module

public import Stage0.Senke.Bild.ImageAddress
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- The main start stub follows exactly the emitted clone sites. The
    serialized depth and private frame limits are shared with child starts. -/
theorem Emitted.main_stub_code [Kern] (output : Emitted src reserve options) {memory : Mem}
    (loaded : BytesAt memory codeBase (output.image.code.flatMap encII)) :
    let pc := BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length))
    CodeAt memory pc (startC output.image.A output.compiled.main output.image.depth 231 true) ∧
      2 < output.image.Ks ∧ output.image.depth + 1 < 2 ^ 31 ∧
      startScratch output.compiled.main + 8 ≤ output.image.Ks ∧ output.image.Ks < 2 ^ 31 := by
  intro pc
  obtain ⟨_, lowered, spawnSites, layout, serialized, _, _, _⟩ :=
    bild_lage output.emission output.funktionen_voll
      (fun base bound => layU_in output.compiled.unit output.tor base bound)
      (fun base => layU_dis output.compiled.unit output.tor base)
      (fun base => by simp only [layU]; omega)
      (fun base => layU_sync output.compiled.unit output.tor base)
  have actual := codeAt_bytes _ codeBase layout.hops (serialized ▸ loaded)
  have main := codeAt_right (a := spawnC (startScratch output.compiled.main) spawnSites) (by
    simpa only [Emitted.starts, List.append_assoc] using actual :
      CodeAt memory (BitVec.ofNat 64 codeBase)
        (spawnC (startScratch output.compiled.main) spawnSites ++
          (startC output.image.A output.compiled.main output.image.depth 231 true ++
            (rootsC output.image.A output.image.depth (output.starts.map (·.1)) ++ lowered))))
  have sites : (spawnC (startScratch output.compiled.main) spawnSites).length = 10 * output.starts.length := by
    simp only [spawnC_len, layout.hsp, List.length_map, List.length_range, Emitted.starts]
  rw [sites, ofNat_add64] at main
  exact ⟨codeAt_left main, layout.startLimits.1, layout.startLimits.2.1,
    layout.hex output.compiled.main List.mem_cons_self, layout.startLimits.2.2⟩


/-- The actual start site carries its decoded stub and its position in the
    declared stack reservation, for main as well as for each child. -/
structure ImageStartSite [Kern] (output : Emitted src reserve options) where
  thread : Nat
  bounded : thread ≤ output.starts.length
  pc : W
  fn : (declOf output.compiled.unit).Fn
  args : Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params fn)
  exit : Nat
  keep : Bool
  stub : ∀ {memory : Mem}, BytesAt memory codeBase (output.image.code.flatMap encII) →
    CodeAt memory pc (startC output.image.A fn output.image.depth exit keep) ∧
    2 < output.image.Ks ∧ output.image.depth + 1 < 2 ^ 31 ∧
    startScratch fn + 8 ≤ output.image.Ks ∧ output.image.Ks < 2 ^ 31

def ImageStartSite.entry [Kern] {output : Emitted src reserve options} (site : ImageStartSite output) : T :=
  ⟨site.pc, BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * site.thread))⟩

def Emitted.mainStartSite [Kern] (output : Emitted src reserve options) : ImageStartSite output where
  thread := 0
  bounded := Nat.zero_le _
  pc := BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length))
  fn := output.compiled.main
  args := output.args
  exit := 231
  keep := true
  stub := output.main_stub_code

def Emitted.childStartSite [Kern] (output : Emitted src reserve options)
    {index : Nat} {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root) : ImageStartSite output where
  thread := index + 1
  bounded := Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp declared).1
  pc := BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index))
  fn := root.1
  args := root.2
  exit := 60
  keep := false
  stub := fun loaded => output.root_stub_code loaded declared

/-- The first call-tail instruction writes the decrement operand in the
    scratch word immediately after the serialized parameter span. -/
theorem ImageStartSite.call_decrement_operand [Kern] {output : Emitted src reserve options}
    {before : Runner.Mach.Cfg imageTSO (Runner.Res T)}
    (site : ImageStartSite output)
    (loaded : BytesAt (before.ms.1.view site.thread) codeBase (output.image.code.flatMap encII)) :
    let entry := site.entry
    let scratch := FB + FB + contextWords ((declOf output.compiled.unit).params site.fn)
    before.ths[site.thread]? = some (some (.next (nxt entry))) →
    FrameOK (before.ms.1.view site.thread) entry.fp output.image.Ks →
    ∃ after : imageTSO.St,
      Runner.Mach.ProcessPrefix imageTSO Runner.Beweis.actI before [] 5
        ⟨after, before.ths.set site.thread (some (.next (nxt (nxt entry))))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view site.thread =
        Mem.write (before.ms.1.view site.thread) (slot entry.fp (BitVec.ofNat 64 scratch)) 8 1 ∧
      ∀ other, other ≠ site.thread → after.1.view other = before.ms.1.view other := by
  intro entry scratch running frame
  obtain ⟨stub, _, _, exitRoom, signed⟩ := site.stub loaded
  have callRoom : scratch < output.image.Ks := by
    have margin := startScratch_ge site.fn
    dsimp only [scratch]
    omega
  have instruction : InsAt (before.ms.1.view site.thread) (nxt entry).pc 1
      (II.f (scratch : Int)) (II.f 1) (II.f 0) := by
    have first := stub 1 (by rw [startC_len]; decide)
    change InsAt _ (entry.pc + BitVec.ofNat 64 (16 * 1)) 1 (II.f (scratch : Int)) (II.f 1) (II.f 0)
    simpa only [scratch, entry, ImageStartSite.entry, startC, callTail, callTailN, ci, List.singleton_append, List.cons_append,
      List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero] using first
  have destination : sx (II.f (scratch : Int)) = BitVec.ofNat 64 scratch := sx_nat (callRoom.trans signed)
  have operand : (sx (II.f 1)).toNat = 1 := by decide
  have writable : Mem.all before.ms.1.m.wr (slot entry.fp (sx (II.f (scratch : Int)))) 8 = true := by
    rw [destination, ← Runner.Beweis.foldl_wr (before.ms.1.buf site.thread) before.ms.1.m]
    exact frame.wr scratch callRoom
  obtain ⟨after, run, memory, view, others⟩ :=
    tso_const_prefix (before := imageToTSO before) running instruction writable
  refine ⟨after, tso_silent_prefix_image run rfl, memory, ?_, others⟩
  rw [view, destination, operand] <;> rfl

/-- The emitted subtraction installs the exact model call depth in
    the child's callee frame, before the jump into lowered code. -/
theorem ImageStartSite.call_depth [Kern] {output : Emitted src reserve options}
    {before : Runner.Mach.Cfg imageTSO (Runner.Res T)}
    (site : ImageStartSite output)
    (loaded : BytesAt (before.ms.1.view site.thread) codeBase (output.image.code.flatMap encII)) :
    let entry := site.entry
    let scratch := FB + FB + contextWords ((declOf output.compiled.unit).params site.fn)
    before.ths[site.thread]? = some (some (.next (nxt (nxt entry)))) →
    FrameOK (before.ms.1.view site.thread) entry.fp output.image.Ks →
    (before.ms.1.view site.thread).rd64 (slot entry.fp (BitVec.ofNat 64 2)) =
      some (BitVec.ofNat 64 (output.image.depth + 1)) →
    (before.ms.1.view site.thread).rd64 (slot entry.fp (BitVec.ofNat 64 scratch)) = some 1 →
    ∃ after : imageTSO.St,
      Runner.Mach.ProcessPrefix imageTSO Runner.Beweis.actI before [] 8
        ⟨after, before.ths.set site.thread (some (.next (nxt (nxt (nxt entry)))))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view site.thread =
        Mem.write (before.ms.1.view site.thread) (slot entry.fp (BitVec.ofNat 64 (FB + 2))) 8 output.image.depth ∧
      ∀ other, other ≠ site.thread → after.1.view other = before.ms.1.view other := by
  intro entry scratch running frame depth one
  obtain ⟨stub, _, depthFits, exitRoom, signed⟩ := site.stub loaded
  have callRoom : scratch < output.image.Ks := by
    have margin := startScratch_ge site.fn
    dsimp only [scratch]
    omega
  have calleeRoom : FB + 2 < output.image.Ks := by
    dsimp only [scratch] at callRoom
    simp only [FB] at callRoom ⊢
    omega
  have instruction : InsAt (before.ms.1.view site.thread) (nxt (nxt entry)).pc 4
      (II.f ((FB + 2 : Nat) : Int)) (II.f 2) (II.f (scratch : Int)) := by
    have subtract := stub 2 (by rw [startC_len]; decide)
    rw [show (nxt (nxt entry)).pc = entry.pc + BitVec.ofNat 64 (16 * 2) by
      change entry.pc + 16 + 16 = _
      rw [BitVec.add_assoc]
      rfl]
    simpa only [entry, ImageStartSite.entry, scratch, startC, callTail, callTailN, ci, List.singleton_append, List.cons_append,
      List.nil_append, List.getElem_cons_succ, List.getElem_cons_zero] using subtract
  have out : sx (II.f ((FB + 2 : Nat) : Int)) = BitVec.ofNat 64 (FB + 2) := sx_nat (calleeRoom.trans signed)
  have lhs : sx (II.f 2) = BitVec.ofNat 64 2 := by decide
  have rhs : sx (II.f (scratch : Int)) = BitVec.ofNat 64 scratch := sx_nat (callRoom.trans signed)
  have writable : Mem.all before.ms.1.m.wr (slot entry.fp (sx (II.f ((FB + 2 : Nat) : Int)))) 8 = true := by
    rw [out, ← Runner.Beweis.foldl_wr (before.ms.1.buf site.thread) before.ms.1.m]
    exact frame.wr _ calleeRoom
  have subtract : (fun a b : W => some (a - b)) (BitVec.ofNat 64 (output.image.depth + 1)) 1 =
      some (BitVec.ofNat 64 output.image.depth) := by
    change some (BitVec.ofNat 64 (output.image.depth + 1) - BitVec.ofNat 64 1) = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (output.image.depth + 1) 1 (by decide) (by omega),
      Nat.add_sub_cancel]
  obtain ⟨after, run, shared, view, others⟩ := tso_binary_prefix
    (before := imageToTSO before) (compute := fun a b => some (a - b)) rfl (by decide)
    running instruction (by rw [lhs]; exact depth) (by rw [rhs]; exact one) subtract writable
  refine ⟨after, tso_silent_prefix_image run rfl, shared, ?_, others⟩
  rw [view, out, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ((Nat.lt_succ_self _).trans (depthFits.trans (by decide : 2 ^ 31 < 2 ^ 64)))] <;> rfl

/-- The first stub instruction leaves its exact arguments, frame
    permissions and code intact. The issuing view holds the depth word
    before the store is flushed to shared memory. -/
theorem ImageStartSite.depth_preserves_frame [Kern] {output : Emitted src reserve options}
    {before : Runner.Mach.Cfg imageTSO (Runner.Res T)}
    (site : ImageStartSite output)
    (loaded : BytesAt (before.ms.1.view site.thread) codeBase (output.image.code.flatMap encII)) :
    let pointer := site.entry
    let words := encodeEnv output.image.Y site.args
    before.ths[site.thread]? = some (some (.next pointer)) →
    FrameOK (before.ms.1.view site.thread) pointer.fp output.image.Ks →
    FB + FB + words.length ≤ output.image.Ks →
    WordsAt (before.ms.1.view site.thread) pointer.fp (FB + FB) words →
    ∃ after : imageTSO.St,
      Runner.Mach.ProcessPrefix imageTSO Runner.Beweis.actI before [] 5
        ⟨after, before.ths.set site.thread (some (.next (nxt pointer)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      (∀ other, other ≠ site.thread → after.1.view other = before.ms.1.view other) ∧
      BytesAt (after.1.view site.thread) codeBase (output.image.code.flatMap encII) ∧
      FrameOK (after.1.view site.thread) pointer.fp output.image.Ks ∧
      WordsAt (after.1.view site.thread) pointer.fp (FB + FB) words ∧
      (after.1.view site.thread).rd64 (slot pointer.fp (BitVec.ofNat 64 2)) =
        some (BitVec.ofNat 64 (output.image.depth + 1)) ∧
      Agree pointer.fp 0 output.image.Ks (before.ms.1.view site.thread) (after.1.view site.thread) := by
  intro pointer words running frame fits args
  obtain ⟨stub, depthSlot, depthFits, _, _⟩ := site.stub loaded
  obtain ⟨after, run, memory, wroteDepth, others⟩ := image_depth_setup stub depthSlot depthFits running frame
  refine ⟨after, run, memory, others, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [wroteDepth]
  · apply output.code_survives_writes (write_nurIn _ _ _) _ loaded
    intro byte touched
    have own := imageStackFootprint_slot (output := output) (i := site.thread)
      (index := 2) site.bounded depthSlot touched
    exact (Nat.le_add_right _ _).trans own.2.1
  · exact ⟨frame.lt, frame.rd, frame.wr⟩
  · intro i present
    have within : FB + FB + i < output.image.Ks := by omega
    have elsewhere : 2 ≠ FB + FB + i := by simp only [FB]; omega
    rw [Mem.rd64_write_far (slot_far frame.room depthSlot within elsewhere)]
    exact args i present
  · have word := rd64_write_same (w := BitVec.ofNat 64 (output.image.depth + 1)) (frame.rd 2 depthSlot)
    simpa only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (depthFits.trans (by decide : 2 ^ 31 < 2 ^ 64))] using word
  · exact agree_write frame.room (Nat.zero_le _) depthSlot _

/-- The concrete child startup prefix advances the IR counter within
    the child's stub and retains the same dormant GX head. -/
theorem Emitted.root_depth_phase [Kern] (output : Emitted src reserve options)
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    {before : Runner.Mach.Cfg imageTSO (Runner.Res T)} {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root)
    {history : List Runner.Mach.Ev} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (head : state.m.faeden (index + 1) = (imageSourceStart E).m.faeden (index + 1)) :
    let pointer : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))⟩
    let view := before.ms.1.view (index + 1)
    before.ths[index + 1]? = some (some (.next pointer)) →
    ImageRootPhase output E history view (index + 1) (.next pointer) state →
    FB + FB + (encodeEnv output.image.Y root.2).length ≤ output.image.Ks →
    ∃ after : imageTSO.St,
      Runner.Mach.ProcessPrefix imageTSO Runner.Beweis.actI before [] 5
        ⟨after, before.ths.set (index + 1) (some (.next (nxt pointer)))⟩ ∧
      ImageRootPhase output E history (after.1.view (index + 1)) (index + 1) (.next (nxt pointer)) state ∧
      after.1.m = before.ms.1.m ∧
      (∀ other, other ≠ index + 1 → after.1.view other = before.ms.1.view other) ∧
      (after.1.view (index + 1)).rd64 (slot pointer.fp (BitVec.ofNat 64 2)) =
        some (BitVec.ofNat 64 (output.image.depth + 1)) := by
  intro pointer view running phase fits
  have exported : E.starts[index + 1]? = some root := by rw [unit.starts]; exact declared
  obtain ⟨code, frame, args⟩ := output.child_phase_payload unit declared phase
  have address (i : Nat) : slot pointer.fp (BitVec.ofNat 64 (FB + FB + i)) =
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)) + 8 * (FB + FB + i)) := by
    change BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1))) +
      BitVec.ofNat 64 (FB + FB + i) * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm (FB + FB + i) 8]
  obtain ⟨after, run, shared, others, loaded, permissions, words, depth, _⟩ :=
    (output.childStartSite declared).depth_preserves_frame code running frame fits args
  refine ⟨after, run, Or.inr ⟨root, exported, Or.inl head, loaded, permissions, ?_, ?_⟩, shared, others, depth⟩
  · intro i present
    rw [← address i]
    exact words i present
  · refine ⟨nxt pointer, ⟨rfl, 10 * output.starts.length + startLen + startLen * index + 1, ?_, ?_, ?_⟩, Or.inl rfl⟩
    · simp only [Nat.succ_ne_zero, ite_false, startLen]; omega
    · simp only [Nat.succ_ne_zero, ite_false, startLen]; omega
    · change BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)) +
          BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1

end Gabbro.Stage0
