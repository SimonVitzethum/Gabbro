module

public import Stage0.Senke.Bild.Mehr.Ort.MemoryReference
public import Stage0.Senke.Start
import Stage0.Senke.Bild.ImageAddress
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Mem Runner.Beweis Runner.Mach BildLauf

private theorem spawnSite_memory [Kern]
    {memory : Mem} {pc fp : W} {slots scratch entry stack : Nat}
    (code : CodeAt memory pc (spawnOne scratch entry stack))
    (frame : FrameOK memory fp slots) (far : CodeFar pc 10 fp slots)
    (scratchFits : scratch + 2 ≤ slots) (slotsFit : slots < 2 ^ 31)
    (entryFits : entry < 2 ^ 31) (stackFits : stack < 2 ^ 31) :
    let parent : T := ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩
    let child : T := ⟨BitVec.ofNat 64 entry, BitVec.ofNat 64 stack⟩
    ∃ prepared, StarM 2 ⟨pc, fp⟩ memory parent prepared ∧
      RunP (step parent) prepared (.ask (.sys cloneReq) fun answer =>
        opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1) prepared := by
  intro parent child
  let initial : T := ⟨pc, fp⟩
  let middle : T := ⟨pc + 16, fp⟩
  have first : InsAt memory initial.pc 1 (II.f scratch) (II.f entry) (II.f 0) := by
    have exactInstruction := code 0 (by rw [spawnOne_len]; decide)
    simp only [Nat.mul_zero, BitVec.add_zero] at exactInstruction
    exact exactInstruction
  have firstSlot : sx (II.f scratch) = BitVec.ofNat 64 scratch := sx_nat (by omega)
  have secondSlot : sx (II.f ((scratch + 1 : Nat) : Int)) = BitVec.ofNat 64 (scratch + 1) := sx_nat (by omega)
  let firstMemory := Mem.write memory (slot fp (BitVec.ofNat 64 scratch)) 8 child.pc.toNat
  have wroteFirst : RunM (step initial) memory middle firstMemory := by
    have fits : Mem.all memory.wr (slot initial.fp (sx (II.f scratch))) 8 = true := by
      rw [firstSlot]
      exact frame.wr scratch (by omega)
    have ran := constantInstruction_memory first fits
    simpa only [firstSlot, sx_nat entryFits, firstMemory, child, initial, middle, nxt] using ran
  have keptFirst : Agree fp scratch slots memory firstMemory :=
    agree_write frame.room (Nat.le_refl _) (by omega) _
  have second : InsAt firstMemory middle.pc 1 (II.f ((scratch + 1 : Nat) : Int)) (II.f stack) (II.f 0) :=
    (code.agree keptFirst (spawnOne_len scratch entry stack ▸ far)) 1 (by rw [spawnOne_len]; decide)
  let prepared := Mem.write firstMemory (slot fp (BitVec.ofNat 64 (scratch + 1))) 8 child.fp.toNat
  have wroteSecond : RunM (step middle) firstMemory parent prepared := by
    have fits : Mem.all firstMemory.wr (slot middle.fp (sx (II.f ((scratch + 1 : Nat) : Int)))) 8 = true := by
      rw [secondSlot]
      exact (frame.agree keptFirst).wr (scratch + 1) (by omega)
    have ran := constantInstruction_memory second fits
    have pointer : nxt middle = parent :=
      congrArg (fun ip => T.mk ip fp) (pcN pc 1 1 2 rfl)
    simpa only [pointer, secondSlot, sx_nat stackFits, prepared, child, middle] using ran
  have keptSecond : Agree fp scratch slots firstMemory prepared :=
    agree_write frame.room (Nat.le_succ _) (by omega) _
  have decoded : InsAt prepared parent.pc 24 (II.f ((scratch + 2 : Nat) : Int))
      (II.f scratch) (II.f 0) :=
    (code.agree (keptFirst.trans keptSecond) (spawnOne_len scratch entry stack ▸ far)) 2 (by rw [spawnOne_len]; decide)
  have childEntry : prepared.rd64 (slot parent.fp (sx (II.f scratch))) = some child.pc := by
    rw [firstSlot]
    change (Mem.write firstMemory _ 8 child.fp.toNat).rd64 _ = _
    rw [rd64_write_far (slot_far frame.room (by omega) (by omega) (by omega))]
    exact rd64_wr64 (wr64_some (frame.wr scratch (by omega))) (frame.rd scratch (by omega))
  have childFrame : prepared.rd64 (slot parent.fp (sx (II.f scratch)) + 8) = some child.fp := by
    rw [firstSlot, show (8 : W) = BitVec.ofNat 64 (8 * 1) by rfl, slot_plus]
    have next := frame.agree keptFirst
    exact rd64_wr64 (wr64_some (next.wr (scratch + 1) (by omega))) (next.rd (scratch + 1) (by omega))
  have initialBlock : StarM 2 initial memory parent prepared :=
    .next wroteFirst (.next wroteSecond (.refl _ _))
  exact ⟨prepared, initialBlock, spawnInstruction_reference decoded childEntry childFrame⟩

/-- The emitted startup code reaches the exact clone request. Every
    partial execution either stays within the installed code and frame
    or reaches that request with the same relocated operands. -/
theorem spawnSite_reference [Kern] {layout : Runner.Beweis.Lay}
    {memory : Mem} {pc fp : W} {slots scratch entry stack : Nat}
    (table : TabInv layout memory) (code : CodeAt memory pc (spawnOne scratch entry stack))
    (frame : FrameOK memory fp slots) (far : CodeFar pc 10 fp slots)
    (scratchFits : scratch + 2 ≤ slots) (slotsFit : slots < 2 ^ 31)
    (entryFits : entry < 2 ^ 31) (stackFits : stack < 2 ^ 31) :
    let parent : T := ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩
    let child : T := ⟨BitVec.ofNat 64 entry, BitVec.ofNat 64 stack⟩
    let pending := Res.ask (.sys cloneReq) (fun answer =>
      opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)
    ∃ (count : Nat) (prepared : Mem) (invariant : TabInv layout prepared),
      SCMemoryPrefix layout ⟨⟨memory, table⟩, [some (.next ⟨pc, fp⟩)]⟩ count
        ⟨⟨prepared, invariant⟩, [some pending]⟩ ∧
      ∀ (reads : W → Prop), (∀ byte, inSlots fp 0 slots byte → reads byte) →
        (∀ byte, pc.toNat ≤ byte.toNat → byte.toNat < pc.toNat + 16 * 10 → reads byte) →
        ∀ {control actual}, SoloLauf ⟨pc, fp⟩ memory control actual →
          MemoryScopedControl reads (inSlots fp 0 slots) control ∨ control = pending := by
  intro parent child pending
  obtain ⟨prepared, initialBlock, request⟩ := spawnSite_memory code frame far scratchFits slotsFit entryFits stackFits
  obtain ⟨count, invariant, reference⟩ := StarM.sc_reference_through initialBlock request table
  refine ⟨count, prepared, invariant, reference, ?_⟩
  intro reads frameReads codeReads
  have nowrap : pc.toNat + 16 * (spawnOne scratch entry stack).length < 2 ^ 64 := by
    simpa only [spawnOne_len] using far.1
  have covered : ∀ byte, pc.toNat ≤ byte.toNat →
      byte.toNat < pc.toNat + 16 * (spawnOne scratch entry stack).length → reads byte := by
    simpa only [spawnOne_len] using codeReads
  obtain ⟨maskedFrame, maskedCode⟩ := maskMemory_code_frame code frame nowrap frameReads covered
  obtain ⟨_, reference, request⟩ := spawnSite_memory maskedCode maskedFrame far scratchFits slotsFit entryFits stackFits
  obtain ⟨agrees, readable, writable⟩ := maskMemory_agreement reads (inSlots fp 0 slots) memory frameReads
  intro control actual solo
  exact StarM.scoped_until_host reference request readable writable agrees solo

end Gabbro.Stage0.Senke.BildMehr

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf Runner Runner.IR Runner.Mem

/-- The clone result store leaves the same argument frame in place.
    The guard reads that actual word and selects the next installed
    startup site or the declared refusal stop. -/
theorem spawnResult_reference [kernel : Kern] {view : Mem} {pc fp id : W}
    {slots scratch entry stack : Nat} (decoded : CodeAt view pc (spawnOne scratch entry stack))
    (frame : FrameOK view fp slots) (far : CodeFar pc 10 fp slots)
    (room : scratch + 8 ≤ slots) (small : slots < 2 ^ 31) :
    let parent : T := ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩
    let guard := nxt parent
    let next : T := ⟨pc + BitVec.ofNat 64 (16 * 10), fp⟩
    let result := Mem.write view (slot fp (BitVec.ofNat 64 (scratch + 2))) 8 id.toNat
    RunP (ret1 parent id) view (.next guard) result ∧ Agree fp (scratch + 2) slots view result ∧
      (0 < id.toInt → ∃ final, @Star kernel.withoutSyscalls guard result next final ∧
        Agree fp (scratch + 3) slots result final) ∧
      (id.toInt ≤ 0 → @Stops kernel.withoutSyscalls guard result cloneCode) := by
  intro parent guard next result
  let site := spawnOne scratch entry stack
  have destination : view.rd32 (parent.pc + 4) = some (II.f ((scratch + 2 : Nat) : Int)) :=
    (decoded 2 (by rw [spawnOne_len]; decide)).f1
  have inFrame : scratch + 2 < slots := by omega
  have operand : sx (II.f ((scratch + 2 : Nat) : Int)) = BitVec.ofNat 64 (scratch + 2) :=
    sx_nat (inFrame.trans small)
  have writable : Mem.all view.wr (slot parent.fp (sx (II.f ((scratch + 2 : Nat) : Int)))) 8 = true := by
    rw [operand]
    exact frame.wr _ inFrame
  have stored := resultStore_reference (value := id) destination writable
  rw [operand] at stored
  have unchanged : Agree fp (scratch + 2) slots view result :=
    agree_write frame.room (Nat.le_refl _) inFrame _
  have actualWord : result.rd64 (slot fp (BitVec.ofNat 64 (scratch + 2))) = some id :=
    rd64_wr64 (wr64_some (frame.wr _ inFrame)) (frame.rd _ inFrame)
  have guardAddr : guard.pc = pc + BitVec.ofNat 64 (16 * 3) := pcN pc 2 1 3 rfl
  have through : (site.take 3).length = 3 := by simp [List.length_take, site, spawnOne_len]
  have remaining : (site.drop 3).length = 7 := by simp only [List.length_drop, site, spawnOne_len, Nat.reduceSub]
  have splitCode : CodeAt view pc (site.take 3 ++ site.drop 3) :=
    (List.take_append_drop 3 site).symm ▸ decoded
  have original : CodeAt view guard.pc (site.drop 3) := by
    have tail := codeAt_right splitCode
    rw [through, ← guardAddr] at tail
    exact tail
  have separated : CodeFar guard.pc (site.drop 3).length fp slots := by
    rw [guardAddr, remaining]
    exact codeFar_right (n := 3) (k := 7) far
  letI : Kern := kernel.withoutSyscalls
  obtain ⟨accepted, rejected⟩ :=
    spawnCheck_ok (s := scratch) (original.agree unchanged separated) (frame.agree unchanged) room small
      (by simpa only [remaining] using separated) actualWord
  refine ⟨stored, unchanged, ?_, rejected⟩
  intro positive
  obtain ⟨final, ran, agrees⟩ := accepted positive
  have target : (⟨guard.pc + BitVec.ofNat 64 (16 * 7), fp⟩ : T) = next := by
    rw [guardAddr, pcN pc 3 7 10 rfl]
  exact ⟨final, target ▸ ran, agrees⟩

end Gabbro.Stage0.Senke.BildMehr

namespace Gabbro.Stage0

open Senke Senke.BildMehr Senke.BildLauf Runner Runner.IR Runner.Beweis

/-- A positive reply selects the successor in the actual startup
    header. Every partial memory run stays in the same scope until its
    exact boundary, which still has the installed code and frame. -/
theorem Emitted.clone_guard_progress [kernel : Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    (output : Emitted src reserve options) {index : Nat} {view : Mem} {id : W}
    (declared : index < output.starts.length) (positive : 0 < id.toInt)
    (table : TabInv L0 view)
    (loaded : BytesAt view codeBase (output.image.code.flatMap encII))
    (frame : FrameOK view (BitVec.ofNat 64 output.image.fp0) output.image.Ks) :
    let pc := BitVec.ofNat 64 (codeBase + 16 * (10 * index))
    let fp := BitVec.ofNat 64 output.image.fp0
    let scratch := startScratch output.compiled.main
    let guard := nxt ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩
    let next : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * (index + 1))), fp⟩
    let result := Mem.write view (slot fp (BitVec.ofNat 64 (scratch + 2))) 8 id.toNat
    ∀ {control current}, SoloLauf guard result control current →
      HostFreeControl (imageRootReads output 0) (imageStackFootprint output 0) control ∨
      ∃ boundary, SoloLauf next boundary control current ∧
        TabInv L0 boundary ∧ BytesAt boundary codeBase (output.image.code.flatMap encII) ∧
        FrameOK boundary fp output.image.Ks := by
  intro pc fp scratch guard next result control current path
  obtain ⟨code, far, room, small, _, childFits⟩ := output.loaded_spawn_site loaded declared
  have fpValue : fp.toNat = output.image.fp0 := by
    change (BitVec.ofNat 64 output.image.fp0).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have frameRegion : inSlots fp 0 output.image.Ks = imageStackFootprint output 0 := by
    funext byte
    apply propext
    simp only [inSlots, fpValue, imageStackFootprint, Nat.zero_le, true_and, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.mul_one]
  let reads := imageRootReads output 0
  let writes := inSlots fp 0 output.image.Ks
  have frameReads : ∀ byte, writes byte → reads byte :=
    fun _ inside => .inl (frameRegion ▸ inside)
  have codeReads : ∀ byte : W, pc.toNat ≤ byte.toNat → byte.toNat < pc.toNat + 16 * 10 → reads byte := by
    intro byte _ last
    exact .inr (last.trans_le (fpValue ▸ far.2.2))
  obtain ⟨smallFrame, smallCode⟩ := maskMemory_code_frame code frame
    (by simpa only [spawnOne_len] using far.1) frameReads (by simpa only [spawnOne_len] using codeReads)
  obtain ⟨_, _, accepted, _⟩ := spawnResult_reference (id := id) smallCode smallFrame far room small
  obtain ⟨_, reference, _⟩ := accepted positive
  obtain ⟨count, compiled⟩ := @IRReference.of_star kernel.withoutSyscalls _ _ _ _ reference
  have target : (⟨pc + BitVec.ofNat 64 (16 * 10), fp⟩ : T) = next := by
    simp only [pc, next, ← BitVec.ofNat_add, Nat.mul_add, Nat.add_assoc, Nat.mul_one]
  rw [target] at compiled
  obtain ⟨agreement, readable, writable⟩ := maskMemory_agreement reads writes result frameReads
  change @IRReference kernel.withoutSyscalls count guard (maskMemory reads writes result) next _ at compiled
  rcases IRReference.split_scoped (kernel := kernel) compiled agreement readable writable path with
    internal | ⟨boundary, complete, suffix, _, unchanged⟩
  · exact .inl (Eq.mp (congrArg (fun written => HostFreeControl reads written control) frameRegion) internal)
  · obtain ⟨rd, wr⟩ := StarM.permissions complete
    have inFrame : scratch + 2 < output.image.Ks := by omega
    have answerFrame : Agree fp 0 output.image.Ks view result :=
      agree_write frame.room (Nat.zero_le _) inFrame _
    have guardFrame : Agree fp 0 output.image.Ks result boundary :=
      ⟨rd, wr, fun byte outside => (unchanged byte outside).1⟩
    have kept := answerFrame.trans guardFrame
    have wrote : view.wr64 (slot fp (BitVec.ofNat 64 (scratch + 2))) id = some result :=
      Mem.wr64_some (frame.wr _ inFrame)
    obtain ⟨_, installed, _⟩ := StarM.sc_reference complete (table.keep (wr64_keeps wrote))
    refine .inr ⟨boundary, suffix, installed, ?_, frame.agree kept⟩
    intro byte present
    have below := output.code_byte_before_stacks present
    have outside : ¬ inSlots fp 0 output.image.Ks (BitVec.ofNat 64 (codeBase + byte)) := by
      intro inFrame
      exact (Nat.not_le_of_lt below) (fpValue ▸ (Nat.le_trans (Nat.le_add_right _ _) inFrame.1))
    rw [kept.rd, kept.wr, kept.b _ outside]
    exact loaded byte present

end Gabbro.Stage0
