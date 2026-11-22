module

public import Stage0.Senke.Bild.Mehr.Ort.MemoryReference
public import Stage0.Senke.Start
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

namespace Gabbro.Stage0

open Senke Senke.BildMehr Senke.BildLauf Runner Runner.IR Runner.Mem

/-- The clone result store leaves the same argument frame in place.
    The guard reads that actual word and selects the next installed
    startup site or the declared refusal stop. -/
theorem Emitted.clone_result_reference [kernel : Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    (output : Emitted src reserve options) {index : Nat} {view : Mem} {id : W}
    (declared : index < output.starts.length)
    (loaded : BytesAt view codeBase (output.image.code.flatMap encII))
    (frame : FrameOK view (BitVec.ofNat 64 output.image.fp0) output.image.Ks) :
    let pc := BitVec.ofNat 64 (codeBase + 16 * (10 * index))
    let fp := BitVec.ofNat 64 output.image.fp0
    let scratch := startScratch output.compiled.main
    let parent : T := ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩
    let guard := nxt parent
    let next : T := ⟨pc + BitVec.ofNat 64 (16 * 10), fp⟩
    let result := Mem.write view (slot fp (BitVec.ofNat 64 (scratch + 2))) 8 id.toNat
    RunP (ret1 parent id) view (.next guard) result ∧ Agree fp (scratch + 2) output.image.Ks view result ∧
      (0 < id.toInt → ∃ final, @Star kernel.withoutSyscalls guard result next final ∧
        Agree fp (scratch + 3) output.image.Ks result final) ∧
      (id.toInt ≤ 0 → @Stops kernel.withoutSyscalls guard result cloneCode) := by
  intro pc fp scratch parent guard next result
  obtain ⟨code, far, room, small, _, _⟩ := output.loaded_spawn_site loaded declared
  let entry := codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)
  let stack := output.image.fp0 + 8 * (output.image.Ks * (index + 1))
  let site := spawnOne scratch entry stack
  have decoded : CodeAt view pc site := code
  have destination : view.rd32 (parent.pc + 4) = some (II.f ((scratch + 2 : Nat) : Int)) :=
    (decoded 2 (by rw [spawnOne_len]; decide)).f1
  have inFrame : scratch + 2 < output.image.Ks := by omega
  have operand : sx (II.f ((scratch + 2 : Nat) : Int)) = BitVec.ofNat 64 (scratch + 2) :=
    sx_nat (inFrame.trans small)
  have writable : Mem.all view.wr (slot parent.fp (sx (II.f ((scratch + 2 : Nat) : Int)))) 8 = true := by
    rw [operand]
    exact frame.wr _ inFrame
  have stored := resultStore_reference (value := id) destination writable
  rw [operand] at stored
  have unchanged : Agree fp (scratch + 2) output.image.Ks view result :=
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
  have separated : CodeFar guard.pc (site.drop 3).length fp output.image.Ks := by
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

end Gabbro.Stage0
