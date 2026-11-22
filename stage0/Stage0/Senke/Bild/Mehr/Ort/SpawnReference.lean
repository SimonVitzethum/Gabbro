module

public import Stage0.Senke.Bild.Mehr.Ort.MemoryReference
public import Stage0.Senke.Start
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Mem Runner.Beweis Runner.Mach BildLauf

/-- The emitted startup prefix supplies one SC reference ending exactly
    at the clone request, with both relocated child operands. -/
theorem spawnSite_reference [Kern] {layout : Runner.Beweis.Lay}
    {memory : Mem} {pc fp : W} {slots scratch entry stack : Nat}
    (table : TabInv layout memory)
    (code : CodeAt memory pc (spawnOne scratch entry stack))
    (frame : FrameOK memory fp slots) (far : CodeFar pc 10 fp slots)
    (scratchFits : scratch + 2 ≤ slots) (slotsFit : slots < 2 ^ 31)
    (entryFits : entry < 2 ^ 31) (stackFits : stack < 2 ^ 31) :
    let parent : T := ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩
    let child : T := ⟨BitVec.ofNat 64 entry, BitVec.ofNat 64 stack⟩
    ∃ (count : Nat) (prepared : Mem) (invariant : TabInv layout prepared),
      SCMemoryPrefix layout ⟨⟨memory, table⟩, [some (.next ⟨pc, fp⟩)]⟩ count
        ⟨⟨prepared, invariant⟩, [some (.ask (.sys cloneReq) fun answer =>
          opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)]⟩ ∧
      ∀ {seen : Req} {resume : Ans → Res T} {actual}, SoloLauf ⟨pc, fp⟩ memory (.ask (.sys seen) resume) actual →
        (.ask (.sys seen) resume : Res T) = .ask (.sys cloneReq) (fun answer =>
          opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1) ∧ actual = prepared := by
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
  have request := spawnInstruction_reference decoded childEntry childFrame
  obtain ⟨count, invariant, reference⟩ := StarM.sc_reference_through initialBlock request table
  exact ⟨count, prepared, invariant, reference, fun ran => SoloLauf.host_unique initialBlock request ran⟩

end Gabbro.Stage0.Senke.BildMehr
