module

public import Stage0.Senke.Bild.Mehr.Ort.SilentControl

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis Runner.Mach BildLauf

theorem frame_slot_byte {memory : Mem} {fp : W} {K index offset : Nat}
    (frame : FrameOK memory fp K) (slotFits : index < K) (inWord : offset < 8) :
    inSlots fp 0 K (slot fp (BitVec.ofNat 64 index) + BitVec.ofNat 64 offset) := by
  have address := slot_toNat frame.room slotFits
  simp only [inSlots, Nat.mul_zero, Nat.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat, address]
  rw [Nat.mod_eq_of_lt (a := offset) (by omega), Nat.mod_eq_of_lt (by have := frame.lt; omega)]
  omega

/-- Restricting the permitted data accesses preserves decoding of an
    installed code region and access to every word of its private frame. -/
theorem maskMemory_code_frame [Kern] {memory : Mem} {pc fp : W} {slots : Nat}
    {code : List II} {reads : W → Prop} (decoded : CodeAt memory pc code)
    (frame : FrameOK memory fp slots) (nowrap : pc.toNat + 16 * code.length < 2 ^ 64)
    (frameReads : ∀ byte, inSlots fp 0 slots byte → reads byte)
    (codeReads : ∀ byte, pc.toNat ≤ byte.toNat → byte.toNat < pc.toNat + 16 * code.length → reads byte) :
    let restricted := maskMemory reads (inSlots fp 0 slots) memory
    FrameOK restricted fp slots ∧ CodeAt restricted pc code := by
  intro restricted
  have agree := (maskMemory_agreement reads (inSlots fp 0 slots) memory frameReads).1
  refine ⟨⟨frame.lt, fun index present => ?_, fun index present => ?_⟩, ?_⟩
  · rw [Mem.all_congr (fun offset valid => (agree.1 _ (frameReads _ (frame_slot_byte frame present valid))).2)]
    exact frame.rd index present
  · rw [Mem.all_congr (fun offset valid => agree.2 _ (frame_slot_byte frame present valid))]
    exact frame.wr index present
  · intro index present
    let atInstruction := pc + BitVec.ofNat 64 (16 * index)
    have address (offset : Nat) (inside : offset < 16) :
        reads (atInstruction + BitVec.ofNat 64 offset) := by
      have natural : (atInstruction + BitVec.ofNat 64 offset).toNat = pc.toNat + 16 * index + offset := by
        simp only [atInstruction, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (a := 16 * index + offset) (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      apply codeReads <;> rw [natural] <;> omega
    have opcode : restricted.rd8 atInstruction = memory.rd8 atInstruction := by
      have pair := agree.1 atInstruction (by simpa using address 0 (by decide))
      simp only [Mem.rd8, pair.1, pair.2]
    have operand (offset : Nat) (fits : offset + 4 ≤ 16) :
        restricted.rd32 (atInstruction + BitVec.ofNat 64 offset) =
          memory.rd32 (atInstruction + BitVec.ofNat 64 offset) := by
      have input (j : Nat) (inside : j < 4) :
          reads (atInstruction + BitVec.ofNat 64 offset + BitVec.ofNat 64 j) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact address (offset + j) (by omega)
      simp only [Mem.rd32,
        Mem.all_congr (fun j inside => (agree.1 _ (input j inside)).2),
        Mem.le_congr (fun j inside => (agree.1 _ (input j inside)).1)]
    have original := decoded index present
    exact ⟨opcode.trans original.op, (operand 4 (by decide)).trans original.f1,
      (operand 8 (by decide)).trans original.f2, (operand 12 (by decide)).trans original.f3⟩

private theorem RunP.host_unique {initial residual : Res T} {before after : Mem}
    {call : Req} {resume : Ans → Res T}
    (reference : RunP initial before residual after)
    (atHost : residual = .ask (.sys call) resume) :
    ∀ {seen : Req} {k : Ans → Res T} {actual : Mem},
      RunP initial before (.ask (.sys seen) k) actual →
      (.ask (.sys seen) k : Res T) = .ask (.sys call) resume ∧ actual = after := by
  induction reference with
  | refl =>
    cases atHost
    intro seen k actual ran
    cases ran with
    | refl => exact ⟨rfl, rfl⟩
    | ask answer _ => cases answer
  | ask answer _ ih =>
    intro seen k actual ran
    cases ran with
    | refl => cases answer
    | ask observed rest =>
      rw [answer] at observed
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj observed)
      exact ih atHost rest

/-- A whole memory reference through the final request selects the same
    host continuation for every solo run from its entry. The run may be
    interleaved with other threads that preserve this memory view. -/
theorem SoloLauf.host_unique [Kern] {start boundary : T} {before middle after : Mem}
    {count : Nat} {call : Req} {resume : Ans → Res T}
    (reference : StarM count start before boundary middle)
    (tail : RunP (step boundary) middle (.ask (.sys call) resume) after) :
    ∀ {seen : Req} {k : Ans → Res T} {actual : Mem},
      SoloLauf start before (.ask (.sys seen) k) actual →
      (.ask (.sys seen) k : Res T) = .ask (.sys call) resume ∧ actual = after := by
  induction reference with
  | refl =>
    intro seen k actual ran
    obtain ⟨used, pointer, memory, complete, pending⟩ := ran
    rcases pending with ⟨impossible, _⟩ | pending
    · cases impossible
    cases complete with
    | refl => exact RunP.host_unique tail rfl pending
    | next first _ =>
      cases tail.remaining first with
      | ask answer _ => cases answer
  | next first _ ih =>
    intro seen k actual ran
    obtain ⟨used, pointer, memory, complete, pending⟩ := ran
    rcases pending with ⟨impossible, _⟩ | pending
    · cases impossible
    cases complete with
    | refl =>
      cases pending.remaining first with
      | ask answer _ => cases answer
    | next executed later =>
      obtain ⟨rfl, rfl⟩ := first.det executed.run
      exact ih tail ⟨_, _, _, later, Or.inr pending⟩

/-- A memory-only execution of an instruction tree supplies the SC
    reference up to its residual control, including pending host calls. -/
theorem RunP.sc_reference {layout : Runner.Beweis.Lay}
    {control residual : Res T} {before after : Mem}
    (ran : RunP control before residual after) (table : TabInv layout before)
    (blind : Blind control) :
    ∃ (count : Nat) (final : TabInv layout after),
      SCMemoryPrefix layout ⟨⟨before, table⟩, [some control]⟩ count ⟨⟨after, final⟩, [some residual]⟩ := by
  induction ran with
  | refl => exact ⟨0, table, .nil _⟩
  | @ask request resume before middle after reply residual answered _ ih =>
    have kind : istSpeicherOp request = true := by
      cases request <;> first | rfl | cases answered
    have widths (n : Nat) (address : W) (read : request = .rd n address) :
        n = 1 ∨ n = 4 ∨ n = 8 := (blind.lesen read).1
    obtain ⟨preserved, answer⟩ := memAns_sc (L := layout) (s := ⟨before, table⟩) (i := 0) widths answered
    obtain ⟨count, final, reference⟩ := ih preserved (blind.weiter reply)
    have first : SCSchritt layout 0 ⟨⟨before, table⟩, [some (.ask request resume)]⟩
        ⟨⟨middle, preserved⟩, [some (resume reply)]⟩ := .ask rfl kind answer
    exact ⟨count + 1, final, .cons first reference⟩

private theorem RunM.partial {control : Res T} {before after : Mem} {next : T}
    (ran : RunM control before next after) : RunP control before (.next next) after := by
  induction ran with
  | next => exact .refl _ _
  | ask answered _ ih => exact .ask answered ih

/-- A sequence of whole proved memory instructions gives the counted
    reference used to cover all actual one-thread silent prefixes. -/
theorem StarM.sc_reference {layout : Runner.Beweis.Lay}
    {initial final : T} {before after : Mem} {instructions : Nat}
    (ran : StarM instructions initial before final after) (table : TabInv layout before) :
    ∃ (count : Nat) (preserved : TabInv layout after),
      SCMemoryPrefix layout ⟨⟨before, table⟩, [some (.next initial)]⟩ count
        ⟨⟨after, preserved⟩, [some (.next final)]⟩ := by
  induction ran with
  | refl => exact ⟨0, table, .nil _⟩
  | next instruction _ ih =>
    obtain ⟨first, middleTable, requests⟩ := RunP.sc_reference (RunM.partial instruction) table (blind_step _)
    obtain ⟨rest, finalTable, tail⟩ := ih middleTable
    exact ⟨rest + first + 1, finalTable, .cons (.priv rfl) (requests.trans tail)⟩

/-- A whole generated block and its final partial instruction give one
    memory reference, ending at the control selected by the IR tree. -/
theorem StarM.sc_reference_through {layout : Runner.Beweis.Lay}
    {initial boundary : T} {before middle after : Mem} {instructions : Nat} {residual : Res T}
    (ran : StarM instructions initial before boundary middle)
    (tail : RunP (step boundary) middle residual after) (table : TabInv layout before) :
    ∃ (count : Nat) (preserved : TabInv layout after),
      SCMemoryPrefix layout ⟨⟨before, table⟩, [some (.next initial)]⟩ count
        ⟨⟨after, preserved⟩, [some residual]⟩ := by
  obtain ⟨prefixCount, middleTable, initialRun⟩ := StarM.sc_reference ran table
  obtain ⟨tailCount, finalTable, suffix⟩ := tail.sc_reference middleTable (blind_step _)
  exact ⟨tailCount + 1 + prefixCount, finalTable, initialRun.trans (.cons (.priv rfl) suffix)⟩

private theorem RunP.read8 {before after : Mem} {address : W} {byte : B}
    {resume : W → Res T} {finish : Res T} (read : before.rd8 address = some byte)
    (tail : RunP (resume (byte.setWidth 64)) before finish after) :
    RunP (rd8 address resume) before finish after := by
  refine .ask (a := some (byte.setWidth 64, 0)) (m' := before) (by simp [memAns, read]) ?_
  simpa only [opt_some, BitVec.setWidth_setWidth_of_le byte (k := 8) (l := 64) (by decide),
    BitVec.setWidth_eq] using tail

private theorem RunP.read32 {before after : Mem} {address : W} {word : BitVec 32}
    {resume : BitVec 32 → Res T} {finish : Res T} (read : before.rd32 address = some word)
    (tail : RunP (resume word) before finish after) :
    RunP (rd32 address resume) before finish after := by
  refine .ask (a := some (word.setWidth 64, 0)) (m' := before) (by simp [memAns, read]) ?_
  simpa only [opt_some, BitVec.setWidth_setWidth_of_le word (k := 32) (l := 64) (by decide),
    BitVec.setWidth_eq] using tail

private theorem RunP.read64 {before after : Mem} {address word : W}
    {resume : W → Res T} {finish : Res T} (read : before.rd64 address = some word)
    (tail : RunP (resume word) before finish after) :
    RunP (rd64 address resume) before finish after := by
  exact .ask (a := some (word, 0)) (m' := before) (by simp [memAns, read]) tail

/-- The immediate instruction selects its operand and writes one word
    using only the IR memory semantics. -/
theorem constantInstruction_memory [Kern] {pointer : T} {memory : Mem} {dest value pad : BitVec 32}
    (instruction : InsAt memory pointer.pc 1 dest value pad)
    (writable : Mem.all memory.wr (slot pointer.fp (sx dest)) 8 = true) :
    RunM (step pointer) memory (nxt pointer)
      (Mem.write memory (slot pointer.fp (sx dest)) 8 (sx value).toNat) := by
  apply runP_runM (t := nxt pointer) ?_ rfl
  unfold step
  refine RunP.read8 instruction.op ?_
  change RunP (op 1 pointer) _ _ _
  simp only [op]
  apply RunP.read32 instruction.f2
  simp only [ret1]
  apply RunP.read32 instruction.f1
  refine .ask (a := some (0, 0)) (by rw [memAns_wr, Mem.wr64_some writable]) ?_
  exact .refl _ _

/-- The IR instruction tree reaches the host with the continuation
    selected by the operands that it read from the issuing frame. -/
theorem spawnInstruction_reference {parent child : T} {memory : Mem} {dest index pad : BitVec 32}
    (instruction : InsAt memory parent.pc 24 dest index pad)
    (entry : memory.rd64 (slot parent.fp (sx index)) = some child.pc)
    (frame : memory.rd64 (slot parent.fp (sx index) + 8) = some child.fp) :
    RunP (step parent) memory
      (.ask (.sys cloneReq) fun answer =>
        opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1) memory := by
  unfold step
  refine RunP.read8 instruction.op ?_
  change RunP (op 24 parent) _ _ _
  simp only [op]
  apply RunP.read32 instruction.f2
  simp only [ld]
  exact RunP.read64 entry (RunP.read64 frame (.refl _ _))

end Gabbro.Stage0.Senke.BildMehr
