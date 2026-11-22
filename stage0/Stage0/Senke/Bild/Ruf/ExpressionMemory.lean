module

public import Stage0.Senke.Ausdruck.Satz
public import Stage0.Senke.Bild.Mehr.Solo

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Stage0.Senke.BildMehr Gabbro.Stage0.Senke.BildLauf Runner Runner.IR

private theorem expression_frame_byte {memory : Mem} {fp : W} {K index offset : Nat}
    (frame : FrameOK memory fp K) (slotFits : index < K) (inWord : offset < 8) :
    inSlots fp 0 K (slot fp (BitVec.ofNat 64 index) + BitVec.ofNat 64 offset) := by
  have address := slot_toNat frame.room slotFits
  simp only [inSlots, Nat.mul_zero, Nat.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat, address]
  rw [Nat.mod_eq_of_lt (a := offset) (by omega), Nat.mod_eq_of_lt (by have := frame.lt; omega)]
  omega

/-- A restricted expression memory retains the exact code and lexical
    environment. The read region covers the code bytes and its frame. -/
theorem expression_pre_mask {D : Deklaration} {L : Senke.Lay D} {Γ : Ctx}
    {memory : Mem} {fp pc : W} {K d reserved : Nat} {env : Env D Γ} {code : List II}
    {reads : W → Prop} (frameReads : ∀ byte, inSlots fp 0 K byte → reads byte)
    (codeReads : ∀ byte, pc.toNat ≤ byte.toNat → byte.toNat < pc.toNat + 16 * code.length → reads byte)
    (destination : d ≤ K) (pre : Senke.PreS L memory pc fp K d code env reserved) :
    Senke.PreS L (maskMemory reads (inSlots fp 0 K) memory) pc fp K d code env reserved := by
  let restricted := maskMemory reads (inSlots fp 0 K) memory
  have agree := (maskMemory_agreement reads (inSlots fp 0 K) memory frameReads).1
  have withinFrame (index : Nat) (present : index < K) (offset : Nat) (inWord : offset < 8) :
      inSlots fp 0 K (slot fp (BitVec.ofNat 64 index) + BitVec.ofNat 64 offset) :=
    expression_frame_byte pre.frame present inWord
  have frames : FrameOK restricted fp K := by
    refine ⟨pre.frame.lt, fun index present => ?_, fun index present => ?_⟩
    · rw [Mem.all_congr (fun offset valid => (agree.1 _ (frameReads _ (withinFrame index present offset valid))).2)]
      exact pre.frame.rd index present
    · rw [Mem.all_congr (fun offset valid => agree.2 _ (withinFrame index present offset valid))]
      exact pre.frame.wr index present
  refine ⟨pre.ctx, pre.small, frames, ?_, pre.far, ?_, trivial, Senke.wstab_true _ _⟩
  · intro index present
    let atInstruction := pc + BitVec.ofNat 64 (16 * index)
    have address (offset : Nat) (inside : offset < 16) :
        reads (atInstruction + BitVec.ofNat 64 offset) := by
      have bound := pre.far.1
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
    have original := pre.code index present
    exact ⟨opcode.trans original.op, (operand 4 (by decide)).trans original.f1,
      (operand 8 (by decide)).trans original.f2, (operand 12 (by decide)).trans original.f3⟩
  · intro ty variableAt
    have stored := pre.env ty variableAt
    refine ⟨stored.1, fun word present => ?_⟩
    have width : word < Senke.valueWords ty := by simpa only [Senke.encodeWords_length] using present
    have location := Senke.variableOffset_bound variableAt
    have slotFits : Senke.vslot variableAt reserved + word < K := by
      have frame := pre.ctx
      unfold Senke.vslot Senke.frei at *
      omega
    have sameWord (j : Nat) (inside : j < 8) :=
      agree.1 _ (frameReads _ (withinFrame _ slotFits j inside))
    change restricted.rd64 (slot fp (BitVec.ofNat 64 (Senke.vslot variableAt reserved + word))) = _
    simp only [Mem.rd64,
      Mem.all_congr (fun j inside => (sameWord j inside).2),
      Mem.le_congr (fun j inside => (sameWord j inside).1)]
    exact stored.2 word present

private theorem expression_mask_value {D : Deklaration} {L : Senke.Lay D}
    {memory : Mem} {reads writes : W → Prop} {address : Nat} {ty : Ty} {value : Wert D ty}
    (writeReads : ∀ byte, writes byte → reads byte)
    (bound : address + 8 * Senke.valueWords ty < 2 ^ 64)
    (covered : ∀ byte : W, address ≤ byte.toNat → byte.toNat < address + 8 * Senke.valueWords ty → reads byte)
    (typed : Senke.ValueAt L memory (BitVec.ofNat 64 address) 0 ty value) :
    Senke.ValueAt L (maskMemory reads writes memory) (BitVec.ofNat 64 address) 0 ty value := by
  have agree := (maskMemory_agreement reads writes memory writeReads).1
  exact Senke.ValueAt.congr_read_bytes bound (fun byte first last => agree.1 byte (covered byte first last)) typed

/-- A physical read region containing the authorized carriers
    preserves their complete value representations in the proof memory. -/
theorem expression_world_mask {D : Deklaration} {L : Senke.Lay D} {memory : Mem}
    {reads writes : W → Prop} {world : World D} {resources : List (Res D)}
    (writeReads : ∀ byte, writes byte → reads byte) (layout : Senke.LayIn L)
    (authorized : ∀ cell : Senke.Zelle D, cell.da L →
      Sum.elim (fun table => darf D table resources) (fun global => gdarf D global resources) cell.carrier →
      ∀ byte : W, cell.adr L ≤ byte.toNat → byte.toNat < cell.adr L + cell.bytes → reads byte)
    (values : Senke.ReadWorldAt memory L world resources) :
    Senke.ReadWorldAt (maskMemory reads writes memory) L world resources := by
  refine ⟨?_, ?_⟩
  · intro table access field index valid
    have inside := (layout.1 table field index valid).2.trans_lt layout.2.2
    exact expression_mask_value writeReads (inside.trans (by decide))
      (authorized (.elem table field index) valid access) (values.table table access field index valid)
  · intro global access
    have inside := (layout.2.1 global).2.trans_lt layout.2.2
    exact expression_mask_value writeReads (inside.trans (by decide))
      (authorized (.glob global) trivial access) (values.global global access)

/-- Every successful production expression lowering has an exact
    host-free reference. Any actual memory prefix reaches the same
    typed result when complete and cannot ask the host while incomplete. -/
theorem lowE_frameMemory [kernel : Kern] {D : Deklaration} {L : Senke.Lay D} {Λ : List (Res D)}
    {Γ : Ctx} {τ : Ty} {memory : Mem} {pc fp : W} {K d reserved top : Nat}
    {code : List II} {world initial : World D} {env : Env D Γ} {currentOld : Bool}
    (reads : W → Prop) (frameReads : ∀ byte, inSlots fp 0 K byte → reads byte)
    (codeReads : ∀ byte, pc.toNat ≤ byte.toNat → byte.toNat < pc.toNat + 16 * code.length → reads byte)
    (expression : Expr D Γ Λ τ)
    (lowered : Senke.lowE (reserved := reserved) (currentOld := currentOld) L expression d = some (code, top))
    (fits : top ≤ K) (resultFits : d + Senke.valueWords τ ≤ K)
    (pre : Senke.PreS L memory pc fp K d code env reserved)
    (valueMemory : Senke.ReadWorldAt memory L world Λ)
    (worldReads : ∀ cell : Senke.Zelle D, cell.da L →
      Sum.elim (fun table => darf D table Λ) (fun global => gdarf D global Λ) cell.carrier →
      ∀ byte : W, cell.adr L ≤ byte.toNat → byte.toNat < cell.adr L + cell.bytes → reads byte)
    (layout : Senke.LayIn L)
    (separated : fp.toNat + 8 * K ≤ L.lo) (entry : currentOld = true → initial = world) :
    let start : T := ⟨pc, fp⟩
    let target : T := ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩
    let restricted := maskMemory reads (inSlots fp 0 K) memory
    ∃ count finish, @IRReference kernel.withoutSyscalls count start restricted target finish ∧
      ∀ {taken : Nat} {pointer : T} {actual : Mem},
        StarM taken start memory pointer actual → taken ≤ count →
        (taken = count → pointer = target ∧
          Senke.ValueAt L actual fp d τ (eval initial expression world env)) ∧
        (taken < count → ∀ {request : Op} {resume : Ans → Res T} {atRequest : Mem},
          RunP (step pointer) actual (.ask request resume) atRequest →
          (∀ call, request ≠ .sys call) ∧
          (∀ byte, fussOp request byte → reads byte) ∧
          (schreibtOp request = true → ∀ byte, fussOp request byte → inSlots fp 0 K byte)) := by
  intro start target restricted
  letI : Kern := kernel.withoutSyscalls
  have masked := expression_pre_mask frameReads codeReads (by omega : d ≤ K) pre
  have scope : Senke.Pre L restricted pc fp K d code env (fun m => Senke.ReadWorldAt m L world Λ) reserved :=
    ⟨masked.ctx, masked.small, masked.frame, masked.code, masked.far, masked.env,
      expression_world_mask frameReads layout worldReads valueMemory, Senke.readWorldAt_stab layout separated⟩
  obtain ⟨finish, executed, _, value⟩ :=
    Senke.lowE_ok_scoped (same := entry) initial world (fun _ h => h) layout
      expression d code top lowered fits restricted pc env scope
  obtain ⟨count, reference⟩ := IRReference.of_star executed
  obtain ⟨agree, readable, writable⟩ :=
    maskMemory_agreement reads (inSlots fp 0 K) memory frameReads
  refine ⟨count, finish, reference, ?_⟩
  intro taken pointer actual ran within
  obtain ⟨cut, remaining, memoryEq, rd, wr⟩ := StarM.align_reference ran reference within readable writable agree
  constructor
  · intro completed
    subst taken
    rw [Nat.sub_self] at remaining
    have endpoint : pointer = target ∧ cut = finish := by
      cases remaining
      exact ⟨rfl, rfl⟩
    obtain ⟨rfl, exactMemory⟩ := endpoint
    subst cut
    refine ⟨rfl, value.1, ?_⟩
    intro index present
    have indexFits : index < Senke.valueWords τ := by simpa only [Senke.encodeWords_length] using present
    have agreeWord (offset : Nat) (inWord : offset < 8) :=
      memoryEq.1 _ (frameReads _ (expression_frame_byte pre.frame (by omega : d + index < K) inWord))
    have sameRead : actual.rd64 (slot fp (BitVec.ofNat 64 (d + index))) =
        finish.rd64 (slot fp (BitVec.ofNat 64 (d + index))) := by
      simp only [Mem.rd64, Mem.all_congr (fun offset valid => (agreeWord offset valid).2.symm),
        Mem.le_congr (fun offset valid => (agreeWord offset valid).1.symm)]
    rw [sameRead]
    exact value.2 index present
  · intro inside request resume atRequest waiting
    have left : 0 < count - taken := Nat.sub_pos_of_lt inside
    cases available : count - taken with
    | zero => omega
    | succ unused =>
      have restOfReference : IRReference (Nat.succ unused) pointer cut target finish := by
        simpa only [available] using remaining
      cases restOfReference with
      | extend first rest =>
        obtain ⟨_, aligned, _⟩ := waiting.align_reference first (blind_step _)
          (fun byte granted => readable byte (by simpa only [rd] using granted))
          (fun byte granted => writable byte (by simpa only [wr] using granted)) memoryEq
        constructor
        · intro call equal
          subst request
          exact aligned.no_syscall (kernel := kernel) first
        · have allowed := aligned.remaining_run first
          have permits := aligned.permissions
          cases allowed with
          | ask answered continued =>
            rename_i reply
            cases reply with
            | none =>
              have rejected := (aligned.blind (blind_step _)).missing
              rw [rejected] at continued
              cases continued
            | some words =>
              exact memAns_confined (reads := reads) (writes := inSlots fp 0 K)
                (fun byte granted => readable byte (by simpa only [rd, permits.1] using granted))
                (fun byte granted => writable byte (by simpa only [wr, permits.2] using granted))
                answered
          | sys unavailable _ => exact unavailable.elim
          | fp _ _ => exact ⟨fun _ => False.elim, fun refused => by cases refused⟩

end Gabbro.Stage0
