module

public import Stage0.Senke.Ausdruck.Satz
public import Stage0.Senke.Bild.Mehr.Solo

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Stage0.Senke.BildMehr Gabbro.Stage0.Senke.BildLauf Runner Runner.IR

/-- The production expression proof works with write permission confined
    to its frame. The memory restriction is used only in the proof. -/
private theorem expression_reference_memory [kernel : Kern]
    {D : Deklaration} {L : Senke.Lay D} {Λ : List (Res D)}
    {Γ : Ctx} {τ : Ty} {memory : Mem} {pc fp : W} {K d reserved top : Nat}
    {code : List II} {world initial : World D} {env : Env D Γ} {currentOld : Bool}
    (expression : Expr D Γ Λ τ)
    (lowered : Senke.lowE (reserved := reserved) (currentOld := currentOld) L expression d = some (code, top))
    (fits : top ≤ K) (pre : Senke.PreS L memory pc fp K d code env reserved)
    (valueMemory : Senke.WeltAt memory L world) (layout : Senke.LayIn L)
    (separated : fp.toNat + 8 * K ≤ L.lo) (entry : currentOld = true → initial = world) :
    @Senke.ValueOk D kernel.withoutSyscalls L (maskMemory (fun _ => True) (inSlots fp 0 K) memory) pc fp K d code τ
      (eval initial expression world env) := by
  classical
  let restricted := maskMemory (fun _ => True) (inSlots fp 0 K) memory
  have readSame : restricted.rd = memory.rd := by
    funext byte
    simp only [restricted, maskMemory, decide_true, Bool.and_true]
  have exactMemory : restricted = { memory with wr := restricted.wr } := by
    cases memory
    simp only [restricted, maskMemory, decide_true, Bool.and_true]
  have original : Senke.WeltAt restricted L world false := by
    rw [exactMemory]
    exact valueMemory.withWriteMap _
  have frames : FrameOK restricted fp K := by
    refine ⟨pre.frame.lt, fun index bound => ?_, fun index bound => ?_⟩
    · rw [readSame]
      exact pre.frame.rd index bound
    · apply Mem.all_of
      intro offset fitsWord
      have addr := slot_toNat pre.frame.room bound
      have inside : inSlots fp 0 K (slot fp (BitVec.ofNat 64 index) + BitVec.ofNat 64 offset) := by
        simp only [inSlots, Nat.mul_zero, Nat.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat, addr]
        rw [Nat.mod_eq_of_lt (a := offset) (by omega), Nat.mod_eq_of_lt (by have := pre.frame.lt; omega)]
        omega
      have allowed := Mem.all_spec (pre.frame.wr index bound) fitsWord
      simpa only [restricted, maskMemory, inside, decide_true, Bool.and_true] using allowed
  have prepared : Senke.Pre L restricted pc fp K d code env (fun m => Senke.WeltAt m L world false) reserved := by
    refine ⟨pre.ctx, pre.small, frames, ?_, pre.far, ?_, original,
      Senke.weltAt_stab (requireWrites := false) layout separated⟩
    · rw [exactMemory]
      intro index present
      obtain ⟨opcode, first, second, third⟩ := pre.code index present
      exact ⟨opcode, first, second, third⟩
    · rw [exactMemory]
      exact pre.env
  letI : Kern := kernel.withoutSyscalls
  exact Senke.lowE_ok (same := entry) initial world (fun _ h => h) layout expression d code top lowered fits restricted pc env prepared

/-- Every successful production expression lowering has an exact
    host-free reference. Any actual memory prefix reaches the same
    typed result when complete and cannot ask the host while incomplete. -/
theorem lowE_frameMemory [kernel : Kern] {D : Deklaration} {L : Senke.Lay D} {Λ : List (Res D)}
    {Γ : Ctx} {τ : Ty} {memory : Mem} {pc fp : W} {K d reserved top : Nat}
    {code : List II} {world initial : World D} {env : Env D Γ} {currentOld : Bool}
    (expression : Expr D Γ Λ τ)
    (lowered : Senke.lowE (reserved := reserved) (currentOld := currentOld) L expression d = some (code, top))
    (fits : top ≤ K) (pre : Senke.PreS L memory pc fp K d code env reserved)
    (valueMemory : Senke.WeltAt memory L world) (layout : Senke.LayIn L)
    (separated : fp.toNat + 8 * K ≤ L.lo) (entry : currentOld = true → initial = world) :
    let start : T := ⟨pc, fp⟩
    let target : T := ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩
    let restricted := maskMemory (fun _ => True) (inSlots fp 0 K) memory
    ∃ count finish, @IRReference kernel.withoutSyscalls count start restricted target finish ∧
      ∀ {taken : Nat} {pointer : T} {actual : Mem},
        StarM taken start memory pointer actual → taken ≤ count →
        (taken = count → pointer = target ∧
          Senke.ValueAt L actual fp d τ (eval initial expression world env)) ∧
        (taken < count → ∀ {request : Op} {resume : Ans → Res T} {atRequest : Mem},
          RunP (step pointer) actual (.ask request resume) atRequest →
          (∀ call, request ≠ .sys call) ∧
          (schreibtOp request = true → ∀ byte, fussOp request byte → inSlots fp 0 K byte)) := by
  intro start target restricted
  obtain ⟨finish, executed, _, value⟩ :=
    expression_reference_memory expression lowered fits pre valueMemory layout separated entry
  letI : Kern := kernel.withoutSyscalls
  obtain ⟨count, reference⟩ := IRReference.of_star executed
  obtain ⟨agree, readable, writable⟩ :=
    maskMemory_agreement (fun _ => True) (inSlots fp 0 K) memory (fun _ _ => trivial)
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
    have sameRead : actual.rd64 (slot fp (BitVec.ofNat 64 (d + index))) =
        finish.rd64 (slot fp (BitVec.ofNat 64 (d + index))) := by
      simp only [Mem.rd64, Mem.all_congr (fun _ _ => (memoryEq.1 _ trivial).2.symm),
        Mem.le_congr (fun _ _ => (memoryEq.1 _ trivial).1.symm)]
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
        · intro writesRequest
          have allowed := aligned.remaining_run first
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
              exact (memAns_confined (reads := fun _ => True) (writes := inSlots fp 0 K)
                (fun _ _ => trivial)
                (fun byte granted => writable byte (by simpa only [wr, permits.2] using granted))
                answered).2 writesRequest
          | sys unavailable _ => exact unavailable.elim
          | fp _ _ => cases writesRequest

end Gabbro.Stage0
