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

/-- Every successful production expression lowering has an exact
    host-free reference. Any actual memory prefix reaches the same
    typed result when complete and cannot ask the host while incomplete. -/
theorem lowE_frameMemory [kernel : Kern] {D : Deklaration} {L : Senke.Lay D} {Λ : List (Res D)}
    {Γ : Ctx} {τ : Ty} {memory : Mem} {pc fp : W} {K d reserved top : Nat}
    {code : List II} {world initial : World D} {env : Env D Γ} {currentOld : Bool}
    (reads : W → Prop) (frameReads : ∀ byte, inSlots fp 0 K byte → reads byte)
    (expression : Expr D Γ Λ τ)
    (lowered : Senke.lowE (reserved := reserved) (currentOld := currentOld) L expression d = some (code, top))
    (fits : top ≤ K) (resultFits : d + Senke.valueWords τ ≤ K)
    (pre : Senke.PreS L (maskMemory reads (inSlots fp 0 K) memory) pc fp K d code env reserved)
    (valueMemory : Senke.ReadWorldAt (maskMemory reads (inSlots fp 0 K) memory) L world Λ)
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
  have scope : Senke.Pre L restricted pc fp K d code env (fun m => Senke.ReadWorldAt m L world Λ) reserved :=
    ⟨pre.ctx, pre.small, pre.frame, pre.code, pre.far, pre.env, valueMemory, Senke.readWorldAt_stab layout separated⟩
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
