module

public import Grammatik.Niedrig.Konstrukte.Fixture
public import Grammatik.Niedrig.Konstrukte.Saetze

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct.Witness

/-- Literal, signed offset and narrowing all go through the new step functions. -/
theorem address_offset_zeuge :
    (addrOffStep start 3 (by unfold AddrOffOk; decide) before).value.value.n = 103 ∧
    (addrOffStep start 3 (by unfold AddrOffOk; decide) before).world = before ∧
    (narrowAddrStep start 7 (by decide) before).value.value.n = 100 ∧
    addrOffB start 200 = false := ⟨rfl, rfl, rfl, rfl⟩

theorem bind_view_zeuge :
    bindViewStep authority initial start 4 LowLevel.Witness.readWriteRights OwnerWitness.child before =
      (.ok receipt, before) := rfl

theorem bind_view_typing_zeuge :
    bindViewB span layout 2 100 4 1 LowLevel.Witness.readWriteRights [0] = true := by decide

theorem view_refusal_zeuge :
    (bindViewStep authority initial start 9 LowLevel.Witness.readWriteRights OwnerWitness.child before).1 =
      .error .bounds ∧
    bindViewB { span with memoryClass := .device } layout 2 100 4 1
      LowLevel.Witness.readWriteRights [0] = false := ⟨rfl, by decide⟩

theorem view_get_put_zeuge :
    (before.slots false 0 ()).n = 0 ∧
    (viewGetStep view layout () rfl 0 1 resources getChecked written).value.n = 42 ∧
    written.spur = [.zugriff false true resources []] ∧
    returnViewStep authority receipt.next written = (.ok initial, written) :=
  ⟨rfl, rfl, rfl, congrArg (fun result => (result, written)) (ram_view_return initial_valid receipt)⟩

theorem initial_sim_zeuge : SimRel authority initial before := simRel_initial initial_valid rfl before

theorem borrowed_sim_zeuge : SimRel authority receipt.next before :=
  (borrow_sim initial_sim_zeuge start 4 LowLevel.Witness.readWriteRights OwnerWitness.child receipt
    (congrArg Prod.fst bind_view_zeuge)).1

theorem written_sim_zeuge : SimRel authority receipt.next written :=
  viewPutStep_sim view layout () 0 ⟨42, by decide, by decide⟩ resources (fun _ => true)
    putChecked before borrowed_sim_zeuge layout_correct layout_realizes
    (List.mem_cons_self ..) rfl (by intro lock; exact lock.elim)

/-- A real byte changes, is read back, and survives the exact owner return. -/
theorem roundtrip_sim_zeuge :
    SimRel authority receipt.next
      (viewGetStep view layout () rfl 0 1 resources getChecked written).world ∧
    SimRel authority initial (returnViewStep authority receipt.next written).2 ∧
    (written.slots false 0 ()).n = 42 :=
  ⟨(viewGetStep_sim view layout () rfl 0 1 resources getChecked written written_sim_zeuge
      (List.mem_cons_self ..) rfl).1,
    returnViewStep_sim written_sim_zeuge (ram_view_return initial_valid receipt), rfl⟩

theorem scope_both_exits_zeuge :
    closeViewExitStep (.ok 42 : Except Nat Nat) authority receipt.next written =
      (.ok (.ok 42, initial), written) ∧
    closeViewExitStep (.error 7 : Except Nat Nat) authority receipt.next written =
      (.ok (.error 7, initial), written) := close_borrowed_both initial_valid receipt written 42 7

/-- Exercise the complete scope combinator, not just its standalone close. -/
theorem scope_run_zeuge :
    runViewScope authority initial start 4 LowLevel.Witness.readWriteRights OwnerWitness.child before
      (fun _ _ => (.error 7, receipt.next, written))
      (fun _ world => (.ok 0, world)) =
      (.ok ((.error 7 : Except Nat Nat), initial), written) := by
  have produced := congrArg Prod.fst bind_view_zeuge
  simp only [bindViewStep] at produced
  simpa only [runViewScope, produced] using
    closeViewExitStep_success (.error 7 : Except Nat Nat) written (ram_view_return initial_valid receipt)

theorem scope_run_sim_zeuge : SimRel authority initial written := by
  have executed := runViewScope_sim authority initial start 4 LowLevel.Witness.readWriteRights OwnerWitness.child before
    (fun _ _ => ((.error 7 : Except Nat Nat), receipt.next, written))
    (fun _ world => (.ok 0, world)) initial_sim_zeuge
    (fun _ _ _ => written_sim_zeuge)
    (fun _ _ => initial_sim_zeuge) (congrArg Prod.fst scope_run_zeuge)
  simpa only [scope_run_zeuge] using executed

theorem getBytes_correspondence_zeuge :
    (viewGetStep view layout () rfl 0 1 resources getChecked written).value =
      eval written (.getBytes false () rfl 1
        (.lit 0 : Expr D [] resources (.int 0 0)) (by decide) (by decide)
        getChecked.2.1.2.2.1) written .nil :=
  viewGetStep_eval_getBytes view layout () rfl 1
    (.lit 0 : Expr D [] resources (.int 0 0)) (by decide) (by decide)
    getChecked.2.1.2.2.1 written .nil getChecked

/-- A four-byte source sliced at [1,3) has exactly the two middle bytes. -/
def text : Wert D (.str 4) :=
  ⟨[⟨10, by decide, by decide⟩, ⟨20, by decide, by decide⟩,
    ⟨30, by decide, by decide⟩, ⟨40, by decide, by decide⟩], by decide⟩

theorem string_slice_zeuge :
    (strSliceStep text 1 3 (by decide) before).value.1.map (·.n) = [20, 30] ∧
    (strSliceStep text 1 3 (by decide) before).value.1.length = 2 ∧
    (strSliceStep text 4 4 (by decide) before).value.1 = [] ∧
    sliceB text.1.length 3 2 = false ∧ sliceB text.1.length 0 5 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def array : Wert D (.arr (.int 0 255) 4) :=
  fun index => ⟨(index.val : Int), by omega, by have := index.isLt; omega⟩

theorem array_slice_zeuge :
    ((arrSliceStep array 1 3 (by decide) before).value ⟨0, by decide⟩).n = 1 ∧
    ((arrSliceStep array 1 3 (by decide) before).value ⟨1, by decide⟩).n = 2 ∧
    (arrSliceStep array 1 3 (by decide) before).world = before := ⟨rfl, rfl, rfl⟩

theorem context_typing_zeuge :
    bindCtxB (D := D) 0 true 0 ghost renamedGhost 10 11 = true ∧
    ctxMoveB (D := D) true 0 renamedGhost ghost 10 11 = false := ⟨by decide, by decide⟩

theorem context_step_zeuge :
    bindCtxStep (resources := []) oracle 0 true 0 .nil .nil ghost renamedGhost 10 11
      (by decide) before =
      some (renamedGhost, before.fragt (.inl 0), some (.inl ())) :=
  bindCtxStep_eq oracle 0 true 0 .nil .nil ghost renamedGhost 10 11 (by decide) before

end Gabbro.Grammatik.LowLevel.Construct.Witness
