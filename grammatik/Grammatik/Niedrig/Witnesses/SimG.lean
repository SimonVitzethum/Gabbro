module

public import Grammatik.Niedrig.Authority.SimGMachine
public import Grammatik.Niedrig.Witnesses.Layout
public import Grammatik.Niedrig.Witnesses.Shared

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Witness

def writeResources : List (Res D) := [Res.marke true 0]

theorem write_allowed : darf D writableView.span.table writeResources := by
  intro requirement member
  change requirement ∈ [Sum.inr (true, 0)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst requirement
  exact List.mem_cons_self ..

theorem write_held : HeldIn writeResources before.haelt := by
  intro lock
  exact lock.elim

def tracedWrite : World D :=
  before.schreibSlot writableView.span.table writeResources write.index write.field write.value

theorem initial_sim_zeuge : SimRel authority initial before :=
  simRel_initial initial_valid rfl before

theorem borrow_sim_zeuge :
    SimRel authority writableResult.next before ∧
    OwnerState.borrow authority.names initial.owners initial.frame writableView.borrower
      authority.token = some writableResult.next.owners ∧
    writableResult.next.owners.access authority.names writableResult.next.frame authority.token ∧
    ¬ writableResult.next.owners.access authority.names initial.frame authority.token ∧
    ¬ writableResult.next.owners.owns authority.names writableResult.next.frame authority.token ∧
    writableResult.next.owners.spent = initial.owners.spent ∧
    writableResult.next.owners.stage = initial.owners.stage :=
  borrow_sim initial_sim_zeuge start 4 readWriteRights OwnerWitness.child writableResult
    successful_view_zeuge

theorem viewwrite_is_storeSlot_zeuge :
    ∃ (index : Int) (field : D.Feld writableView.span.table)
        (value : Wert D (D.typ writableView.span.table field)),
      after = before.storeSlot writableView.span.table index field value ∧
      ImBereich D writableView.span.table index ∧
      ∀ byte, layout.inZelle writableView.span.table index field byte →
        writableView.Contains byte ∧ layout.inTabelle writableView.span.table byte :=
  viewwrite_is_storeSlot write layout_realizes

/-- An inhabited byte extent and an actual change from zero to one, jointly
    with the exact existing store and the index extent. -/
theorem store_extent_zeuge :
    after = before.storeSlot () 0 () write.value ∧ ImBereich D () 0 ∧
    layout.inZelle () 0 () (0, 100) ∧ writableView.Contains (0, 100) ∧
    layout.inTabelle () (0, 100) ∧
    (before.slots () 0 ()).n = 0 ∧ (after.slots () 0 ()).n = 1 := by
  have cell : layout.inZelle () 0 () (0, 100) :=
    ⟨rfl, by change 100 + 0 * 16 + 0 ≤ 100; omega,
      by change 100 < 100 + 0 * 16 + 0 + 1; omega⟩
  have confined := view_write_confined layout_correct write cell
  exact ⟨write.store, write.extent, cell, confined.1, confined.2, rfl, rfl⟩

theorem viewwrite_sim_zeuge : SimRel authority writableResult.next tracedWrite :=
  viewwrite_sim borrow_sim_zeuge.1 layout_correct layout_realizes write writeResources
    write_allowed write_held

theorem viewwrite_trace_zeuge :
    tracedWrite.slots = after.slots ∧ tracedWrite.globs = after.globs ∧
    tracedWrite.spur = .zugriff () true writeResources before.haelt :: before.spur ∧
    after.spur = before.spur :=
  (viewwrite_trace_ok write writeResources).2

theorem viewwrite_gut_zeuge : Gut (fun _ => true) (fun _ => false) before tracedWrite :=
  viewwrite_gut write writeResources (fun _ => true) (fun _ => false) rfl write_allowed write_held

/-- The trace records the actual loan, G store and matching return in order.
    The restored context coexists with the written world, not the old memory. -/
theorem ledger_replay_zeuge :
    LedgerMatchesWorld authority initial before
      [.returned writableView, .wrote writableView, .borrowed writableView] initial tracedWrite := by
  have loan : LedgerMatchesWorld authority initial before
      [.borrowed writableView] writableResult.next before :=
    .borrow .start start 4 readWriteRights OwnerWitness.child writableResult successful_view_zeuge
  have stored : LedgerMatchesWorld authority initial before
      [.wrote writableView, .borrowed writableView] writableResult.next tracedWrite :=
    .store loan layout layout_correct layout_realizes write writeResources write_allowed write_held
  exact .restore stored writableView [] rfl return_zeuge

theorem borrow_return_sim_zeuge :
    returnView authority writableResult.next = .ok initial ∧
    OwnerState.returnBorrow authority.names writableResult.next.owners writableResult.next.frame
      initial.frame authority.token = some initial.owners ∧
    SimRel authority initial tracedWrite ∧ (tracedWrite.slots () 0 ()).n = 1 :=
  ⟨return_zeuge, OwnerState.borrow_return initial_ledger_valid writableResult.borrowed,
    returnView_sim viewwrite_sim_zeuge return_zeuge, rfl⟩

theorem refusal_sim_zeuge :
    ram_view authority initial deviceStart 2 readOnlyRights OwnerWitness.child = .error .memoryClass ∧
    SimRel authority initial before ∧ returnView authority initial = .error .noView :=
  ⟨class_refusal_zeuge,
    ram_view_refusal_sim initial_sim_zeuge deviceStart 2 readOnlyRights OwnerWitness.child
      .memoryClass class_refusal_zeuge, rfl⟩

/-- A real nested read loan exercises the live-view coverage for both the
    innermost view and the suspended outer view, then pops in reverse order. -/
theorem nested_sim_zeuge :
    SimRel authority innerResult.next before ∧
    SimRel authority readResult.next before ∧ SimRel authority initial before := by
  have outer := (borrow_sim initial_sim_zeuge start 4 readOnlyRights OwnerWitness.child
    readResult shared_borrows_zeuge.1).1
  have inner := (borrow_sim outer start 4 readOnlyRights OwnerWitness.grandchild
    innerResult shared_borrows_zeuge.2).1
  have restored := returnView_sim inner nested_return_zeuge.1
  exact ⟨inner, restored, returnView_sim restored nested_return_zeuge.2⟩

/-- A minimal existing G program is used only to witness zero-step address
    evaluation. It does not contain a newly accepted low-level source form. -/
def inertProgram : Programm D where
  invariante := fun i => i.elim
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => .ret .empty (List.Perm.refl _)

def inertMachine : RufMaschineG D :=
  RufStartG inertProgram before.speicher (fun _ => ⟨0, .nil⟩)

theorem inert_world : inertMachine.weltVon 0 = before := rfl

theorem address_sim_zeuge (oracle : Orakel D) :
    RufErreichbarG inertProgram oracle 0 inertMachine inertMachine ∧
    (evalAddress (.offset (.literal 100) 4 : AddressExpr space) (inertMachine.weltVon 0)).2 =
      inertMachine.weltVon 0 ∧
    SimRel authority initial (inertMachine.weltVon 0) := by
  have simulation : SimRel authority initial (inertMachine.weltVon 0) := by
    rw [inert_world]
    exact initial_sim_zeuge
  have result := authority_address_sim (.offset (.literal 100) 4 : AddressExpr space)
    inertProgram oracle 0 inertMachine 0 simulation
  exact ⟨result.1, result.2.1, simulation⟩

/-- Endpoints witnessing the access predicates, without claiming that this
    record update itself is an executable G transition. -/
def writtenMachine : RufMaschineG D :=
  { inertMachine with
    speicher := tracedWrite.speicher
    faeden := fun thread => { (inertMachine.faeden thread) with spur := tracedWrite.spur } }

theorem viewwrite_accessG_zeuge :
    ZugriffG inertMachine writtenMachine 0 (.inl ()) ∧
    SchreibG inertMachine writtenMachine 0 (.inl ()) :=
  viewwrite_accessG write writeResources inert_world rfl

end Gabbro.Grammatik.LowLevel.Witness
