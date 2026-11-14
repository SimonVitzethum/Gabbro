module

public import Grammatik.Niedrig.Authority.SimG
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T3

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

variable {D : Deklaration} {P I : Type} {a : Authority D}
  {c c' : Context D P I} {world : World D}

/-- Zero G steps, witnessed by the start constructor, on the existing call
    machine. The address result may succeed or fail; neither outcome evaluates
    a G expression, adds an access event, or alters the world or simulation. -/
theorem authority_address_sim {space : Space D} (e : AddressExpr space)
    (program : Programm D) (oracle : Orakel D) (passes : Nat)
    (machine : RufMaschineG D) (thread : Faden)
    (simulation : SimRel a c (machine.weltVon thread)) :
    RufErreichbarG program oracle passes machine machine ∧
    (evalAddress e (machine.weltVon thread)).2 = machine.weltVon thread ∧
    (evalAddress e (machine.weltVon thread)).1 = e.eval ∧
    SimRel a c (evalAddress e (machine.weltVon thread)).2 :=
  ⟨.start, rfl, rfl, simulation⟩

/-- A ViewWrite already retains its exact store and index extent. Realization
    additionally places every authorized byte in the actual carrier, even
    without LayoutOk. It cannot manufacture the index extent from byte
    containment: a field may have zero byte size. -/
theorem viewwrite_is_storeSlot {layout : AdressLayout D} {before after : World D}
    (write : ViewWrite a c layout before after) (realizes : a.Realizes layout) :
    ∃ (index : Int) (field : D.Feld write.view.span.table)
        (value : Wert D (D.typ write.view.span.table field)),
      after = before.storeSlot write.view.span.table index field value ∧
      ImBereich D write.view.span.table index ∧
      ∀ byte, layout.inZelle write.view.span.table index field byte →
        write.view.Contains byte ∧ layout.inTabelle write.view.span.table byte := by
  refine ⟨write.index, write.field, write.value, write.store, write.extent, ?_⟩
  intro byte cell
  have inside := write.bytes byte cell
  have valid := write.valid.2.2.2.1 write.view write.live
  have span := realizes write.view.span valid.1
  have bounds := valid.2.2.2.1
  have endBound := valid.2.2.2.2.1
  refine ⟨inside, inside.1.trans span.1, ?_, ?_⟩
  · have base := span.2.1
    have low := inside.2.1
    omega
  · rcases span.2.2 with opened | finite
    · exact Or.inl opened
    · right
      have high := inside.2.2
      omega

/-- Recording the store produces exactly one ordinary G write event. The
    receipt's untraced after-world has identical memory; it does NOT already
    contain the event. In particular, an idempotent write still records it. -/
theorem viewwrite_trace_ok {layout : AdressLayout D} {before after : World D}
    (write : ViewWrite a c layout before after) (resources : List (Res D)) :
    before.schreibSlot write.view.span.table resources write.index write.field write.value =
      after.merke [.zugriff write.view.span.table true resources before.haelt] ∧
    (before.schreibSlot write.view.span.table resources write.index write.field write.value).slots =
      after.slots ∧
    (before.schreibSlot write.view.span.table resources write.index write.field write.value).globs =
      after.globs ∧
    (before.schreibSlot write.view.span.table resources write.index write.field write.value).spur =
      .zugriff write.view.span.table true resources before.haelt :: before.spur ∧
    after.spur = before.spur := by
  rcases write with ⟨view, live, active, valid, writable, index, field, extent, bytes, value, store⟩
  dsimp only
  rw [store]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Permission and held-lock obligations are additional to ViewWrite; the
    receipt never replaces G's effect/lock checks. The canonical G frame/trace
    theorem supplies consistency, good new events and preservation of locks. -/
theorem viewwrite_gut {layout : AdressLayout D} {before after : World D}
    (write : ViewWrite a c layout before after) (resources : List (Res D))
    (writes : D.Tab → Bool) (globals : D.Glob → Bool)
    (effect : writes write.view.span.table = true)
    (allowed : darf D write.view.span.table resources) (held : HeldIn resources before.haelt) :
    Gut writes globals before
      (before.schreibSlot write.view.span.table resources write.index write.field write.value) :=
  gut_schreibSlot before write.view.span.table resources write.index write.field write.value
    effect allowed held

theorem viewwrite_sim {layout : AdressLayout D} {before after : World D}
    (simulation : SimRel a c before) (correct : LayoutOk layout)
    (realizes : a.Realizes layout) (write : ViewWrite a c layout before after)
    (resources : List (Res D)) (allowed : darf D write.view.span.table resources)
    (held : HeldIn resources before.haelt) :
    SimRel a c
      (before.schreibSlot write.view.span.table resources write.index write.field write.value) := by
  obtain ⟨origin, initialWorld, trace, initialValid, empty, replay, covered⟩ := simulation.replay
  refine ⟨simulation.valid,
    ⟨origin, initialWorld, .wrote write.view :: trace, initialValid, empty,
      .store replay layout correct realizes write resources allowed held, ?_⟩⟩
  intro view member
  exact List.mem_cons_of_mem _ (covered view member)

theorem ram_view_refusal_sim (simulation : SimRel a c world) {space : Space D}
    (start : Address space) (length : Nat) (rights : DataRights)
    (borrower : ArenaOwnership.Frame) (reason : ViewFailure)
    (refused : ram_view a c start length rights borrower = .error reason) :
    SimRel a c world := by
  obtain ⟨origin, initialWorld, trace, initialValid, empty, replay, covered⟩ := simulation.replay
  refine ⟨simulation.valid,
    ⟨origin, initialWorld, .refused reason :: trace, initialValid, empty,
      .refuse replay start length rights borrower reason refused, ?_⟩⟩
  intro view member
  exact List.mem_cons_of_mem _ (covered view member)

theorem returnView_refusal_sim (simulation : SimRel a c world) (reason : ViewFailure)
    (refused : returnView a c = .error reason) : SimRel a c world := by
  obtain ⟨origin, initialWorld, trace, initialValid, empty, replay, covered⟩ := simulation.replay
  refine ⟨simulation.valid,
    ⟨origin, initialWorld, .refused reason :: trace, initialValid, empty,
      .refuseReturn replay reason refused, ?_⟩⟩
  intro view member
  exact List.mem_cons_of_mem _ (covered view member)

/-- Total checked success/refusal simulation at the ledger level. No machine
    call is inferred from a successful check. -/
theorem ram_view_step_sim (simulation : SimRel a c world) {space : Space D}
    (start : Address space) (length : Nat) (rights : DataRights)
    (borrower : ArenaOwnership.Frame) :
    match ram_view a c start length rights borrower with
    | .error _ => SimRel a c world
    | .ok r => SimRel a r.next world := by
  cases result : ram_view a c start length rights borrower with
  | error reason =>
    exact ram_view_refusal_sim simulation start length rights borrower reason result
  | ok receipt =>
    exact (borrow_sim simulation start length rights borrower receipt result).1

theorem authority_step_sim (simulation : SimRel a c world)
    {result : Option (View D)} (step : AuthorityStep a c result c') : SimRel a c' world := by
  cases step with
  | address => exact simulation
  | ram start length rights borrower receipt produced =>
    exact (borrow_sim simulation start length rights borrower receipt produced).1
  | restore returned => exact returnView_sim simulation returned
  | refuse start length rights borrower reason refused =>
    exact ram_view_refusal_sim simulation start length rights borrower reason refused
  | refuseReturn reason refused => exact returnView_refusal_sim simulation reason refused

/-- A matching return restores the complete original context, independently
    of any stores performed in the meantime. Return changes no world. -/
theorem borrow_return_sim (simulation : SimRel a c world) {space : Space D}
    (start : Address space) (length : Nat) (rights : DataRights)
    (borrower : ArenaOwnership.Frame) (receipt : ViewResult a c)
    (produced : ram_view a c start length rights borrower = .ok receipt) :
    SimRel a receipt.next world ∧
    returnView a receipt.next = .ok c ∧
    OwnerState.returnBorrow a.names receipt.next.owners receipt.next.frame c.frame a.token =
      some c.owners ∧ SimRel a c world := by
  have borrowed := (borrow_sim simulation start length rights borrower receipt produced).1
  have returned := ram_view_return simulation.valid receipt
  exact ⟨borrowed, returned, OwnerState.borrow_return simulation.valid.2.1 receipt.borrowed,
    returnView_sim borrowed returned⟩

end Gabbro.Grammatik.LowLevel
