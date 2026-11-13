module

public import Grammatik.Niedrig.Konstrukte.Sicht

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration} {P I : Type}

/-- Canonical failure identities. Selection can report bounds before checkView;
    checkView itself keeps its existing ordered checks. No check is reordered. -/
def viewFailureCode : ViewFailure → Fin 10
  | .authority => ⟨0, by omega⟩
  | .bounds => ⟨1, by omega⟩
  | .memoryClass => ⟨2, by omega⟩
  | .permissions => ⟨3, by omega⟩
  | .alignment => ⟨4, by omega⟩
  | .mapping => ⟨5, by omega⟩
  | .initialization => ⟨6, by omega⟩
  | .conflictingLoan => ⟨7, by omega⟩
  | .escrow => ⟨8, by omega⟩
  | .noView => ⟨9, by omega⟩

theorem viewFailureCode_injective : Function.Injective viewFailureCode := by
  intro first second equal
  have values := congrArg Fin.val equal
  cases first <;> cases second <;> simp only [viewFailureCode] at values <;> first | rfl | omega

/-- The checked admission changes only ghost escrow. The actual G binder
    binds Unit; SimRel supplies its Context and its successful receipt. -/
def bindViewStep {space : Space D} (a : Authority D) (c : Context D P I)
    (start : Address space) (length : Nat) (rights : DataRights) (borrower : ArenaOwnership.Frame)
    (world : World D) : Except ViewFailure (ViewResult a c) × World D :=
  (ram_view a c start length rights borrower, world)

def returnViewStep (a : Authority D) (c : Context D P I) (world : World D) :
    Except ViewFailure (Context D P I) × World D := (returnView a c, world)

theorem bindViewStep_frame {space : Space D} (a : Authority D) (c : Context D P I)
    (start : Address space) (length : Nat) (rights : DataRights) (borrower : ArenaOwnership.Frame)
    (world : World D) : (bindViewStep a c start length rights borrower world).2 = world := rfl

theorem returnViewStep_frame (a : Authority D) (c : Context D P I) (world : World D) :
    (returnViewStep a c world).2 = world := rfl

theorem bindViewStep_sim {space : Space D} (a : Authority D) (c : Context D P I)
    (start : Address space) (length : Nat) (rights : DataRights) (borrower : ArenaOwnership.Frame)
    (world : World D) (simulation : SimRel a c world) :
    match (bindViewStep a c start length rights borrower world).1 with
    | .error _ => SimRel a c world
    | .ok receipt => SimRel a receipt.next world :=
  ram_view_step_sim simulation start length rights borrower

theorem returnViewStep_sim {a : Authority D} {c c' : Context D P I} {world : World D}
    (simulation : SimRel a c world) (returned : (returnViewStep a c world).1 = .ok c') :
    SimRel a c' (returnViewStep a c world).2 := returnView_sim simulation returned

/-- Close a returning scope before delivering EITHER its value or its reason.
    Memory is outside Except: a refused close cannot roll back body stores.
    Non-returning exits are excluded by the future scope-depth checker. -/
def closeViewExitStep {α ρ : Type} (outcome : Except ρ α)
    (a : Authority D) (c : Context D P I) (world : World D) :
    Except ViewFailure (Except ρ α × Context D P I) × World D :=
  (match returnView a c with
   | .error reason => .error reason
   | .ok restored => .ok (outcome, restored), world)

theorem closeViewExitStep_frame {α ρ : Type} (outcome : Except ρ α)
    (a : Authority D) (c : Context D P I) (world : World D) :
    (closeViewExitStep outcome a c world).2 = world := rfl

theorem closeViewExitStep_success {α ρ : Type} (outcome : Except ρ α)
    {a : Authority D} {c restored : Context D P I} (world : World D)
    (returned : returnView a c = .ok restored) :
    closeViewExitStep outcome a c world = (.ok (outcome, restored), world) := by
  simp only [closeViewExitStep, returned]

theorem closeViewExitStep_sim {α ρ : Type} (outcome : Except ρ α)
    {a : Authority D} {c restored : Context D P I} {world : World D}
    (simulation : SimRel a c world) {delivered : Except ρ α}
    (closed : (closeViewExitStep outcome a c world).1 = .ok (delivered, restored)) :
    delivered = outcome ∧ SimRel a restored (closeViewExitStep outcome a c world).2 := by
  cases returned : returnView a c with
  | error reason => simp only [closeViewExitStep, returned] at closed; cases closed
  | ok next =>
    simp only [closeViewExitStep, returned] at closed
    cases closed
    exact ⟨rfl, returnView_sim simulation returned⟩

/-- A full callback equation shared by Block and Endblock. Admission refusal
    runs err in the caller context. A returning body is always closed first;
    its original success/reason payload survives the close unchanged. -/
def runViewScope {α ρ : Type} {space : Space D}
    (a : Authority D) (c : Context D P I) (start : Address space) (length : Nat)
    (rights : DataRights) (borrower : ArenaOwnership.Frame) (world : World D)
    (body : ViewResult a c → World D → Except ρ α × Context D P I × World D)
    (err : ViewFailure → World D → Except ρ α × World D) :
    Except ViewFailure (Except ρ α × Context D P I) × World D :=
  match ram_view a c start length rights borrower with
  | .error reason =>
    let result := err reason world
    (.ok (result.1, c), result.2)
  | .ok receipt =>
    let result := body receipt world
    closeViewExitStep result.1 a result.2.1 result.2.2

theorem runViewScope_opened {α ρ : Type} {space : Space D}
    (a : Authority D) (c : Context D P I) (start : Address space) (length : Nat)
    (rights : DataRights) (borrower : ArenaOwnership.Frame) (world : World D)
    (body : ViewResult a c → World D → Except ρ α × Context D P I × World D)
    (err : ViewFailure → World D → Except ρ α × World D) (receipt : ViewResult a c)
    (produced : ram_view a c start length rights borrower = .ok receipt) :
    runViewScope a c start length rights borrower world body err =
      closeViewExitStep (body receipt world).1 a (body receipt world).2.1 (body receipt world).2.2 := by
  simp only [runViewScope, produced]

/-- Generic preservation across the complete scope. The body and refusal
    continuation must supply their ordinary G simulation; admission and the
    mandatory close then preserve it on either returning payload channel. -/
theorem runViewScope_sim {α ρ : Type} {space : Space D}
    (a : Authority D) (c : Context D P I) (start : Address space) (length : Nat)
    (rights : DataRights) (borrower : ArenaOwnership.Frame) (world : World D)
    (body : ViewResult a c → World D → Except ρ α × Context D P I × World D)
    (err : ViewFailure → World D → Except ρ α × World D)
    (simulation : SimRel a c world)
    (bodySim : ∀ receipt, ram_view a c start length rights borrower = .ok receipt →
      SimRel a receipt.next world → SimRel a (body receipt world).2.1 (body receipt world).2.2)
    (errSim : ∀ reason, ram_view a c start length rights borrower = .error reason →
      SimRel a c (err reason world).2)
    {outcome : Except ρ α} {next : Context D P I}
    (executed : (runViewScope a c start length rights borrower world body err).1 = .ok (outcome, next)) :
    SimRel a next (runViewScope a c start length rights borrower world body err).2 := by
  cases produced : ram_view a c start length rights borrower with
  | error reason =>
    simp only [runViewScope, produced] at executed ⊢
    cases executed
    exact errSim reason produced
  | ok receipt =>
    have borrowed := (borrow_sim simulation start length rights borrower receipt produced).1
    have middle := bodySim receipt produced borrowed
    simp only [runViewScope, produced] at executed ⊢
    exact (closeViewExitStep_sim (body receipt world).1 middle executed).2

theorem runViewScope_frame {α ρ : Type} {space : Space D}
    (a : Authority D) (c : Context D P I) (start : Address space) (length : Nat)
    (rights : DataRights) (borrower : ArenaOwnership.Frame) (world : World D)
    (body : ViewResult a c → World D → Except ρ α × Context D P I × World D)
    (err : ViewFailure → World D → Except ρ α × World D)
    (writes : D.Tab → Bool) (globals : D.Glob → Bool)
    (bodyFrame : ∀ receipt, ram_view a c start length rights borrower = .ok receipt →
      Rahmen writes globals world (body receipt world).2.2)
    (errFrame : ∀ reason, ram_view a c start length rights borrower = .error reason →
      Rahmen writes globals world (err reason world).2) :
    Rahmen writes globals world (runViewScope a c start length rights borrower world body err).2 := by
  cases produced : ram_view a c start length rights borrower with
  | error reason => simpa only [runViewScope, produced] using errFrame reason produced
  | ok receipt =>
    simpa only [runViewScope, produced, closeViewExitStep] using bodyFrame receipt produced

/-- Both returning channels restore exactly the lender, without memory rollback. -/
theorem close_borrowed_both {α ρ : Type} {a : Authority D} {c : Context D P I}
    (valid : c.Valid a) (receipt : ViewResult a c) (world : World D)
    (value : α) (reason : ρ) :
    closeViewExitStep (.ok value : Except ρ α) a receipt.next world =
      (.ok (.ok value, c), world) ∧
    closeViewExitStep (.error reason : Except ρ α) a receipt.next world =
      (.ok (.error reason, c), world) :=
  ⟨closeViewExitStep_success _ world (ram_view_return valid receipt),
    closeViewExitStep_success _ world (ram_view_return valid receipt)⟩

def scopeFootprint : Footprint D := .empty

/-- locks overhead (2) plus bindCallElse dispatch (2), including a close on
    normal return and reason delivery. End-position dispatch adds three. -/
def bindViewCost (request body err : Nat) : Nat := 4 + request + max (body + 1) (err + 2)

def bindViewEndCost (request body err : Nat) : Nat := 3 + bindViewCost request body err

theorem bindViewCost_body_bound (request body err : Nat) :
    body + 1 ≤ bindViewCost request body err := by unfold bindViewCost; omega

theorem bindViewCost_reason_bound (request body err : Nat) :
    err + 2 ≤ bindViewCost request body err := by unfold bindViewCost; omega

theorem bindViewEndCost_body_bound (request body err : Nat) :
    body + 1 ≤ bindViewEndCost request body err := by unfold bindViewEndCost bindViewCost; omega

theorem bindViewEndCost_reason_bound (request body err : Nat) :
    err + 2 ≤ bindViewEndCost request body err := by unfold bindViewEndCost bindViewCost; omega

end Gabbro.Grammatik.LowLevel.Construct
