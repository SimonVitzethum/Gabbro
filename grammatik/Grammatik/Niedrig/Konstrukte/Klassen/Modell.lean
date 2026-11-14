module

public import Grammatik.Niedrig.Konstrukte.Kontext

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration}

/-- Shared RAM/device view invariant. Reserved storage is never admitted.
    Device accesses additionally require the register descriptor, never a slot
    load/store. The existing RAM-only invariant is retained unchanged. -/
def ClassViewValid (a : Authority D) (layout : AdressLayout D) (v : View D) : Prop :=
  v.span ∈ a.spans ∧ v.epoch = a.epoch ∧
  (v.span.memoryClass = .ordinaryRam ∨ v.span.memoryClass = .device) ∧
  v.span.base ≤ v.base ∧ v.base + v.length ≤ v.span.base + v.span.length ∧
  v.span.owner = a.token.mark ∧ v.span.epoch = a.epoch ∧
  (v.rights.read = true ∨ v.rights.write = true) ∧
  (v.rights.read = true → v.span.rights.read = true) ∧
  (v.rights.write = true → v.span.rights.write = true) ∧
  v.rights.owner = v.span.rights.owner ∧
  0 < v.span.alignment ∧ v.base % v.span.alignment = 0 ∧ v.length % v.span.alignment = 0 ∧
  v.span.mapped = true ∧ v.span.initialized = true ∧ SpacePairing v.span layout ∧
  v.span.Valid ∧ v.span.owner ∈ D.eigner v.span.table

instance (a : Authority D) (layout : AdressLayout D) (v : View D) :
    Decidable (ClassViewValid a layout v) := by
  unfold ClassViewValid
  infer_instance

def ClassContextValid {P I : Type} (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) : Prop :=
  a.Valid ∧ c.owners.ledger.valid ∧ c.owners.access a.names c.frame a.token ∧
  (∀ v ∈ c.views, ClassViewValid a layout v) ∧
  (∀ v ∈ c.views, ∀ w ∈ c.views, v ≠ w → v.Compatible w)

/-- Dynamic admission retains exact memoryClass and space pairing; two nominal
    names with one backing do not evade Compatible's physical overlap test. -/
def BindClassViewOk {P I : Type} (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) (memoryClass : MemoryClass) (v : View D) : Prop :=
  ClassViewValid a layout v ∧ v.span.memoryClass = memoryClass ∧
  v.lender = c.frame ∧ v.span.base ≤ v.base ∧ v.base < v.span.base + v.span.length ∧
  v.borrower ≠ c.frame ∧
  (∀ w ∈ c.views, v.Compatible w ∧ w.Compatible v)

instance {P I : Type} (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) (memoryClass : MemoryClass) (v : View D) :
    Decidable (BindClassViewOk a layout c memoryClass v) := by
  unfold BindClassViewOk
  infer_instance

def bindClassViewB {P I : Type} (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) (memoryClass : MemoryClass) (v : View D) : Bool :=
  decide (BindClassViewOk a layout c memoryClass v)

theorem bindClassViewB_iff {P I : Type} (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) (memoryClass : MemoryClass) (v : View D) :
    bindClassViewB a layout c memoryClass v = true ↔ BindClassViewOk a layout c memoryClass v := by
  simp only [bindClassViewB, decide_eq_true_eq]

/-- Same Context and OwnerState as RAM borrowing; no device token is minted. -/
structure ClassViewResult {P I : Type} (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) (memoryClass : MemoryClass) where
  view : View D
  checked : BindClassViewOk a layout c memoryClass view
  owners : OwnerState D
  borrowed : OwnerState.borrow a.names c.owners c.frame view.borrower a.token = some owners

def ClassViewResult.next {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {memoryClass : MemoryClass} (r : ClassViewResult a layout c memoryClass) : Context D P I :=
  { c with owners := r.owners, frame := r.view.borrower, views := r.view :: c.views }

/-- Same diagnostic order as checkView: authority, bounds, class, rights,
    alignment, mapping, initialization, conflicts, then the actual escrow.
    Space pairing is an authority check, not a hardware-stop classification.
    The final fallback is unreachable when BindClassViewOk has failed and
    all preceding checks passed; it never fabricates a successful receipt. -/
def classViewFailure {P I : Type} (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) (memoryClass : MemoryClass) (v : View D) : ViewFailure :=
  if v.span ∈ a.spans ∧ v.span.owner = a.token.mark ∧ v.span.epoch = a.epoch ∧
      v.epoch = a.epoch ∧ v.lender = c.frame ∧ v.span.Valid ∧
      v.span.owner ∈ D.eigner v.span.table ∧ SpacePairing v.span layout then
    if v.span.base ≤ v.base ∧ v.base < v.span.base + v.span.length ∧
        v.base + v.length ≤ v.span.base + v.span.length then
      if v.span.memoryClass = memoryClass ∧
          (v.span.memoryClass = .ordinaryRam ∨ v.span.memoryClass = .device) then
        if (v.rights.read = true ∨ v.rights.write = true) ∧
            (v.rights.read = true → v.span.rights.read = true) ∧
            (v.rights.write = true → v.span.rights.write = true) ∧
            v.rights.owner = v.span.rights.owner then
          if 0 < v.span.alignment ∧ v.base % v.span.alignment = 0 ∧ v.length % v.span.alignment = 0 then
            if v.span.mapped = true then
              if v.span.initialized = true then
                if v.borrower ≠ c.frame ∧ (∀ w ∈ c.views, v.Compatible w ∧ w.Compatible v) then
                  .escrow
                else .conflictingLoan
              else .initialization
            else .mapping
          else .alignment
        else .permissions
      else .memoryClass
    else .bounds
  else .authority

/-- Refusal preserves the caller. G6 derives the candidate from the evaluated
    address and the declared span; the complete request equality is explicit. -/
def bindClassViewStep {P I : Type} (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) (memoryClass : MemoryClass) (v : View D) (world : World D) :
    Except ViewFailure (ClassViewResult a layout c memoryClass) × World D :=
  (if checked : BindClassViewOk a layout c memoryClass v then
    match borrowed : OwnerState.borrow a.names c.owners c.frame v.borrower a.token with
    | none => .error .escrow
    | some owners => .ok ⟨v, checked, owners, borrowed⟩
   else .error (classViewFailure a layout c memoryClass v), world)

theorem bindClassViewStep_world {P I : Type} (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) (memoryClass : MemoryClass) (v : View D) (world : World D) :
    (bindClassViewStep a layout c memoryClass v world).2 = world := rfl

theorem bindClassViewStep_success {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {memoryClass : MemoryClass} (r : ClassViewResult a layout c memoryClass) (world : World D) :
    bindClassViewStep a layout c memoryClass r.view world = (.ok r, world) := by
  cases r with
  | mk view checked owners borrowed =>
    rw [bindClassViewStep, dif_pos checked]
    split
    · rename_i heq
      rw [borrowed] at heq
      cases heq
    · rename_i owners' heq
      have e : owners' = owners := Option.some.inj (heq.symm.trans borrowed)
      subst e
      rfl

theorem bindClassViewStep_refused {P I : Type} (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) (memoryClass : MemoryClass) (v : View D) (world : World D)
    (refused : ¬ BindClassViewOk a layout c memoryClass v) :
    bindClassViewStep a layout c memoryClass v world =
      (.error (classViewFailure a layout c memoryClass v), world) := by
  simp only [bindClassViewStep, dif_neg refused]

theorem bindClassViewStep_request {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {memoryClass : MemoryClass} {v : View D} {world : World D}
    {r : ClassViewResult a layout c memoryClass}
    (produced : (bindClassViewStep a layout c memoryClass v world).1 = .ok r) : r.view = v := by
  unfold bindClassViewStep at produced
  split at produced
  · split at produced
    · cases produced
    · cases produced; rfl
  · cases produced

theorem classBorrow_preserves {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {memoryClass : MemoryClass}
    (valid : ClassContextValid a layout c) (r : ClassViewResult a layout c memoryClass) :
    ClassContextValid a layout r.next := by
  have grant := OwnerState.borrow_grant (D := D) valid.2.1 r.borrowed
  refine ⟨valid.1, grant.1, grant.2.1, ?_, ?_⟩
  · intro v member
    rcases List.mem_cons.mp member with same | old
    · subst v; exact r.checked.1
    · exact valid.2.2.2.1 v old
  · intro v vm w wm different
    rcases List.mem_cons.mp vm with same | old
    · subst v
      rcases List.mem_cons.mp wm with same | old
      · exact False.elim (different same.symm)
      · exact (r.checked.2.2.2.2.2.2 w old).1
    · rcases List.mem_cons.mp wm with same | oldw
      · subst w; exact (r.checked.2.2.2.2.2.2 v old).2
      · exact valid.2.2.2.2 v old w oldw different

theorem classBorrow_return {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {memoryClass : MemoryClass}
    (valid : ClassContextValid a layout c) (r : ClassViewResult a layout c memoryClass) :
    returnView a r.next = .ok c := by
  have returned := OwnerState.borrow_return (D := D) valid.2.1 r.borrowed
  simp only [returnView, ClassViewResult.next, r.checked.2.2.1, returned, ↓reduceIte]

theorem classReturn_preserves {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c next : Context D P I} (valid : ClassContextValid a layout c)
    (returned : returnView a c = .ok next) : ClassContextValid a layout next := by
  obtain ⟨view, rest, stack, active, popped, frame, tail, _, _⟩ := returnView_ledger returned
  have grant := OwnerState.returnBorrow_grant (D := D) valid.2.1 popped
  refine ⟨valid.1, grant.1, ?_, ?_, ?_⟩
  · rw [frame]; exact grant.2.1
  · intro v member
    rw [tail] at member
    exact valid.2.2.2.1 v (by rw [stack]; exact List.mem_cons_of_mem _ member)
  · intro v vm w wm different
    rw [tail] at vm wm
    exact valid.2.2.2.2 v (by rw [stack]; exact List.mem_cons_of_mem _ vm)
      w (by rw [stack]; exact List.mem_cons_of_mem _ wm) different

end Gabbro.Grammatik.LowLevel.Construct
