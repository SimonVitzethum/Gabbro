module

public import Grammatik.Niedrig.Konstrukte.Klassen.Modell

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration} {P I : Type}

/-- The class extension of the existing proof replay, over the SAME Context,
    owner operations, World and stores. No source interpreter is introduced.
    Existing RAM SimRel embeds without reinterpreting a device as RAM. -/
inductive ClassReplay (a : Authority D) (layout : AdressLayout D) :
    Context D P I → World D → Prop where
  | ordinary {c : Context D P I} {world : World D}
      (simulation : SimRel a c world) : ClassReplay a layout c world
  | borrow {c : Context D P I} {world : World D} {memoryClass : MemoryClass}
      (previous : ClassReplay a layout c world) (r : ClassViewResult a layout c memoryClass) :
      ClassReplay a layout r.next world
  | restore {c next : Context D P I} {world : World D}
      (previous : ClassReplay a layout c world) (returned : returnView a c = .ok next) :
      ClassReplay a layout next world
  | store {c : Context D P I} {world : World D}
      (previous : ClassReplay a layout c world) (view : View D)
      (live : view ∈ c.views) (active : c.frame = view.borrower)
      (ram : view.span.memoryClass = .ordinaryRam)
      (field : D.Feld view.span.table) (index : Int)
      (value : Wert D (D.typ view.span.table field))
      (resources : List (Res D)) (writes : D.Tab → Bool)
      (checked : ViewPutOk view layout field index resources writes)
      (held : HeldIn resources world.haelt) :
      ClassReplay a layout c (viewPutStep view layout field index value resources writes checked world)
  | observe {c : Context D P I} {world : World D}
      (previous : ClassReplay a layout c world) (register : D.Reg) :
      ClassReplay a layout c (world.fragt (.inr (.inl register)))
  | metadata {c : Context D P I} {world : World D}
      (previous : ClassReplay a layout c world) (privilege : P) (interrupt : I) :
      ClassReplay a layout { c with privilege := privilege, interrupt := interrupt } world
  | foreign {c : Context D P I} {world nextWorld : World D} {Γ : Ctx} {resources : List (Res D)}
      (previous : ClassReplay a layout c world) (oracle : Orakel D) (item : D.Ax)
      (args : Args D Γ resources (D.aparams item)) (env : Env D Γ)
      (before after : OwnerBindings D.Marke) (source into : Nat)
      (checked : BindCtxOk item a.token.mark a.token.stage before after source into)
      (empty : c.views = []) (owned : c.owners.owns a.names c.frame a.token)
      (answer : Option (ErgVal D (D.aerg item) ⊕ Fin (D.agruende item)))
      (invoked : bindCtxStep oracle item a.token.mark a.token.stage args env before after source into checked world =
        some (after, nextWorld, answer)) (writes : D.Tab → Bool) (globals : D.Glob → Bool)
      (effect : Gut writes globals world nextWorld) : ClassReplay a layout c nextWorld

/-- Class-aware preservation, separate from source admission. The RAM-only
    SimRel cannot contain a device view: its fixed Valid predicate rules it
    out. This extension keeps real owner-operation provenance for both classes. -/
structure ClassSimRel (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) (world : World D) : Prop where
  valid : ClassContextValid a layout c
  replay : ClassReplay a layout c world

theorem classSimRel_of_simRel {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {world : World D} (simulation : SimRel a c world)
    (pairing : ∀ v ∈ c.views, SpacePairing v.span layout ∧ v.span.owner ∈ D.eigner v.span.table) :
    ClassSimRel a layout c world := by
  refine ⟨⟨simulation.valid.1, simulation.valid.2.1, simulation.valid.2.2.1,
    ?_, simulation.valid.2.2.2.2⟩, .ordinary simulation⟩
  intro v member
  obtain ⟨span, epoch, memoryClass, low, high, owner, spanEpoch, permissions,
    read, write, rightsOwner, alignment, base, length, mapped, initialized⟩ :=
    simulation.valid.2.2.2.1 v member
  exact ⟨span, epoch, .inl memoryClass, low, high, owner, spanEpoch, permissions,
    read, write, rightsOwner, alignment, base, length, mapped, initialized,
    (pairing v member).1, (simulation.valid.1.2.2.1 v.span span).1, (pairing v member).2⟩

theorem bindClassViewStep_sim {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {world : World D} {memoryClass : MemoryClass}
    (simulation : ClassSimRel a layout c world) (r : ClassViewResult a layout c memoryClass) :
    ClassSimRel a layout r.next world :=
  ⟨classBorrow_preserves simulation.valid r, .borrow simulation.replay r⟩

theorem classReturnStep_sim {a : Authority D} {layout : AdressLayout D}
    {c next : Context D P I} {world : World D}
    (simulation : ClassSimRel a layout c world) (returned : returnView a c = .ok next) :
    ClassSimRel a layout next world :=
  ⟨classReturn_preserves simulation.valid returned, .restore simulation.replay returned⟩

theorem classViewPutStep_sim {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {world : World D} (simulation : ClassSimRel a layout c world)
    (view : View D) (live : view ∈ c.views) (active : c.frame = view.borrower)
    (ram : view.span.memoryClass = .ordinaryRam) (field : D.Feld view.span.table)
    (index : Int) (value : Wert D (D.typ view.span.table field))
    (resources : List (Res D)) (writes : D.Tab → Bool)
    (checked : ViewPutOk view layout field index resources writes)
    (held : HeldIn resources world.haelt) :
    ClassSimRel a layout c (viewPutStep view layout field index value resources writes checked world) :=
  ⟨simulation.valid, .store simulation.replay view live active ram field index value resources writes checked held⟩

theorem classMetadata_sim {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {world : World D} (simulation : ClassSimRel a layout c world)
    (privilege : P) (interrupt : I) :
    ClassSimRel a layout { c with privilege := privilege, interrupt := interrupt } world :=
  ⟨simulation.valid, .metadata simulation.replay privilege interrupt⟩

/-- The dynamic access boundary paired with the finite per-operation checks.
    Preservation-only lemmas never substitute for live/active authorization. -/
theorem classViewAccess_authorized {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {world : World D} (simulation : ClassSimRel a layout c world)
    (view : View D) (live : view ∈ c.views) (active : c.frame = view.borrower) :
    ClassViewValid a layout view ∧ c.frame = view.borrower :=
  ⟨simulation.valid.2.2.2.1 view live, active⟩

/-- Closure restores the current lender on both returning channels. Stores
    remain in the World; there is no rollback, including on a reason exit. -/
def closeClassViewStep {ε α : Type} (outcome : Except ε α) (a : Authority D)
    (c : Context D P I) (world : World D) :
    Except ViewFailure (Except ε α × Context D P I) × World D :=
  ((returnView a c).map (fun restored => (outcome, restored)), world)

theorem closeClassViewStep_both {ε α : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {memoryClass : MemoryClass} (simulation : ClassContextValid a layout c)
    (r : ClassViewResult a layout c memoryClass) (world : World D) (value : α) (reason : ε) :
    closeClassViewStep (.ok value : Except ε α) a r.next world = (.ok (.ok value, c), world) ∧
    closeClassViewStep (.error reason : Except ε α) a r.next world = (.ok (.error reason, c), world) := by
  constructor <;> (unfold closeClassViewStep; rw [classBorrow_return simulation r]; rfl)

end Gabbro.Grammatik.LowLevel.Construct
