module

public import Grammatik.Niedrig.Konstrukte.Klassen.Simulation
public import Grammatik.Niedrig.Arch.Zustand
public import Grammatik.Niedrig.Maske.Prio

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

open Niedrig

variable {D : Deklaration}

/-- Assumption identities are supplied by the unit's target binding. These
    are names in D, not new logical axioms or promises about software. -/
structure SystemAssumptions (D : Deklaration) where
  Mmu : D.Annahme
  IrqDelivery : D.Annahme
  FirmwareEntry : D.Annahme
  distinct : Mmu ≠ IrqDelivery ∧ Mmu ≠ FirmwareEntry ∧ IrqDelivery ≠ FirmwareEntry

abbrev SystemContext (D : Deklaration) := Context D Arch.ArchState Maske.PrioMaske

/-- The context owns the whole grant, has no outstanding views and performs
    the existing checked linear source move. Hardware identity is exact. -/
def SystemCallOk (a : Authority D) (c : SystemContext D) (item : D.Ax) (named : D.Annahme)
    (before after : OwnerBindings D.Marke) (source into : Nat) : Prop :=
  BindCtxOk item a.token.mark a.token.stage before after source into ∧
  D.axBeleg item = some named ∧ c.views = [] ∧
  c.owners.owns a.names c.frame a.token

instance [DecidableEq D.Annahme] (a : Authority D) (c : SystemContext D)
    (item : D.Ax) (named : D.Annahme) (before after : OwnerBindings D.Marke) (source into : Nat) :
    Decidable (SystemCallOk a c item named before after source into) := by
  unfold SystemCallOk
  infer_instance

def systemCallB [DecidableEq D.Annahme] (a : Authority D) (c : SystemContext D)
    (item : D.Ax) (named : D.Annahme) (before after : OwnerBindings D.Marke) (source into : Nat) : Bool :=
  decide (SystemCallOk a c item named before after source into)

theorem systemCallB_iff [DecidableEq D.Annahme] (a : Authority D) (c : SystemContext D)
    (item : D.Ax) (named : D.Annahme) (before after : OwnerBindings D.Marke) (source into : Nat) :
    systemCallB a c item named before after source into = true ↔
      SystemCallOk a c item named before after source into := by
  simp only [systemCallB, decide_eq_true_eq]

/-- Shared binding execution for all system operations. Only a successful
    VALUE answer installs architectural metadata. A reason retains metadata,
    while both returning channels retain the moved source inventory. A hardware
    stop remains a stop. The actual World's effects are bindCtxStep's effects.
    G6 still supplies RufPasst, answer checks, effects and the user's contract. -/
def systemBindingStep {Γ : Ctx} {resources : List (Res D)}
    (oracle : Orakel D) (a : Authority D) (c : SystemContext D)
    (item : D.Ax) (named : D.Annahme) (args : Args D Γ resources (D.aparams item)) (env : Env D Γ)
    (before after : OwnerBindings D.Marke) (source into : Nat)
    (checked : SystemCallOk a c item named before after source into)
    (nextArch : Arch.ArchState) (nextInterrupt : Maske.PrioMaske) (world : World D) :
    Option (OwnerBindings D.Marke × SystemContext D × World D ×
      Option (ErgVal D (D.aerg item) ⊕ Fin (D.agruende item))) := do
  let (moved, nextWorld, answer) ← bindCtxStep oracle item a.token.mark a.token.stage args env
    before after source into checked.1 world
  let next := match answer with
    | some (.inl _) => { c with privilege := nextArch, interrupt := nextInterrupt }
    | _ => c
  pure (moved, next, nextWorld, answer)

theorem systemCall_named {a : Authority D} {c : SystemContext D} {item : D.Ax} {named : D.Annahme}
    {before after : OwnerBindings D.Marke} {source into : Nat}
    (checked : SystemCallOk a c item named before after source into) :
    D.axHerkunft item = some .hardware ∧ D.axBeleg item = some named ∧ c.views = [] :=
  ⟨checked.1.1.1, checked.2.1, checked.2.2.1⟩

/-- Target-binding state functions change metadata only. The oracle call's
    World effects have the separate bindCtxCall_gut theorem and contract duty. -/
def systemMetadataStep (c : SystemContext D) (arch : Arch.ArchState)
    (interrupt : Maske.PrioMaske) (world : World D) : SystemContext D × World D :=
  ({ c with privilege := arch, interrupt := interrupt }, world)

theorem systemMetadataStep_sim {a : Authority D} {layout : AdressLayout D}
    {c : SystemContext D} {world : World D} (simulation : ClassSimRel a layout c world)
    (arch : Arch.ArchState) (interrupt : Maske.PrioMaske) :
    ClassSimRel a layout (systemMetadataStep c arch interrupt world).1
      (systemMetadataStep c arch interrupt world).2 := classMetadata_sim simulation arch interrupt

/-- All system primitives use the existing bindCtx cost and signature effect
    predicates, including arguments and both continuations. No constant-cost
    assertion is made for firmware, a page-table walk or generated entry code. -/
def systemCallCost (args reason rest : Nat) : Nat := bindCtxCost args reason rest

def systemCallFootprint (arguments : List (D.Tab ⊕ D.Glob)) : D.Tab ⊕ D.Glob → Prop :=
  CtxReads arguments

/-- Metadata primitives have no carrier effects; effects of the binding and
    generated entry code are checked separately by their ordinary contracts. -/
def systemMetadataFootprint : Footprint D := Footprint.empty

end Gabbro.Grammatik.LowLevel.Construct
