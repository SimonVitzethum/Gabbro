module

public import Grammatik.Niedrig.Konstrukte.System.Bindung

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

open Niedrig

variable {D : Deklaration}

/-- Actual binding-call replay, including the updated World, before dispatch
    to value/reason continuations. Gut is the existing frame/trace obligation,
    discharged with bindCtxCall_gut, not a new hardware safety assumption. -/
theorem systemBindingStep_sim {Γ : Ctx} {resources : List (Res D)}
    (oracle : Orakel D) (a : Authority D) (layout : AdressLayout D) (c : SystemContext D)
    (item : D.Ax) (named : D.Annahme) (args : Args D Γ resources (D.aparams item)) (env : Env D Γ)
    (before after : OwnerBindings D.Marke) (source into : Nat)
    (checked : SystemCallOk a c item named before after source into)
    (nextArch : Arch.ArchState) (nextInterrupt : Maske.PrioMaske)
    (world nextWorld : World D) (answer : Option (ErgVal D (D.aerg item) ⊕ Fin (D.agruende item)))
    (simulation : ClassSimRel a layout c world)
    (invoked : bindCtxStep oracle item a.token.mark a.token.stage args env before after source into checked.1 world =
      some (after, nextWorld, answer))
    (writes : D.Tab → Bool) (globals : D.Glob → Bool) (effect : Gut writes globals world nextWorld) :
    let next := match answer with
      | some (.inl _) => { c with privilege := nextArch, interrupt := nextInterrupt }
      | _ => c
    systemBindingStep oracle a c item named args env before after source into checked
      nextArch nextInterrupt world = some (after, next, nextWorld, answer) ∧
      ClassSimRel a layout next nextWorld := by
  have called : ClassSimRel a layout c nextWorld :=
    ⟨simulation.valid, .foreign simulation.replay oracle item args env before after source into checked.1
      checked.2.2.1 checked.2.2.2 answer invoked writes globals effect⟩
  constructor
  · simp only [systemBindingStep, invoked, bind, Option.bind_some, pure]
    cases answer with
    | none => rfl
    | some r => cases r <;> rfl
  · cases answer with
    | none => exact called
    | some result =>
      cases result with
      | inl value => exact classMetadata_sim called nextArch nextInterrupt
      | inr reason => exact called

/-- Named delivery discharges the local entry check's hardware half. Source
    descriptor and no-view requirements remain explicit software premises. -/
theorem irqEntryDuty_delivery {names : SystemAssumptions D} {item : D.Ax}
    {c : SystemContext D} {frame : Eingang.EntryFrame} {handlers : HandlerTable}
    {vector handler priority : Nat} {delivered : Nat → Nat → Nat → Nat → Bool → Prop}
    (duty : IrqEntryDuty names item c frame handlers vector handler priority delivered) :
    handlers c.privilege.kern vector = some (handler, priority) ∧
    (c.interrupt.maske.zustand c.privilege.kern).maskiert = false ∧
    (c.interrupt.prio c.privilege.kern).aktuell < priority := by
  have hardware := duty.hardware c.privilege.kern vector handler priority true duty.arrival
  exact ⟨hardware.2.1, hardware.2.2.1, hardware.2.2.2.2⟩

/-- Mask and priority models keep every other core intact, including across
    nested handler entry. Masking is never promoted to a multicore lock. -/
theorem irqEntered_other (state : Maske.PrioMaske) (core priority other : Nat) (different : other ≠ core) :
    (irqEntered state core priority).maske.zustand other = state.maske.zustand other ∧
    (irqEntered state core priority).prio other = state.prio other :=
  ⟨Maske.aufKernAnderer state.maske core other _ different,
    Maske.erhoeheNachAndererPrio state core other priority true different⟩

theorem irqExited_other (state : Maske.PrioMaske) (core : Nat) (mask : Bool) (masks : List Bool)
    (priority : Nat) (priorities : List Nat) (other : Nat) (different : other ≠ core) :
    (irqExited state core mask masks priority priorities).maske.zustand other = state.maske.zustand other ∧
    (irqExited state core mask masks priority priorities).prio other = state.prio other :=
  ⟨Maske.aufKernAnderer state.maske core other _ different,
    Maske.senkeNachAndererPrio state core other priority priorities different⟩

theorem irqReturn_resumes {interrupted current : SystemContext D} {frame : Eingang.EntryFrame}
    {mask : Bool} {masks : List Bool} {priority : Nat} {priorities : List Nat}
    (duty : IrqReturnDuty interrupted current frame mask masks priority priorities) (world : World D) :
    (irqExitStep current frame mask masks priority priorities duty.checked world).1.privilege.priv =
      interrupted.privilege.priv ∧
    ((irqExitStep current frame mask masks priority priorities duty.checked world).1.interrupt.maske.zustand
      current.privilege.kern).maskiert =
      (interrupted.interrupt.maske.zustand interrupted.privilege.kern).maskiert ∧
    ((irqExitStep current frame mask masks priority priorities duty.checked world).1.interrupt.prio
      current.privilege.kern).aktuell = (interrupted.interrupt.prio interrupted.privilege.kern).aktuell :=
  ⟨duty.resume, (Maske.verlasseNachMaskiert _ _ _ _).trans duty.savedMask,
    (Maske.senkeNachAktuell _ _ _ _).trans duty.savedPriority⟩

end Gabbro.Grammatik.LowLevel.Construct
