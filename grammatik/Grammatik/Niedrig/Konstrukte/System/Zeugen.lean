module

public import Grammatik.Niedrig.Konstrukte.System.Fixture

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct.Witness

open Niedrig

theorem named_binding_zeuge :
    systemCallB authority systemInitial 0 systemNames.Mmu ghost renamedGhost 10 11 = true ∧
    systemCallB authority systemInitial 1 systemNames.IrqDelivery ghost renamedGhost 10 11 = true ∧
    systemCallB authority systemInitial 1 systemNames.Mmu ghost renamedGhost 10 11 = false :=
  ⟨by decide, by decide, by decide⟩

theorem mmu_install_zeuge :
    switched.privilege.wurzel = 1 ∧ switched.privilege.kern = 0 ∧
    ClassSimRel authority layout switched before :=
  ⟨rfl, rfl, mmuInstallStep_sim systemInitial_sim [0, 1] 1 true true rootChecked⟩

theorem mmu_translation_zeuge :
    observedTranslation switched.privilege.wurzel 0 = Uebersetzung.walk regime pageTables 1 0 :=
  mmuInstallStep_translation rootChecked before mmuHardware 0

theorem mmu_readiness_zeuge :
    (1 ∈ ([0, 1] : List Nat)) ∧ observedTranslation 1 0 = Uebersetzung.walk regime pageTables 1 0 :=
  ⟨rootDuty.readySound rfl, rootDuty.syncSound rfl⟩

theorem mmu_user_refusal_zeuge : mmuInstallB userInitial [0, 1] 1 true true = false := by decide

theorem mmu_binding_invoke_zeuge :
    bindCtxStep (resources := []) oracle 0 true 0 .nil .nil ghost renamedGhost 10 11
      mmuCall.1 before = some (renamedGhost, before.fragt (.inl 0), some (.inl ())) :=
  bindCtxStep_eq oracle 0 true 0 .nil .nil ghost renamedGhost 10 11 mmuCall.1 before

theorem mmu_binding_sim_zeuge :
    ClassSimRel authority layout
      { systemInitial with privilege := switched.privilege, interrupt := systemInitial.interrupt }
      (before.fragt (.inl 0)) :=
  (systemBindingStep_sim (resources := []) oracle authority layout systemInitial 0 systemNames.Mmu .nil .nil
    ghost renamedGhost 10 11 mmuCall switched.privilege systemInitial.interrupt
    before (before.fragt (.inl 0)) (some (.inl ())) systemInitial_sim mmu_binding_invoke_zeuge
    (fun _ => false) (fun _ => false) (gut_fragt before (.inl 0))).2

theorem mask_two_cores_zeuge :
    ((maskSetStep systemInitial true rfl before).1.interrupt.maske.zustand 0).maskiert = true ∧
    (maskSetStep systemInitial false rfl before).1.interrupt.maske.zustand 1 =
      systemInitial.interrupt.maske.zustand 1 :=
  ⟨maskSetStep_mask systemInitial true rfl before,
    maskSetStep_other systemInitial false rfl before 1 (by decide)⟩

theorem irq_entry_zeuge :
    Maske.MaskStep (.betreteHandler 0 128) userInitial.interrupt.maske entered.interrupt.maske ∧
    entered.privilege.priv = .kern ∧
    ClassSimRel authority layout entered before :=
  ⟨irqEnterStep_mask irqChecked, rfl,
    irqEnterStep_sim (classMetadata_sim systemInitial_sim userInitial.privilege userInitial.interrupt)
      irqFrame handlerTable 128 5 1 irqChecked⟩

theorem irq_delivery_zeuge :
    handlerTable 0 128 = some (5, 1) ∧
    (userInitial.interrupt.maske.zustand 0).maskiert = false ∧
    (userInitial.interrupt.prio 0).aktuell < 1 := irqEntryDuty_delivery entryDuty

theorem irq_entry_refusal_zeuge :
    irqEnterB entered { irqFrame with privVor := .kern } handlerTable 128 5 2 = false ∧
    irqEnterB userInitial irqFrame handlerTable 130 5 1 = false := ⟨by decide, by decide⟩

theorem irq_exit_zeuge :
    Maske.MaskStep (.verlasseHandler 0) entered.interrupt.maske
      (irqExitStep entered irqReturnFrame false [] 0 [] exitChecked before).1.interrupt.maske ∧
    ((irqExitStep entered irqReturnFrame false [] 0 [] exitChecked before).1.interrupt.maske.zustand 0).maskiert = false ∧
    ((irqExitStep entered irqReturnFrame false [] 0 [] exitChecked before).1.interrupt.prio 0).aktuell = 0 :=
  ⟨irqExitStep_mask exitChecked, Maske.verlasseNachMaskiert _ _ _ _, Maske.senkeNachAktuell _ _ _ _⟩

theorem irq_other_core_zeuge :
    entered.interrupt.maske.zustand 1 = userInitial.interrupt.maske.zustand 1 ∧
    entered.interrupt.prio 1 = userInitial.interrupt.prio 1 :=
  irqEntered_other userInitial.interrupt 0 1 1 (by decide)

theorem firmware_handoff_zeuge :
    ClassSimRel systemHandoff.authority layout systemHandoff.next before ∧
    systemBoot.root systemHandoff.authority systemHandoff.next ∧
    ∀ frame, ¬ systemHandoff.next.owners.access authority.names frame authority.token :=
  ⟨bootHandoffStep_sim (simRel_initial systemInitial_valid rfl before) systemHandoff layout,
    bootHandoffStep_root systemFirmware systemBoot_logic systemHandoff systemHandoff_contract⟩

theorem firmware_names_zeuge :
    D.axBeleg 0 = some systemNames.Mmu ∧ D.axBeleg 1 = some systemNames.IrqDelivery ∧
    D.axBeleg 2 = some systemNames.FirmwareEntry ∧ systemNames.Mmu ≠ systemNames.IrqDelivery ∧
    systemNames.IrqDelivery ≠ systemNames.FirmwareEntry := ⟨rfl, rfl, rfl, by decide, by decide⟩

theorem firmware_entry_zeuge :
    ClassSimRel authority layout
      (firmwareEntryStep systemNames 2 systemBoot authority systemInitial bootDeclaration
        systemFirmware bootChecked before).1 before :=
  firmwareEntryStep_sim systemNames 2 systemBoot authority systemInitial bootDeclaration
    systemFirmware bootChecked layout before

theorem boot_descriptor_zeuge :
    Eingang.frameOf bootDeclaration = .ok (Eingang.rahmenAus bootDeclaration) :=
  firmwareEntryStep_descriptor bootChecked

end Gabbro.Grammatik.LowLevel.Construct.Witness
