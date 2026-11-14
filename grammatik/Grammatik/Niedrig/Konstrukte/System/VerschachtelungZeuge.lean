module

public import Grammatik.Niedrig.Konstrukte.System.Fixture

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct.Witness

open Niedrig

/-- The outer handler deliberately unmasks, permitting a strictly higher
    declared priority. The incoming mode is kernel, not a second user entry. -/
def outerUnmasked : SystemContext D := (maskSetStep entered false rfl before).1

def innerFrame : Eingang.EntryFrame := irqFrameAt irqFrame .kern

def innerChecked : IrqEnterOk outerUnmasked innerFrame handlerTable 129 6 3 := by decide

def innerEntered : SystemContext D :=
  (irqEnterStep outerUnmasked innerFrame handlerTable 129 6 3 innerChecked before).1

def innerDelivered (core vector handler priority : Nat) (boundary : Bool) : Prop :=
  core = 0 ∧ vector = 129 ∧ handler = 6 ∧ priority = 3 ∧ boundary = true

theorem innerHardware : IrqDelivery handlerTable outerUnmasked.interrupt innerDelivered := by
  intro core vector handler priority boundary arrival
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := arrival
  exact ⟨rfl, rfl, rfl, by decide, by decide⟩

def innerEntryDuty : IrqEntryDuty systemNames 1 outerUnmasked innerFrame handlerTable 129 6 3 innerDelivered :=
  { origin := ⟨rfl, rfl⟩
    named := rfl
    declaration := ⟨{ Eingang.zeigeEingang with vektor := some (.lit 129) }, Eingang.zeigeRahmen,
      (frameOf_replaceVector Eingang.zeigeEingang (.lit 128) (.lit 129) rfl).trans Eingang.zeigeRahmenOk,
      rfl, rfl⟩
    checked := innerChecked
    hardware := innerHardware
    arrival := ⟨rfl, rfl, rfl, rfl, rfl⟩ }

def innerReturnFrame : Eingang.EntryFrame := { irqReturnFrame with privNach := .kern }

def innerExitChecked : IrqExitOk innerEntered innerReturnFrame false [false] 1 [0] := by decide

def innerReturnDuty : IrqReturnDuty outerUnmasked innerEntered innerReturnFrame false [false] 1 [0] :=
  ⟨innerExitChecked, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nested_irq_delivery_zeuge :
    handlerTable 0 129 = some (6, 3) ∧
    (outerUnmasked.interrupt.maske.zustand 0).maskiert = false ∧
    (outerUnmasked.interrupt.prio 0).aktuell < 3 := irqEntryDuty_delivery innerEntryDuty

theorem nested_irq_depth_zeuge :
    (innerEntered.interrupt.maske.zustand 0).tiefe = 2 ∧
    (innerEntered.interrupt.prio 0).unterbrochen = [1, 0] :=
  ⟨Maske.betreteNachTiefe outerUnmasked.interrupt.maske 0,
    Maske.erhoeheNachStapel outerUnmasked.interrupt 0 3 true⟩

theorem nested_irq_return_zeuge :
    (irqExitStep innerEntered innerReturnFrame false [false] 1 [0] innerExitChecked before).1.privilege.priv = .kern ∧
    ((irqExitStep innerEntered innerReturnFrame false [false] 1 [0] innerExitChecked before).1.interrupt.prio 0).aktuell = 1 ∧
    ((irqExitStep innerEntered innerReturnFrame false [false] 1 [0] innerExitChecked before).1.interrupt.maske.zustand 0).tiefe = 1 :=
  ⟨innerReturnDuty.resume, Maske.senkeNachAktuell _ _ _ _,
    Maske.verlasseNachTiefe innerEntered.interrupt.maske 0 false [false]⟩

theorem priority_table_refusal_zeuge :
    irqEnterB outerUnmasked innerFrame handlerTable 129 6 2 = false ∧
    irqEnterB outerUnmasked innerFrame handlerTable 128 5 1 = false := ⟨by decide, by decide⟩

end Gabbro.Grammatik.LowLevel.Construct.Witness
