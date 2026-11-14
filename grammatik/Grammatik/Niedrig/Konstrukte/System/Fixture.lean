module

public import Grammatik.Niedrig.Konstrukte.Fixture
public import Grammatik.Niedrig.Konstrukte.System.Erhaltung
public import Grammatik.Niedrig.Eingang.RahmenZeuge

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct.Witness

open Niedrig

def systemNames : SystemAssumptions D := ⟨0, 1, 2, by decide⟩

/-- Two cores have distinct initial mask bits. Masking core zero must keep
    core one's state, not merely another copy of the same constant state. -/
def systemInterrupt : Maske.PrioMaske :=
  { maske := { zustand := fun core => ⟨decide (core ≠ 0), 0, []⟩ }
    prio := Maske.anfangPrio }

def systemInitial : SystemContext D :=
  { owners := owners
    frame := OwnerWitness.root
    views := []
    privilege := ⟨.kern, 0, false, 3, 0⟩
    interrupt := systemInterrupt }

theorem systemInitial_valid : systemInitial.Valid authority := by
  refine ⟨authority_valid, owners_valid, initial_valid.2.2.1, ?_, ?_⟩
  · intro v member
    cases member
  · intro v member
    cases member

theorem systemInitial_sim : ClassSimRel authority layout systemInitial before := by
  apply classSimRel_of_simRel (simRel_initial systemInitial_valid rfl before)
  intro view member
  cases member

def mmuCall : SystemCallOk authority systemInitial 0 systemNames.Mmu ghost renamedGhost 10 11 :=
  ⟨by decide, rfl, rfl, initial_owned⟩

def maskCall : SystemCallOk authority systemInitial 1 systemNames.IrqDelivery ghost renamedGhost 10 11 :=
  ⟨by decide, rfl, rfl, initial_owned⟩

def regime : Uebersetzung.Regime := ⟨1, by decide, 1, by decide, 0⟩

def pagePermissions : Uebersetzung.Perm := ⟨true, true, false⟩

def pageTables : Uebersetzung.Tables :=
  fun root index => if root = 1 ∧ index = 0 then .leaf 7 pagePermissions else .absent

def observedTranslation : Nat → Nat → Option (Nat × Uebersetzung.Perm) :=
  Uebersetzung.walk regime pageTables

theorem mmuHardware : Mmu regime pageTables observedTranslation := fun _ _ => rfl

def namedMmu : NamedMmu systemNames 0 regime pageTables observedTranslation :=
  ⟨⟨rfl, rfl⟩, rfl, mmuHardware⟩

def rootChecked : MmuInstallOk systemInitial [0, 1] 1 true true := by decide

def switched : SystemContext D := (mmuInstallStep systemInitial [0, 1] 1 true true rootChecked before).1

/-- The software predicates are concrete, and jointly true, rather than an
    uninhabited implication about all syntax. Hardware walking is named apart. -/
def rootDuty : MmuInstallDuty true true
    (1 ∈ ([0, 1] : List Nat))
    (observedTranslation 1 0 = Uebersetzung.walk regime pageTables 1 0) :=
  ⟨fun _ => by decide, fun _ => mmuHardware 1 0⟩

def handlerTable : HandlerTable := fun core vector =>
  if core = 0 ∧ vector = 128 then some (5, 1) else
    if core = 0 ∧ vector = 129 then some (6, 3) else none

def irqFrame : Eingang.EntryFrame := Eingang.zeigeRahmen

def userInitial : SystemContext D :=
  { systemInitial with privilege := { systemInitial.privilege with priv := .nutzer } }

def irqChecked : IrqEnterOk userInitial irqFrame handlerTable 128 5 1 := by decide

def entered : SystemContext D := (irqEnterStep userInitial irqFrame handlerTable 128 5 1 irqChecked before).1

/-- An actual single arrival on the configured core/vector/handler. Other
    tuples are absent; the named premise checks mask and priority as well. -/
def delivered (core vector handler priority : Nat) (boundary : Bool) : Prop :=
  core = 0 ∧ vector = 128 ∧ handler = 5 ∧ priority = 1 ∧ boundary = true

theorem irqHardware : IrqDelivery handlerTable userInitial.interrupt delivered := by
  intro core vector handler priority boundary arrival
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := arrival
  exact ⟨rfl, rfl, rfl, by decide, by decide⟩

def entryDuty : IrqEntryDuty systemNames 1 userInitial irqFrame handlerTable 128 5 1 delivered :=
  { origin := ⟨rfl, rfl⟩
    named := rfl
    declaration := ⟨Eingang.zeigeEingang, Eingang.zeigeRahmen, Eingang.zeigeRahmenOk, rfl, rfl⟩
    checked := irqChecked
    hardware := irqHardware
    arrival := ⟨rfl, rfl, rfl, rfl, rfl⟩ }

def irqReturnFrame : Eingang.EntryFrame :=
  { irqFrame with art := .irqReturn, privVor := .kern, privNach := .nutzer, maskiertBeimEintritt := false }

def exitChecked : IrqExitOk entered irqReturnFrame false [] 0 [] := by decide

def returnDuty : IrqReturnDuty userInitial entered irqReturnFrame false [] 0 [] :=
  ⟨exitChecked, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The contract's root has real privilege, mask and memory realization
    obligations; no boot software is hidden in FirmwareEntry. -/
def systemBoot : BootContract D Arch.ArchState Maske.PrioMaske :=
  { «entry» := fun a c => c.privilege.priv = .kern ∧ c.privilege.wurzel = 0 ∧ a.Realizes layout
    transition := fun a _ a' c' => c'.privilege.priv = .nutzer ∧ c'.privilege.maske = false ∧
      c'.views = [] ∧ a'.spans = a.spans
    root := fun a c => c.privilege.priv = .nutzer ∧ c.privilege.maske = false ∧
      c.views = [] ∧ a.Realizes layout }

theorem systemBoot_logic : BootObligation systemBoot := by
  intro a c nextAuthority nextContext firmware transition
  refine ⟨transition.1, transition.2.1, transition.2.2.1, ?_⟩
  intro span member
  rw [transition.2.2.2] at member
  exact firmware.2.2 span member

def systemFirmware : NamedFirmwareEntry systemNames 2 systemBoot authority systemInitial :=
  { origin := ⟨rfl, rfl⟩
    named := rfl
    firmware :=
      { contract := ⟨rfl, rfl, layout_realizes⟩
        valid := systemInitial_valid
        initial := rfl
        unspent := rfl
        owned := initial_owned
        noViews := rfl } }

def systemHandoff : HandoffResult authority systemInitial :=
  { into := OwnerWitness.child
    privilege := { systemInitial.privilege with priv := .nutzer }
    interrupt := systemInterrupt
    owners := owners.withLedger OwnerWitness.movedLedger
    token := { token with handle := ⟨0, 0, 1⟩ }
    quiescent := rfl
    moved := rfl }

def bootDeclaration : Parser.SEingang := { Eingang.zeigeEingang with vektor := none }

theorem bootChecked : BootEntryOk systemInitial bootDeclaration := by
  refine ⟨?_, rfl, rfl⟩
  have accepted := entryChecks_of_frameOf Eingang.zeigeRahmenOk
  simpa only [Eingang.alleOk, bootDeclaration, Eingang.zeigeEingang, Eingang.hatBeide,
    Eingang.artAus, Eingang.stapelOk, Eingang.brauchtStapel] using accepted

theorem systemHandoff_contract :
    systemBoot.transition authority systemInitial systemHandoff.authority systemHandoff.next :=
  ⟨rfl, rfl, rfl, rfl⟩

end Gabbro.Grammatik.LowLevel.Construct.Witness
