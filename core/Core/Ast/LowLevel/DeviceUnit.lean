module

public import Core.Ast.LowLevel.DeviceSyntax
public import Core.Ast.LowLevel.Execution

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel.Device

open Katalog Maschine

abbrev Unit := Maschine.Einheit PUnit Nat UInt8 PUnit Frame PUnit PUnit PUnit PUnit

/-- Boot data with the declared device in `ready`: only the declaring entry context
    owns the phase entry, every other object stays undeclared. -/
def bootFor (obj : Objekt) (core : Option Nat) : Startdaten UInt8 PUnit Frame PUnit :=
  ⟨fun c => if c = entryContext then
      { phases := fun o => if o = obj then some .ready else none } else {},
    fun c => if c = entryContext then .laeuft else .ruht,
    fun n => ⟨if some n = core then some entryContext else none, .nutzer, (),
      fun _ => false, 0, false, []⟩, ⟨fun _ => false, fun _ => 0⟩⟩

/-- Start ledger for one declared device: the declaring entry context alone holds
    the free device authority and its handle rights. No authority from nothing:
    every other object maps to `none`, every other handle is refused. -/
def startBuchung (obj : Objekt) (h : Handle) : Gabbro.Core.Sicherheit.Buchung Nat :=
  { Gabbro.Core.Sicherheit.Buchung.leer with
    geraet := fun o => if o = obj then some (entryContext, .frei) else none
    aussengriff := fun c h' right => c = entryContext ∧ h' = h ∧ right ∈ h'.rights }

def boot (core : Option Nat) : Startdaten UInt8 PUnit Frame PUnit :=
  bootFor (⟨.virtio, 0⟩ : Objekt) core

def setup (obj : Objekt := (⟨.virtio, 0⟩ : Objekt)) :
    Einrichtung PUnit Nat UInt8 PUnit Frame PUnit PUnit :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ _ => False, fun _ _ => True,
    ⟨0, 0⟩, ⟨entryContext, 0, fun _ => bootFor obj (some 0), fun _ _ => 0, verwerfen⟩,
    fun _ => 0, fun _ _ _ => none⟩

/-- The unit supplied by elaboration uses the catalogue-selected rule and the
    fixed register-machine invariant. The loader installs exactly the declared
    device authority for the declaring entry context. -/
def unit (k : Katalog) (binding : Binding k) (rule : Regel State Plan PUnit) : Unit where
  katalog := k
  bild := image
  einrichtung := setup binding.object
  system := ⟨fun _ => rule,
    fun s c => match s.status c with | .laeuft => some () | _ => none,
    fun s c => s.status c ≠ .laeuft, fun _ _ _ => False⟩
  startdaten := fun start => bootFor binding.object (start.assignment 0)
  startmedium := medium
  laden := fun start load =>
    if load.starts 0 = some 0 ∧ load.bytes 0 = some 0 then
      let d := bootFor binding.object (start.assignment 0)
      let base := Zustand.start d.lokal d.status d.kerne d.rechte
        (setup binding.object).initial (.leer (medium start))
      some { base with buchung := startBuchung binding.object binding.handle }
    else none
  lokalerBezug := Eq
  stotterLaenge := fun _ => 0
  quelltabellen := ⟨.leer, fun _ _ _ => False⟩

def Denotation.binding : Denotation k scope → Binding k
  | .read _ binding _ => binding
  | .fallibleRead _ binding _ _ _ => binding
  | .write binding _ _ => binding
  | .transition decl => decl.binding

def Denotation.unit (locals : Ast.Umgebung scope) (d : Denotation k scope) : Unit :=
  Gabbro.Core.Ast.LowLevel.Device.unit k d.binding (d.rule locals)

def registerSafetyUnit (binding : Binding k) (access : RegisterAccess) :
    Sicherheit.Einheit PUnit Nat UInt8 PUnit Frame PUnit PUnit PUnit PUnit :=
  ⟨unit k binding (registerRule binding access), []⟩

end Gabbro.Core.Ast.LowLevel.Device
