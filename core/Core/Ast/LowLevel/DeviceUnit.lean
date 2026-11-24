module

public import Core.Ast.LowLevel.DeviceSyntax
public import Core.Ast.LowLevel.Execution

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel.Device

open Katalog Maschine

abbrev Unit := Maschine.Einheit PUnit Nat UInt8 PUnit Frame PUnit PUnit PUnit PUnit

def boot (core : Option Nat) : Startdaten UInt8 PUnit Frame PUnit :=
  ⟨fun _ => {}, fun c => if c = entryContext then .laeuft else .ruht,
    fun n => ⟨if some n = core then some entryContext else none, .nutzer, (),
      fun _ => false, 0, false, []⟩, ⟨fun _ => false, fun _ => 0⟩⟩

def setup : Einrichtung PUnit Nat UInt8 PUnit Frame PUnit PUnit :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ _ => False, fun _ _ => True,
    ⟨0, 0⟩, ⟨entryContext, 0, fun _ => boot (some 0), fun _ _ => 0⟩,
    fun _ => 0, fun _ _ _ => none⟩

/-- The unit supplied by elaboration uses the catalogue-selected rule and the
    fixed register-machine invariant. -/
def unit (k : Katalog) (rule : Regel State Plan PUnit) : Unit where
  katalog := k
  bild := image
  einrichtung := setup
  system := ⟨fun _ => rule,
    fun s c => if s.status c = .laeuft then some () else none,
    fun s c => s.status c ≠ .laeuft, fun _ _ _ => False⟩
  startdaten := fun start => boot (start.assignment 0)
  startmedium := medium
  laden := fun start load =>
    if load.starts 0 = some 0 ∧ load.bytes 0 = some 0 then
      let d := boot (start.assignment 0)
      some (Zustand.start d.lokal d.status d.kerne d.rechte setup.initial (.leer (medium start)))
    else none
  lokalerBezug := Eq
  stotterLaenge := fun _ => 0
  quelltabellen := ⟨.leer, fun _ _ _ => False⟩

def Denotation.unit (locals : Ast.Umgebung scope) (d : Denotation k scope) : Unit :=
  unit k (d.rule locals)

def registerSafetyUnit (binding : Binding k) (access : RegisterAccess) :
    Sicherheit.Einheit PUnit Nat UInt8 PUnit Frame PUnit PUnit PUnit PUnit :=
  ⟨unit k (registerRule binding access), []⟩

end Gabbro.Core.Ast.LowLevel.Device
