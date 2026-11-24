/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Zugriff.lean
  Subject:   THE AUTHORITY AN INSTRUCTION NEEDS BEFORE ITS STEP TOUCHES SHARED STATE (MK-03). A form that
             accesses a cell or asks the outside world has a precondition on the machine state: the handle it
             holds, the cell inside the handle's allocation, the right on the ledger. The classes with such a
             step check this precondition inside their own rule and REFUSE (halt the frame, touch nothing)
             when it fails, exactly as `bindeRegion` refuses a region it was not granted. The step that is
             taken therefore never needs more authority than the state gives (`RegelLokal`), and the form
             never hangs on a refused access (`RegelFortschritt`); whether a program may reach a refusal is
             the checker's question.
-/
module

public import Core.Ast.Semantik.Runtime.Frame
public import Core.Maschine.Buchung
public import Core.Sicherheit.Rennen

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog
open Gabbro.Core.Sicherheit (Speicherrecht)

/-- **The handle a context holds for a location.** A context holds the handle of the region slot it
    lists among its arrival regions, issued in generation `0`; lock words and the event location are no
    region and are never reached through a handle. -/
def Zustand.griff (s : Zustand) (c : Kontext) : Zelle → Option Griff
  | .region slot _offset => if slot < (s.lokal c).arrivalRegions.length then some ⟨slot, 0⟩ else none
  | .sperre _lock => none
  | .aussen => none

/-- **The context may access the cell with the right**: its handle is valid, the object is owned (not
    lent out), the cell lies inside the allocation, and the ledger gives the context the right. This is
    `Annahme.BefugtOrt` of the unit that reads memory through `Zustand.griff` and `Zelle.objekt`
    (`Schrittform.befugt_ort`). -/
def Zustand.befugt (s : Zustand) (c : Kontext) (z : Zelle) (recht : Speicherrecht) : Prop :=
  ∃ (g : Griff) (offset : Nat),
    s.griff c z = some g ∧ g.objekt = z.objekt ∧ s.rechte.Gueltig g ∧ (s.leihen g.objekt).Zugriff ∧
    (s.buchung.umfang g.objekt)[offset]? = some z ∧ s.buchung.haelt c g recht

open Classical in
/-- **The address a context books for an access of a cell**: the handle it holds for the cell and the offset of
    the cell in the allocation, chosen from what the ledger shows. `none` when the context holds no such
    address (the access is then refused before this is used). -/
noncomputable def Zustand.adresse (s : Zustand) (c : Kontext) (z : Zelle) : Option Gabbro.Core.Sicherheit.Adresse :=
  if h : ∃ a : Gabbro.Core.Sicherheit.Adresse, s.griff c z = some a.griff ∧
      (s.buchung.umfang a.griff.objekt)[a.offset]? = some z then
    some (Classical.choose h)
  else none

open Classical in
/-- **The event number of the first access a step makes to a cell**: the access follows the events already in
    the graph, and one lazily materialised initial write comes first when the cell has no write yet
    (`Initialisierung`). The ledger indexes the concrete address of an access by this number. -/
noncomputable def Zustand.zugriffsereignis (s : Zustand) (z : Zelle) : Nat :=
  s.graph.ev.length + (if HatQuelle s.graph z then 0 else 1)

/-- **The context holds every handle and right its question names.** This is `AussengriffeEigen`. -/
def Zustand.aussenBefugt (s : Zustand) (c : Kontext) (q : Frage) : Prop :=
  ∀ z ∈ q.zugriffe, s.buchung.aussengriff c z.handle z.right

/-- **The context may ask the question**: it holds the handles and rights the question names and, for a
    register access, the exclusive authority of the device (`RegisterErlaubt`). -/
def Zustand.fragenBefugt (s : Zustand) (c : Kontext) (q : Frage) : Prop :=
  s.aussenBefugt c q ∧ Gabbro.Core.Sicherheit.RegisterErlaubt s c.nummer q

end Gabbro.Core.Ast.Semantik
