/-
  File:      core/Core/Ast/Semantik/Runtime/Faden/Form.lean
  Subject:   THE INSTRUCTIONS OF THE THREAD LIFECYCLE (MK-07). One instruction starts a thread, ends one, joins
             one, switches a core to one, or starts a core with one. The forms are the instruction side of the
             exact thread creation of the machine (`Aktion.starte`, `.verbinde`, `.beende`, `.wechsle`):
             * `starte`: start a thread at the code position `eintritt`; the temporary `ziel` receives the number of
               the new thread (the machine picks it: the next free number), and the owned regions the temporaries of
               `uebergabe` hold are HANDED OVER to it: the new thread holds their authority, the starter no more;
             * `beende`: end the acting thread with the integer its temporary `quelle` holds;
             * `verbinde`: join the thread whose number the temporary `kind` holds: it waits until that thread has
               ended, binds its outcome into `ziel` and takes back the authority the ended thread still held;
             * `wechsle`: run the thread named by `kind` on the core named by `kern` (the acting thread's own core:
               a switch);
             * `kernStart`: the same step on an IDLE core (a core start). Its bytes are the generated startup
               sequence of the target binding (K4/O17: no assembler); the model fixes the effect, the target
               table row carries the sequence, and that the hardware behaves like the row is a named assumption.
             A thread is named by an integer in a temporary, as a core is. A temporary that holds no integer names
             nothing: the step is refused and the frame halts, so an instruction never acts on a number it
             defaulted. THERE IS NO RELEASE/ACQUIRE IN THESE STEPS: the happens-before of start and join is the one
             of a publication and an observation of a flag cell (`Atom/Form`: `veroeffentliche`, `erwarte`) in
             program order around them; a start or join without them is an instruction of the model, and the
             checker's refusal of it is what excludes the race (`FadenHbAussage`).
-/
module

public import Core.Ast.Semantik.Runtime.Atom.Form
public import Core.Maschine.Buchung

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

/-- **The instructions of the thread lifecycle.** `typ` is the type of the integer a number or an outcome is bound
    at; `eintritt` is the code position the new thread starts at. -/
inductive Fadenform where
  | starte (ziel eintritt : Nat) (typ : Ty .value) (uebergabe : List Nat)
  | beende (quelle : Nat)
  | verbinde (ziel kind : Nat) (typ : Ty .value)
  | wechsle (kern kind : Nat)
  | kernStart (kern kind : Nat)

/-- The number of the thread a temporary names: the non-negative integer it holds. -/
def Rahmen.fadennr (r : Rahmen) (slot : Nat) : Option Nat :=
  (r.ganz slot).bind fun i => if 0 ≤ i then some i.toNat else none

/-- The handle of the owned region a temporary holds: its object, in the first generation. -/
def Rahmen.regionsgriff (r : Rahmen) (slot : Nat) : Option Griff :=
  ((r.temp slot).bind (wertAls .ownedRegion)).map fun (objekt : Nat) => ⟨objekt, 0⟩

/-- **The entry frame of a new thread**: the position it starts at, no temporaries, no locals, no continuation
    and no loop state; the program's functions, constants and platform are the starter's. -/
def Rahmen.kindRahmen (r : Rahmen) (eintritt : Nat) : Rahmen :=
  { r with pc := eintritt, temp := fun _slot => none, lokale := [], rueckgabe := none, stopp := none,
           zaehler := fun _slot => none, obergrenzen := fun _slot => none, fortsetzungen := [],
           funktion := none, mass := none }

/-- **What a lifecycle step names, read from its frame**: whether every temporary it needs holds what it needs,
    the thread it names, the core it names, the entry frame of a new thread, the handles it hands over and the
    outcome it ends with. A class reads the fields it needs and ignores the others. -/
structure Fadenoperand where
  gueltig : Bool
  kind : Nat
  kern : Nat
  anfang : Rahmen
  griffe : List Griff
  ergebnis : Int

/-- The operand of a step that names no thread (every other class). -/
def Fadenoperand.keiner : Fadenoperand :=
  ⟨true, 0, 0, { pc := 0, temp := fun _slot => none, lokale := [], rueckgabe := none }, [], 0⟩

/-- **The lifecycle operand of an instruction at a frame.** -/
def Fadenform.operand (z : Fadenform) (r : Rahmen) : Fadenoperand :=
  match z with
  | .starte ziel eintritt typ uebergabe =>
    { Fadenoperand.keiner with
      gueltig := uebergabe.all fun slot => (r.regionsgriff slot).isSome,
      anfang := r.kindRahmen eintritt,
      griffe := uebergabe.filterMap r.regionsgriff }
  | .beende quelle =>
    { Fadenoperand.keiner with gueltig := (r.ganz quelle).isSome, ergebnis := (r.ganz quelle).getD 0 }
  | .verbinde ziel kind typ =>
    { Fadenoperand.keiner with gueltig := (r.fadennr kind).isSome, kind := (r.fadennr kind).getD 0 }
  | .wechsle kern kind =>
    { Fadenoperand.keiner with
      gueltig := (r.fadennr kern).isSome && (r.fadennr kind).isSome,
      kern := (r.fadennr kern).getD 0, kind := (r.fadennr kind).getD 0 }
  | .kernStart kern kind =>
    { Fadenoperand.keiner with
      gueltig := (r.fadennr kern).isSome && (r.fadennr kind).isSome,
      kern := (r.fadennr kern).getD 0, kind := (r.fadennr kind).getD 0 }

/-- **The frame transfer of a lifecycle instruction**, given the integer the machine supplies: the number of the
    new thread for `starte`, the outcome of the joined thread for `verbinde`; the other instructions ignore it.
    An ended thread has stopped: its frame no longer has a head. -/
def Fadenform.uebertrag (z : Fadenform) (r : Rahmen) (v : Int) : Rahmen :=
  match z with
  | .starte ziel eintritt typ uebergabe => r.bindeGelesen ziel typ v
  | .beende quelle => { r with stopp := some .fertig }
  | .verbinde ziel kind typ => r.bindeGelesen ziel typ v
  | .wechsle kern kind => r.weiter
  | .kernStart kern kind => r.weiter

/-- The frame transfer of a lifecycle instruction keeps the stack and the loop counters and never moves the
    program counter back. -/
theorem Fadenform.uebertrag_lokal (z : Fadenform) (r : Rahmen) (v : Int) :
    (z.uebertrag r v).fortsetzungen = r.fortsetzungen ∧ r.pc ≤ (z.uebertrag r v).pc ∧
      (z.uebertrag r v).zaehler = r.zaehler := by
  cases z with
  | starte ziel eintritt typ uebergabe => exact r.bindeGelesen_lokal ziel typ v
  | beende quelle => exact ⟨rfl, Nat.le_refl _, rfl⟩
  | verbinde ziel kind typ => exact r.bindeGelesen_lokal ziel typ v
  | wechsle kern kind => exact ⟨rfl, Nat.le_succ _, rfl⟩
  | kernStart kern kind => exact ⟨rfl, Nat.le_succ _, rfl⟩

/-- **The frame transfer of a lifecycle instruction keeps the arrival regions of the frame**: the grant of the acting
    context never changes quietly (a start gives authority through the ledger, not through the frame's list). -/
theorem Fadenform.uebertrag_arrival (z : Fadenform) (r : Rahmen) (v : Int) :
    (z.uebertrag r v).arrivalRegions = r.arrivalRegions := by
  have gebunden (ziel : Nat) (typ : Ty .value) :
      (r.bindeGelesen ziel typ v).arrivalRegions = r.arrivalRegions := by
    unfold Rahmen.bindeGelesen
    split <;> rfl
  cases z with
  | starte ziel eintritt typ uebergabe => exact gebunden ziel typ
  | beende quelle => rfl
  | verbinde ziel kind typ => exact gebunden ziel typ
  | wechsle kern kind => rfl
  | kernStart kern kind => rfl

end Gabbro.Core.Ast.Semantik
