/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Form.lean
  Subject:   THE INSTRUCTIONS THAT ACCESS SHARED MEMORY (MK-04). One instruction of the machine reads, writes or
             updates ONE cell of a region in an access mode (`na`, `rlx`, `ra`, `sc`). The forms are the
             instruction side of the source forms of the memory model:
             * `lade` / `speichere`: a load and a store in a mode;
             * `tausche`, `vergleicheTausche`, `holeUndAddiere`: an atomic update (exchange, compare-and-swap,
               fetch-and-add) -- ONE event that reads and writes (RC11's `U`); a failed compare-and-swap is a
               read (`Aenderung.art`);
             * `erwarte`: the CONFIRMING acquire observation of `A awaits { p, q }` -- an acquire load of the flag
               cell that advances only when it observes the published marker, otherwise it observes again;
             * `veroeffentliche`: the release publication of `A = e publishes { p, q }` -- a store of the flag
               cell. The payload `{ p, q }` is the set of cells written before it in program order; which cells
               are declared is the checker's rule (SG-13), the machine carries no list.
             The mode is a field of the instruction, NOT a constant of the carrier: the model must be able to
             represent the instruction with a mode that is too weak for its purpose (a relaxed publication), so
             that the checker's refusal of it is a refusal of something real (`PayloadSichtbarNichtTrivialAussage`).
             THERE IS NO FENCE FORM. The memory model W is fence-free (`Core/Speicher/Basis.lean`: "fences are
             added together with a fence form"); a `zaun` instruction without a fence rule in W would be an
             accepted form the model lacks. It is refused until W has its fence events (finding for the owner:
             `Art.zaun` at the end of `Art`, the fence clauses of `sw` and `psc`).
-/
module

public import Core.Ast.Semantik.Runtime.Frame
public import Core.Ast.Aggregate.Runtime
public import Core.Speicher.Basis

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Gabbro.Core.Speicher (Modus Art)

/-- **How an atomic update computes the value it writes** from the value it read and the instruction's operand:
    `tausche` writes the operand, `addiere` writes the sum, `vergleiche e` writes the operand when the value read
    is `e` and nothing otherwise (the compare-and-swap that fails). -/
inductive Aenderung where
  | tausche
  | addiere
  | vergleiche (erwartet : Int)

/-- The value an update with this change writes, given the value read and the operand. -/
def Aenderung.schreibt : Aenderung → Int → Int → Int
  | .tausche, _gelesen, neu => neu
  | .addiere, gelesen, betrag => gelesen + betrag
  | .vergleiche erwartet, gelesen, neu => if gelesen = erwartet then neu else gelesen

/-- **The kind of the event an update records**: an update, except a compare-and-swap that fails, which only
    reads (RC11: a failed compare-and-swap is a load). -/
def Aenderung.art : Aenderung → Int → Art
  | .tausche, _gelesen => .rmw
  | .addiere, _gelesen => .rmw
  | .vergleiche erwartet, gelesen => if gelesen = erwartet then .rmw else .lesen

/-- **The instructions that access shared memory.** The cell is the `index`-th cell of the region with the
    number `region`; `index`, `quelle`, `betrag`, `erwartet` (as a slot) and `neu` name temporaries of the frame;
    `ziel` is the temporary that receives the value read, at the type `typ`. -/
inductive Zugriffsform where
  | lade (ziel region index : Nat) (typ : Ty .value) (modus : Modus)
  | speichere (region index quelle : Nat) (modus : Modus)
  | tausche (ziel region index quelle : Nat) (typ : Ty .value) (modus : Modus)
  | vergleicheTausche (ziel region index erwartet neu : Nat) (typ : Ty .value) (modus : Modus)
  | holeUndAddiere (ziel region index betrag : Nat) (typ : Ty .value) (modus : Modus)
  | erwarte (ziel region index : Nat) (erwartet : Int) (typ : Ty .value) (modus : Modus)
  | veroeffentliche (region index quelle : Nat) (modus : Modus)

/-- The integer a temporary slot of the frame holds. -/
def Rahmen.ganz (r : Rahmen) (slot : Nat) : Option Int :=
  (r.zahl slot).map fun n => n.zahl.wert

/-- **The cell a region and an index slot name.** A slot that holds no non-negative integer names no cell of any
    region: the location of the outside events, to which no context holds a handle, so the access is refused. -/
def Rahmen.zelle (r : Rahmen) (region index : Nat) : Zelle :=
  match r.ganz index with
  | some i => if 0 ≤ i then .region region i.toNat else .aussen
  | none => .aussen

/-- **The frame after the instruction has bound the value read**: the value is bound at its type; a value the
    type does not contain (a cell that holds something else than the declared type admits) halts the frame. -/
def Rahmen.bindeGelesen (r : Rahmen) (ziel : Nat) (typ : Ty .value) (gelesen : Int) : Rahmen :=
  match wertIn typ ⟨.int gelesen gelesen, Zahl.literal gelesen⟩ with
  | some wert => r.schreibe ziel (some wert)
  | none => r.halt .ungueltigerWert

/-- The frame after an instruction that binds nothing: the next instruction. -/
def Rahmen.weiter (r : Rahmen) : Rahmen := { r with pc := r.pc + 1 }

/-- **The frame transfer of an access instruction**, given the value `gelesen` the memory model returned for the
    read part of its step (every store ignores it). The confirming observation `erwarte` advances only when it
    observed the marker; otherwise the frame is unchanged and the instruction observes again. -/
def Zugriffsform.uebertrag (z : Zugriffsform) (r : Rahmen) (gelesen : Int) : Rahmen :=
  match z with
  | .lade ziel _ _ typ _ => r.bindeGelesen ziel typ gelesen
  | .speichere .. => r.weiter
  | .tausche ziel _ _ _ typ _ => r.bindeGelesen ziel typ gelesen
  | .vergleicheTausche ziel _ _ _ _ typ _ => r.bindeGelesen ziel typ gelesen
  | .holeUndAddiere ziel _ _ _ typ _ => r.bindeGelesen ziel typ gelesen
  | .erwarte ziel _ _ erwartet typ _ => if gelesen = erwartet then r.bindeGelesen ziel typ gelesen else r
  | .veroeffentliche .. => r.weiter

/-- Binding the value read changes only the program counter, the temporaries or the stop reason of the frame: the
    stack and the loop counters stay, and the program counter never moves back. -/
theorem Rahmen.bindeGelesen_lokal (r : Rahmen) (ziel : Nat) (typ : Ty .value) (gelesen : Int) :
    (r.bindeGelesen ziel typ gelesen).fortsetzungen = r.fortsetzungen ∧
      r.pc ≤ (r.bindeGelesen ziel typ gelesen).pc ∧
      (r.bindeGelesen ziel typ gelesen).zaehler = r.zaehler := by
  unfold Rahmen.bindeGelesen
  split
  · exact ⟨rfl, Nat.le_succ _, rfl⟩
  · exact ⟨rfl, Nat.le_refl _, rfl⟩

/-- **The frame transfer of an access instruction keeps the stack and the loop counters and never moves the program
    counter back.** -/
theorem Zugriffsform.uebertrag_lokal (z : Zugriffsform) (r : Rahmen) (gelesen : Int) :
    (z.uebertrag r gelesen).fortsetzungen = r.fortsetzungen ∧ r.pc ≤ (z.uebertrag r gelesen).pc ∧
      (z.uebertrag r gelesen).zaehler = r.zaehler := by
  cases z with
  | erwarte ziel region index erwartet typ modus =>
    simp only [Zugriffsform.uebertrag]
    split
    · exact r.bindeGelesen_lokal _ _ _
    · exact ⟨rfl, Nat.le_refl _, rfl⟩
  | speichere _ _ _ _ => exact ⟨rfl, Nat.le_succ _, rfl⟩
  | veroeffentliche _ _ _ _ => exact ⟨rfl, Nat.le_succ _, rfl⟩
  | lade _ _ _ _ _ => exact r.bindeGelesen_lokal _ _ _
  | tausche _ _ _ _ _ _ => exact r.bindeGelesen_lokal _ _ _
  | vergleicheTausche _ _ _ _ _ _ _ => exact r.bindeGelesen_lokal _ _ _
  | holeUndAddiere _ _ _ _ _ _ => exact r.bindeGelesen_lokal _ _ _

/-- **The frame transfer of an access instruction keeps the arrival regions of the frame**: the grant of the acting
    context never changes quietly. -/
theorem Zugriffsform.uebertrag_arrival (z : Zugriffsform) (r : Rahmen) (gelesen : Int) :
    (z.uebertrag r gelesen).arrivalRegions = r.arrivalRegions := by
  have gebunden (ziel : Nat) (typ : Ty .value) :
      (r.bindeGelesen ziel typ gelesen).arrivalRegions = r.arrivalRegions := by
    unfold Rahmen.bindeGelesen
    split <;> rfl
  cases z with
  | erwarte ziel region index erwartet typ modus =>
    simp only [Zugriffsform.uebertrag]
    split
    · exact gebunden ziel typ
    · rfl
  | speichere _ _ _ _ => rfl
  | veroeffentliche _ _ _ _ => rfl
  | lade ziel _ _ typ _ => exact gebunden ziel typ
  | tausche ziel _ _ _ typ _ => exact gebunden ziel typ
  | vergleicheTausche ziel _ _ _ _ typ _ => exact gebunden ziel typ
  | holeUndAddiere ziel _ _ _ typ _ => exact gebunden ziel typ

end Gabbro.Core.Ast.Semantik
