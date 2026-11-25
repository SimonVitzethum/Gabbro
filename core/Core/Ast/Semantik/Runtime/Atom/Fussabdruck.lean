/-
  File:      core/Core/Ast/Semantik/Runtime/Atom/Fussabdruck.lean
  Subject:   THE WRITE FOOTPRINT OF THE ACCESS INSTRUCTIONS (MK-04b, for MK-19). The declared unit invariants
             (`Praedikat`, MK-19) observe cells of the unit's memory and are preserved by an instruction that
             cannot write one of them. A source form that elaborates to an access instruction can write: a store,
             a publication and an atomic update write ONE cell of a region, and which cell is a RUNTIME value
             (the index slot of the frame). The footprint is therefore a static over-approximation, a predicate on
             cells and not a list: the instruction may write every cell of the region it names
             (`Zugriffsform.schreibtMoeglich`), and nothing else; a load and the confirming observation write
             nothing.
             The footprint is sound against the step the instruction takes (`Zugriffsform.plan_schreibt`): every
             cell a plan of the instruction writes (`Plan.schreibtZelle`: a footprint cell written by the plan, or
             the cell of an update label) is in the footprint, for every frame and every value read. The class of
             a plan that writes is a writing class (`Wirkungsklasse.plan_schreibt`): a private step, a load, a lock
             action, a question and a lifecycle step write no cell of the shared memory.
-/
module

public import Core.Ast.Semantik.Runtime.Atom.Form
public import Core.Ast.Semantik.Runtime.Klasse.Schritt

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine
open Gabbro.Core.Speicher (Art)

/-- **A cell lies where an access of the region can land**: a cell of the region, or the outside location, to which
    an access whose index is no non-negative integer is directed (`Rahmen.zelle`) and which no context holds a
    handle for. -/
def Zelle.imRegion (region : Nat) : Zelle → Bool
  | .region slot _ => slot == region
  | .sperre _ => false
  | .aussen => true

/-- **Every cell a write plan writes**: a cell named in the footprint of the plan that the plan marks as written, or the
    cell of an update (a read-modify-write label writes the cell it reads). -/
def Plan.schreibtZelle (p : Plan) (x : Zelle) : Prop :=
  (x ∈ p.fuss ∧ p.schreibt x = true) ∨ ∃ l ∈ p.lesen, l.art = Art.rmw ∧ l.ort = x

/-- The region number an access instruction names. -/
def Zugriffsform.region : Zugriffsform → Nat
  | .lade (region := r) .. => r
  | .speichere (region := r) .. => r
  | .tausche (region := r) .. => r
  | .vergleicheTausche (region := r) .. => r
  | .holeUndAddiere (region := r) .. => r
  | .erwarte (region := r) .. => r
  | .veroeffentliche (region := r) .. => r

/-- Does the class write a cell of the shared memory? A store and an update do. -/
def Wirkungsklasse.schreibend : Wirkungsklasse → Bool
  | .schreiben _ => true
  | .rmw _ => true
  | .lokal => false
  | .ruf => false
  | .lesen _ => false
  | .sperre _ => false
  | .frage => false
  | .starte => false
  | .beende => false
  | .verbinde => false
  | .wechsle => false

/-- **The write footprint of an access instruction.** The instruction may write the cell `x` only when its class
    writes and `x` is a cell of the region it names. The index is a runtime value of the frame, so the footprint is
    the whole region; the checker's rule for an invariant that observes a cell of the region refuses the write. -/
def Zugriffsform.schreibtMoeglich (z : Zugriffsform) (x : Zelle) : Bool :=
  z.klasse.schreibend && x.imRegion z.region

/-- The cell a frame names in a region lies where an access of the region can land. -/
theorem Rahmen.zelle_imRegion (r : Rahmen) (region index : Nat) :
    (r.zelle region index).imRegion region = true := by
  unfold Rahmen.zelle
  split
  · split
    · simp only [Zelle.imRegion, beq_self_eq_true]
    · rfl
  · rfl

/-- The operand of an access names a cell where an access of its region can land. -/
theorem Rahmen.zugriffOperand_ort (r : Rahmen) (region index : Nat) (wert : Option Int) (a : Aenderung) :
    (r.zugriffOperand region index wert a).ort.imRegion region = true := by
  cases wert with
  | some w => exact r.zelle_imRegion region index
  | none => rfl

/-- **The operand of an access instruction names a cell of its region** (or the outside location). -/
theorem Zugriffsform.operand_ort (z : Zugriffsform) (r : Rahmen) :
    (z.operand r).ort.imRegion z.region = true := by
  cases z with
  | vergleicheTausche ziel region index erwartet neu typ modus =>
    simp only [Zugriffsform.operand, Zugriffsform.region]
    split
    · exact r.zugriffOperand_ort region index _ _
    · exact r.zugriffOperand_ort region index _ _
  | lade ziel region index typ modus => exact r.zugriffOperand_ort region index _ _
  | speichere region index quelle modus => exact r.zugriffOperand_ort region index _ _
  | tausche ziel region index quelle typ modus => exact r.zugriffOperand_ort region index _ _
  | holeUndAddiere ziel region index betrag typ modus => exact r.zugriffOperand_ort region index _ _
  | erwarte ziel region index erwartet typ modus => exact r.zugriffOperand_ort region index _ _
  | veroeffentliche region index quelle modus => exact r.zugriffOperand_ort region index _ _

/-- The plan of a question names no footprint and records no label. -/
theorem Operand.fragePlan_ohne_schreiben (o : Operand) : o.fragePlan.fuss = [] ∧ o.fragePlan.lesen = [] := by
  unfold Operand.fragePlan
  split <;> exact ⟨rfl, rfl⟩

/-- **A plan that writes comes from a writing class and writes the cell its operand names.** -/
theorem Wirkungsklasse.plan_schreibt (k : Wirkungsklasse) (o : Operand) (v : Int) (x : Zelle)
    (h : (k.plan o v).schreibtZelle x) : k.schreibend = true ∧ x = o.ort := by
  cases k with
  | lokal =>
    rcases h with ⟨mem, _⟩ | ⟨l, mem, _⟩ <;> exact absurd mem (List.not_mem_nil)
  | ruf =>
    rcases h with ⟨mem, _⟩ | ⟨l, mem, _⟩ <;> exact absurd mem (List.not_mem_nil)
  | lesen m =>
    rcases h with ⟨mem, _⟩ | ⟨l, mem, hart, _⟩
    · exact absurd mem (List.not_mem_nil)
    · have same : l = ⟨.lesen, o.ort, m, v, v⟩ := List.mem_singleton.mp mem
      subst same
      exact absurd hart (by intro e; cases e)
  | schreiben m =>
    rcases h with ⟨mem, _⟩ | ⟨l, mem, _⟩
    · exact ⟨rfl, List.mem_singleton.mp mem⟩
    · exact absurd mem (List.not_mem_nil)
  | rmw m =>
    rcases h with ⟨mem, _⟩ | ⟨l, mem, hart, hort⟩
    · exact absurd mem (List.not_mem_nil)
    · have same : l = ⟨o.aenderung.art v, o.ort, m, v, o.aenderung.schreibt v o.wert⟩ := List.mem_singleton.mp mem
      subst same
      exact ⟨rfl, hort.symm⟩
  | sperre a =>
    rcases h with ⟨mem, _⟩ | ⟨l, mem, _⟩ <;> exact absurd mem (List.not_mem_nil)
  | frage =>
    rcases h with ⟨mem, _⟩ | ⟨l, mem, _⟩
    · have e : (Wirkungsklasse.frage.plan o v).fuss = [] := (Operand.fragePlan_ohne_schreiben o).1
      rw [e] at mem
      exact absurd mem List.not_mem_nil
    · have e : (Wirkungsklasse.frage.plan o v).lesen = [] := (Operand.fragePlan_ohne_schreiben o).2
      rw [e] at mem
      exact absurd mem List.not_mem_nil
  | starte =>
    rcases h with ⟨mem, _⟩ | ⟨l, mem, _⟩ <;> exact absurd mem (List.not_mem_nil)
  | beende =>
    rcases h with ⟨mem, _⟩ | ⟨l, mem, _⟩ <;> exact absurd mem (List.not_mem_nil)
  | verbinde =>
    rcases h with ⟨mem, _⟩ | ⟨l, mem, _⟩ <;> exact absurd mem (List.not_mem_nil)
  | wechsle =>
    rcases h with ⟨mem, _⟩ | ⟨l, mem, _⟩ <;> exact absurd mem (List.not_mem_nil)

/-- **The footprint is sound against the step of an access instruction (`fussabdruck_treu` of the access forms).**
    Every cell a plan of the instruction writes, at every frame and for every value the memory model returned, is in the
    footprint. -/
theorem Zugriffsform.plan_schreibt (z : Zugriffsform) (r : Rahmen) (v : Int) (x : Zelle)
    (h : (z.klasse.plan (z.operand r) v).schreibtZelle x) : z.schreibtMoeglich x = true := by
  obtain ⟨writes, same⟩ := z.klasse.plan_schreibt _ _ _ h
  unfold Zugriffsform.schreibtMoeglich
  rw [writes, same]
  exact z.operand_ort r

/-- **A load and the confirming observation have an empty footprint.** -/
theorem Zugriffsform.lesend_schreibt_nichts (z : Zugriffsform) (h : z.klasse.schreibend = false) (x : Zelle) :
    z.schreibtMoeglich x = false := by
  unfold Zugriffsform.schreibtMoeglich
  rw [h]
  rfl

/-- **A store, a publication and an update include the region they name** (the footprint is not empty): every cell of
    the region of a writing instruction is in its footprint. -/
theorem Zugriffsform.schreibend_schreibt_region (z : Zugriffsform) (h : z.klasse.schreibend = true) (slot offset : Nat)
    (hr : slot = z.region) : z.schreibtMoeglich (.region slot offset) = true := by
  unfold Zugriffsform.schreibtMoeglich
  rw [h]
  subst hr
  simp only [Zelle.imRegion, beq_self_eq_true, Bool.and_self]

/-- **The write footprint of an instruction (MK-19): the shared cells it may write.** Every instruction but an access
    instruction is frame-only or a lifecycle instruction and writes none; an access instruction writes the cells of the
    region it names (`Zugriffsform.schreibtMoeglich`). The checker refuses the preservation of a declared invariant for
    an observed cell in the footprint (`pruefeBefehlErhalt`). A new instruction must be listed: there is no wildcard. -/
def Befehl.schreibtMoeglich : Befehl → Zelle → Bool
  | .zugriff form, x => form.schreibtMoeglich x
  | .faden _, _ => false
  | .rufe .., _ | .starte .., _ => false
  | .literal .., _ | .binaer .., _ | .wahrheitswert .., _ | .lesen .., _ | .negativ .., _ => false
  | .negieren .., _ | .verneinen .., _ | .teilen .., _ | .vergleichen .., _ => false
  | .binden .., _ | .springeWenn .., _ | .zuweisen .., _ | .zurueck .., _ | .springe .., _ => false
  | .blockEnde .., _ | .bindeWert .., _ | .ende, _ | .bindeRegion .., _ => false
  | .definiere .., _ | .rueckVoid, _ | .pruefeMass .., _ | .setzePasszahl .., _ => false
  | .whileTest .., _ | .forAnfang .., _ | .forTest .., _ | .forNaechster .., _ | .zurueckSprung .., _ => false
  | .baueArray .., _ | .liesArray .., _ | .baueTupel .., _ | .liesTupelfeld .., _ | .bindeTupel .., _ => false
  | .definiereRecord .., _ | .baueRecord .., _ | .liesRecordFeld .., _ | .setzeRecordFeld .., _ => false
  | .definiereVariante .., _ | .baueVariante .., _ | .waehleVariante .., _ => false
  | .definiereTraeger .., _ | .optionIstBesetzt .., _ | .definiereEffektgruppe .., _
  | .waehleUmgebung .., _ => false
  | .textLiteral .., _ | .textConcat .., _ | .textIndex .., _ | .substring .., _ | .textLength .., _ => false

/-- **A writing class belongs to an access instruction**: every instruction of a class that writes the shared memory is
    an access instruction. -/
theorem Befehl.schreibend_zugriff (b : Befehl) (h : b.klasse.schreibend = true) : ∃ z, b = .zugriff z := by
  cases b with
  | zugriff z => exact ⟨z, rfl⟩
  | faden z =>
    cases z <;> cases h
  | _ => cases h

/-- **The footprint of an instruction is sound against its step.** Every cell a plan of the instruction writes, for every
    frame and every value the memory model returned, is in its footprint: a frame-only instruction and a lifecycle
    instruction write none, an access instruction writes inside the region it names. -/
theorem Befehl.plan_schreibt_fussabdruck (b : Befehl) (r : Rahmen) (v : Int) (x : Zelle)
    (h : (b.klasse.plan (b.operand r) v).schreibtZelle x) : b.schreibtMoeglich x = true := by
  obtain ⟨writes, _⟩ := b.klasse.plan_schreibt _ _ _ h
  obtain ⟨z, same⟩ := b.schreibend_zugriff writes
  subst same
  exact z.plan_schreibt r v x h

end Gabbro.Core.Ast.Semantik
