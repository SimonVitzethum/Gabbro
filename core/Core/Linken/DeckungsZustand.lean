module

public import Core.Linken.Abgeschottet

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- The acting frame of a context after its position is moved back by the length of the
    preceding code. Only the program counter changes; all temporaries, locals, continuations and
    function table stay as they were. This is the frame-level content of entry relocation. -/
def frameZurueck (off : Nat) (r : Rahmen) : Rahmen := { r with pc := r.pc - off }

/-- A state seen by a module: only the acting context's position is shifted back by the
    concatenation offset. Guard operands are read from the frame, so they survive the shift. -/
def zustandImModul (off : Nat) (c : Kontext) (s : Zustand) : Zustand :=
  { s with lokal := Function.update s.lokal c (frameZurueck off (s.lokal c)) }

/-- The guard use a unit records at a state, without a run: a context poised at an instruction
    whose guard reports the operation and operands. This is exactly the state-level content of
    `kanonischeVerwendung`; keeping it separate makes the run-surgery premise explicit. -/
def zustandsBedarf [DecidableEq L] (p : Fragment) (s : Zustand) (op : PartielleOperation)
    (args : Operanden op) : Prop :=
  ∃ c b, kopf p.code s c = some b ∧ b.guard (s.lokal c) = some ⟨op, args⟩

/-- The canonical guard use at a cut is the state-level guard use at that cut's state. -/
theorem bedarf_ist_zustandsBedarf [DecidableEq L] (p : Fragment) (platform : Plattform)
    (ρ : I.Lauf (p.einheit platform)) (t : I.Schnitt _ ρ) (op : PartielleOperation)
    (args : Operanden op) :
    (kanonischeVerwendung (p.einheit platform)).bedarf ρ t op args ↔
      zustandsBedarf p (ρ.zeit.zustand t.val) op args := by
  rfl

/-- A head in the first fragment is the head of the concatenation whenever the position is
    strictly inside the first fragment. -/
theorem kopf_anhaengen_vorne [DecidableEq L] (a b : Fragment) (s : Zustand) (c : Kontext)
    (h : (s.lokal c).pc < a.code.length) :
    kopf (a.anhaengen b).code s c = kopf a.code s c := by
  unfold kopf
  cases hstatus : s.status c with
  | ruht => rfl
  | beendet _ => rfl
  | laeuft =>
    cases hr : (s.lokal c).rueckgabe with
    | none =>
      by_cases hs : (s.lokal c).stopp.isNone
      · simp only [hs, ↓reduceIte]
        change (a.code ++ b.code)[(s.lokal c).pc]? = a.code[(s.lokal c).pc]?
        exact List.getElem?_append_left _ _ h
      · simp only [hs, ↓reduceIte]
    | some _ => rfl

/-- A head past the first fragment is a head of the second fragment at the relocated position.
    The projected state has the acting frame's position shifted back by the first fragment's
    length; status, temporaries and continuations are unchanged. -/
theorem kopf_anhaengen_hinten [DecidableEq L] (a b : Fragment) (s : Zustand) (c : Kontext)
    (cmd : Befehl) (h : a.code.length ≤ (s.lokal c).pc)
    (head : kopf (a.anhaengen b).code s c = some cmd) :
    kopf b.code (zustandImModul a.code.length c s) c = some cmd := by
  unfold kopf at head ⊢
  cases hstatus : s.status c with
  | ruht => simp only [hstatus] at head; cases head
  | beendet _ => simp only [hstatus] at head; cases head
  | laeuft =>
    cases hr : (s.lokal c).rueckgabe with
    | none =>
      by_cases hs : (s.lokal c).stopp.isNone
      · simp only [hs, ↓reduceIte] at head
        change (a.code ++ b.code)[(s.lokal c).pc]? = some cmd at head
        rw [List.getElem?_append_right _ _ h] at head
        simp only [zustandImModul, frameZurueck, Function.update_self, hstatus, hr, hs,
          ↓reduceIte]
        exact head
      · simp only [hs, ↓reduceIte] at head
        cases head
    | some _ => simp only [hr] at head; cases head

/-- Shifting the acting position back leaves the guard operands of every instruction unchanged:
    guards read the frame's temporaries, never its program counter. -/
theorem guard_zustandImModul [DecidableEq L] (off : Nat) (c : Kontext) (s : Zustand)
    (b : Befehl) (op : PartielleOperation) (args : Operanden op)
    (g : b.guard (s.lokal c) = some ⟨op, args⟩) :
    b.guard ((zustandImModul off c s).lokal c) = some ⟨op, args⟩ := by
  simpa only [zustandImModul, frameZurueck, Function.update_self] using g

/-- A guard use of a concatenation belongs either to the first fragment at the same state, or to
    the second fragment at the state whose acting position is relocated back. This is the
    state-level coverage step: it produces a state of a module's unit, not yet a run reaching it. -/
theorem zustandsBedarf_anhaengen [DecidableEq L] (a b : Fragment) (s : Zustand)
    (op : PartielleOperation) (args : Operanden op)
    (need : zustandsBedarf (a.anhaengen b) s op args) :
    zustandsBedarf a s op args ∨ ∃ s' : Zustand, zustandsBedarf b s' op args := by
  rcases need with ⟨c, cmd, head, g⟩
  by_cases h : (s.lokal c).pc < a.code.length
  · left
    refine ⟨c, cmd, ?_, g⟩
    rw [kopf_anhaengen_vorne a b s c h] at head
    exact head
  · right
    have hle : a.code.length ≤ (s.lokal c).pc := Nat.le_of_not_gt h
    refine ⟨zustandImModul a.code.length c s, c, cmd, ?_, ?_⟩
    · exact kopf_anhaengen_hinten a b s c cmd hle head
    · exact guard_zustandImModul a.code.length c s cmd op args g

/-- Folding modules by concatenation: the accumulator's code is the prefix and the remaining
    modules are appended after it. -/
def verknuepfteAb (ms : List Modul) (acc : Fragment) : Fragment :=
  ms.foldl (fun a m => a.anhaengen m.fragment) acc

/-- The accumulator cannot carry a guard use: its code is empty. -/
theorem kopf_leer [DecidableEq L] (s : Zustand) (c : Kontext) :
    kopf Fragment.leer.code s c = none := by
  simp only [Fragment.leer, kopf, List.getElem?_nil]

/-- Iterating the two-fragment split over a module list attributes a state-level guard use of the
    accumulated code either to the accumulator or to one of the modules, with a state local to
    that module. -/
theorem zustandsBedarf_foldl [DecidableEq L] (ms : List Modul) (acc : Fragment) (s : Zustand)
    (op : PartielleOperation) (args : Operanden op)
    (need : zustandsBedarf (verknuepfteAb ms acc) s op args) :
    zustandsBedarf acc s op args ∨
      ∃ m ∈ ms, ∃ s' : Zustand, zustandsBedarf m.fragment s' op args := by
  induction ms generalizing acc s with
  | nil => exact Or.inl need
  | cons m rest ih =>
    change zustandsBedarf (verknuepfteAb rest (acc.anhaengen m.fragment)) s op args at need
    rcases ih (acc.anhaengen m.fragment) s need with hacc | hrest
    · rcases zustandsBedarf_anhaengen acc m.fragment s op args hacc with hacc' | hm
      · exact Or.inl hacc'
      · rcases hm with ⟨s', needm⟩
        exact Or.inr ⟨m, List.mem_cons_self, s', needm⟩
    · rcases hrest with ⟨m', hm', s', needm'⟩
      exact Or.inr ⟨m', List.mem_cons_of_mem _ hm', s', needm'⟩

/-- Every state-level guard use of a linked fragment is a state-level guard use of one of its
    modules. This is the whole state-level coverage: the only step left to run-level coverage is
    the construction of a maximal run of that module reaching the resulting state. -/
theorem zustandsBedarf_hat_modul [DecidableEq L] (plan : Bauplan) (s : Zustand)
    (op : PartielleOperation) (args : Operanden op)
    (need : zustandsBedarf (verknuepfteFragmente plan) s op args) :
    ∃ m ∈ plan.module, ∃ s' : Zustand, zustandsBedarf m.fragment s' op args := by
  have h := zustandsBedarf_foldl plan.module Fragment.leer s op args need
  rcases h with hacc | hmods
  · rcases hacc with ⟨c, b, head, _⟩
    rw [kopf_leer s c] at head
    cases head
  · exact hmods

end Gabbro.Core.Linken
