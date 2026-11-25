module

public import Core.Ast.Semantik.Runtime.Klasse.Schritt
public import Core.Ast.Semantik.Runtime.Praedikat

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

/-- The context-local transfer of a frame-only instruction: the acting frame is evaluated at the
    instruction boundary, every other field is the machine's. -/
def Befehl.nach (b : Befehl) (c : Kontext) (s : Zustand) : Zustand :=
  { s with lokal := Function.update s.lokal c (b.auswerten (s.lokal c) s.regionLive) }

/-- **The ideal step of an instruction**: the ideal step of its form, which its class builds. -/
def Befehl.ideal (b : Befehl) (c : Kontext) (s : Zustand) (w : PUnit.{1})
    (plans : List Plan) (u : Zustand) : Prop :=
  b.form.ideal c s w plans u

/-- **The implementation step of an instruction**: the implementation step of its form. -/
def Befehl.impl (b : Befehl) (c : Kontext) (s : Zustand) (w : PUnit.{1})
    (plans : List Plan) (u : Zustand) : Prop :=
  b.form.impl c s w plans u

def Befehl.regel (b : Befehl) : Regel := ⟨b.impl, b.ideal⟩

/-- **The plan of the step of an instruction at a frame**, for the value `v` the memory model returned
    for a read. It replaces the one constant plan of every instruction: the plan depends on the acting
    frame (the cell, the value, the lock or the question the frame names) and on the class. -/
def Befehl.plan (b : Befehl) (r : Rahmen) (v : Int) : Plan :=
  b.form.plan r v

/-- **Every instruction of the current set is frame-only**: it has the class `lokal` or `ruf`. This is the
    one place where the generic proofs over all instructions use that no instruction yet has an access
    class. The first instruction of an access class (MK-04, MK-05, MK-06) makes it false, and every generic
    proof that uses it must then split on the class: the model refuses the instruction until that is done. -/
theorem Befehl.klasse_privat (b : Befehl) : b.klasse = .lokal ∨ b.klasse = .ruf := by
  cases b <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The plan of a frame-only instruction is the private plan, at every frame and for every value. -/
theorem Befehl.plan_privat (b : Befehl) (r : Rahmen) (v : Int) : b.plan r v = Semantik.plan := by
  show b.klasse.plan (b.operand r) v = Semantik.plan
  rcases b.klasse_privat with h | h <;> simp only [h, Wirkungsklasse.plan]

/-- The ideal step of a form of a frame-only class: its private plan and its frame transfer. -/
theorem Schrittform.ideal_privat (F : Schrittform) (h : F.klasse = .lokal ∨ F.klasse = .ruf)
    (c : Kontext) (s : Zustand) (w : PUnit.{1}) (plans : List Plan) (u : Zustand) :
    F.ideal c s w plans u ↔ plans = [Semantik.plan] ∧ u = F.nach c s 0 := by
  obtain ⟨k, o, t⟩ := F
  rcases h with h | h
  · change k = .lokal at h
    subst h
    exact Iff.rfl
  · change k = .ruf at h
    subst h
    exact Iff.rfl

/-- **The ideal step of a frame-only instruction**: the private plan and the frame transfer `Befehl.nach`.
    This is the unfolded step every proof over a generic instruction of the current set uses. -/
theorem Befehl.ideal_privat (b : Befehl) (c : Kontext) (s : Zustand) (w : PUnit.{1})
    (plans : List Plan) (u : Zustand) :
    b.ideal c s w plans u ↔ plans = [Semantik.plan] ∧ u = b.nach c s :=
  b.form.ideal_privat b.klasse_privat c s w plans u

/-- The implementation step of a frame-only instruction is its ideal step. -/
theorem Befehl.impl_privat (b : Befehl) (c : Kontext) (s : Zustand) (w : PUnit.{1})
    (plans : List Plan) (u : Zustand) :
    b.impl c s w plans u ↔ plans = [Semantik.plan] ∧ u = b.nach c s :=
  b.ideal_privat c s w plans u

abbrev LokalSystem := MaschinenSystem Nat Zelle Int Nat Rahmen PUnit PUnit PUnit Befehl

/-- The entry context: the boot context whose body starts at the first instruction. -/
def eintritt : Kontext := .faden 0

/-- **The head of any context.** A context that runs, has returned nothing and has not stopped
    executes the instruction at its own position; every other context has no head. The head
    depends on the status and the frame of that context alone. -/
def kopf (code : List Befehl) (s : Zustand) (c : Kontext) : Option Befehl :=
  match s.status c with
  | .ruht => none
  | .laeuft =>
    match (s.lokal c).rueckgabe with
    | none => if (s.lokal c).stopp.isNone then code[(s.lokal c).pc]? else none
    | some _ => none
  | .beendet _ => none

/-- A head comes from the code: the rule at the head is one of the fragment's commands. -/
theorem kopf_mem (code : List Befehl) (s : Zustand) (c : Kontext) (b : Befehl)
    (h : kopf code s c = some b) : b ∈ code := by
  cases hst : s.status c with
  | ruht =>
    simp only [kopf, hst] at h
    cases h
  | laeuft =>
    cases hret : (s.lokal c).rueckgabe with
    | some _ =>
      simp only [kopf, hst, hret] at h
      cases h
    | none =>
      simp only [kopf, hst, hret] at h
      split at h
      · exact List.mem_of_getElem? h
      · cases h
  | beendet _ =>
    simp only [kopf, hst] at h
    cases h

/-- The frame transfer preserves memory content: it touches only the acting frame. -/
theorem Befehl.nach_initial (b : Befehl) (c : Kontext) (s : Zustand) :
    (b.nach c s).initial = s.initial := rfl

/-- The write footprint is sound against the frame transfer: outside it, memory content is
    unchanged. Vacuous today (every footprint is empty); MK-04 proves the conditional from
    the memory rules. -/
theorem Befehl.fussabdruck_treu (b : Befehl) (c : Kontext) (s : Zustand) (z : Zelle)
    (_ : z ∉ b.schreibFussabdruck) : (b.nach c s).initial z = s.initial z :=
  congrFun (b.nach_initial c s) z

/-- Preservation across the frame transfer for predicates whose observed cells the command
    does not write. -/
theorem Praedikat.gilt_nach (q : Praedikat) (b : Befehl) (c : Kontext) (s : Zustand)
    (h : ∀ z ∈ q.beobachtet, z ∉ b.schreibFussabdruck) : q.gilt s → q.gilt (b.nach c s) := by
  intro hq
  exact q.haelt_stabil _ _ (fun z mem => (b.fussabdruck_treu c s z (h z mem)).symm) hq



def system (code : List Befehl) : LokalSystem :=
  ⟨Befehl.regel, kopf code, fun s c => kopf code s c = none, fun _ _ _ => False⟩

end Gabbro.Core.Ast.Semantik
