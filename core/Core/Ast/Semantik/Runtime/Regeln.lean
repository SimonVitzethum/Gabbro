module

public import Core.Ast.Semantik.Runtime.Klasse.Schritt
public import Core.Ast.Semantik.Runtime.Atom.Fussabdruck
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

/-- **A frame-only instruction**: it has a frame-only class (`lokal`, `ruf` or one of the
    interrupt-control classes of MK-20). Since MK-04 an instruction can have an
    access class, so a generic proof over all instructions splits on the class: the frame-only part is stated
    for the instructions that satisfy this predicate, the access part is the duty of its class
    (`Klasse/Pflichten`) or a pinned statement of the access instructions (`Atom/Aussagen`). -/
def Befehl.Privat (b : Befehl) : Prop :=
  b.klasse = .lokal ∨ b.klasse = .ruf ∨ b.klasse = .maskiere ∨ b.klasse = .prioritaet ∨
    b.klasse = .sendeUnterbrechung ∨ b.klasse = .leiteLeitung

/-- **Every instruction that is no access, lifecycle or interrupt-control instruction is frame-only.** -/
theorem Befehl.privat_von_kein_zugriff {b : Befehl} (h : ∀ form, b ≠ .zugriff form)
    (h' : ∀ form, b ≠ .faden form) (h'' : ∀ form, b ≠ .aussen form) : b.Privat := by
  cases b <;> first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    | exact absurd rfl (h _)
    | exact absurd rfl (h' _)
    | exact absurd rfl (h'' _)

/-- **The plan of a frame-only instruction does not read the frame**: its operand is an immediate
    (or empty), so two frames give the same plan. Access instructions read the frame. -/
theorem Befehl.plan_privat_unabhaengig (b : Befehl) (h : b.Privat) (r₁ r₂ : Rahmen) (v : Int) :
    b.plan r₁ v = b.plan r₂ v := by
  cases b with
  | zugriff form =>
    cases form <;> simp only [Befehl.klasse, Befehl.Privat, Zugriffsform.klasse, reduceCtorEq, or_false, or_true, false_or, true_or] at h
  | faden form =>
    cases form <;> simp only [Befehl.klasse, Befehl.Privat, Fadenform.klasse, reduceCtorEq, or_false, or_true, false_or, true_or] at h
  | aussen form =>
    cases form <;> simp only [Befehl.klasse, Befehl.Privat, AussenfrageformKlasse, reduceCtorEq, or_false, or_true, false_or, true_or] at h
  | _ => rfl

/-- A frame-only instruction transfers its frame by its evaluation at the instruction boundary, whatever the
    memory returned. -/
theorem Befehl.uebertrag_privat (b : Befehl) (h : b.Privat) (r : Rahmen) (live : Nat → Bool) (v : Int) :
    b.uebertrag r live v = b.auswerten r live := by
  cases b with
  | zugriff form => rcases h with h | h | h | h | h | h <;> cases form <;> cases h
  | faden form => rcases h with h | h | h | h | h | h <;> cases form <;> cases h
  | _ => rfl

/-- **The state after the step of a frame-only form**: the transfer of the form is the evaluation of the
    instruction (`Befehl.nach`). -/
theorem Befehl.nach_form (b : Befehl) (h : b.Privat) (c : Kontext) (s : Zustand) (v : Int) :
    b.form.nach c s v = b.nach c s := by
  unfold Schrittform.nach Befehl.nach
  show { s with lokal := Function.update s.lokal c (b.uebertrag (s.lokal c) s.regionLive v) } =
    { s with lokal := Function.update s.lokal c (b.auswerten (s.lokal c) s.regionLive) }
  rw [b.uebertrag_privat h]

/-- The plan of a frame-only instruction records no memory event and has no footprint. -/
theorem Befehl.plan_privat_leer (b : Befehl) (h : b.Privat) (r : Rahmen) :
    (b.plan r 0).lesen = [] ∧ (b.plan r 0).fuss = [] := by
  rcases h with h | h | h | h | h | h <;>
    simp only [Befehl.plan, Befehl.form, Schrittform.plan, h, Wirkungsklasse.plan, planMit,
      Semantik.plan] <;>
    trivial

/-- The protocol action of a frame-only instruction: the internal action or one interrupt-control action. -/
theorem Befehl.plan_privat_aktion (b : Befehl) (h : b.Privat) (r : Rahmen) :
    (b.plan r 0).aktion = .intern ∨
    (∃ vektor aus, (b.plan r 0).aktion = .maskiere vektor aus) ∨
    (∃ grenze, (b.plan r 0).aktion = .prioritaet grenze) ∨
    (∃ vektor kern, (b.plan r 0).aktion = .sende vektor kern) ∨
    (∃ ltg krn prio, (b.plan r 0).aktion = .leite ltg krn prio) := by
  rcases h with h | h | h | h | h | h
  · have e : (b.plan r 0).aktion = .intern := by
      unfold Befehl.plan Befehl.form Schrittform.plan
      rw [h]
      rfl
    exact Or.inl e
  · have e : (b.plan r 0).aktion = .intern := by
      unfold Befehl.plan Befehl.form Schrittform.plan
      rw [h]
      rfl
    exact Or.inl e
  · have e : (b.plan r 0).aktion =
        .maskiere (b.operand r).unterbrechung.vektor (b.operand r).unterbrechung.aus := by
      unfold Befehl.plan Befehl.form Schrittform.plan
      rw [h]
      rfl
    exact Or.inr (Or.inl ⟨_, _, e⟩)
  · have e : (b.plan r 0).aktion = .prioritaet (b.operand r).unterbrechung.grenze := by
      unfold Befehl.plan Befehl.form Schrittform.plan
      rw [h]
      rfl
    exact Or.inr (Or.inr (Or.inl ⟨_, e⟩))
  · have e : (b.plan r 0).aktion =
        .sende (b.operand r).unterbrechung.vektor (b.operand r).unterbrechung.kern := by
      unfold Befehl.plan Befehl.form Schrittform.plan
      rw [h]
      rfl
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, e⟩)))
  · have e : (b.plan r 0).aktion =
        .leite (b.operand r).unterbrechung.leitung (b.operand r).unterbrechung.kern
          (b.operand r).unterbrechung.prioritaet := by
      unfold Befehl.plan Befehl.form Schrittform.plan
      rw [h]
      rfl
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, e⟩)))

/-- A frame-only plan is still and empty: its action, reads and footprint. -/
theorem Befehl.privat_still_leer (b : Befehl) (h : b.Privat) (r : Rahmen) :
    (b.plan r 0).aktion.Still ∧ (b.plan r 0).lesen = [] ∧ (b.plan r 0).fuss = [] := by
  obtain ⟨hlesen, hfuss⟩ := b.plan_privat_leer h r
  refine ⟨?_, hlesen, hfuss⟩
  rcases b.plan_privat_aktion h r with h0 | ⟨_, _, h0⟩ | ⟨_, h0⟩ | ⟨_, _, h0⟩ | ⟨_, _, _, h0⟩ <;>
    rw [h0] <;> trivial

/-- The machine post-state of a frame-only step: the form state, plus the machine effect of the plan's
    protocol action (mask, threshold, send, route). Non-still actions are vacuous; only still plans
    reach this function. -/
def Befehl.maschinennach (b : Befehl) (c : Kontext) (s u : Zustand) : Zustand :=
  match (b.plan (s.lokal c) 0).aktion with
  | .intern => u
  | .maskiere vektor aus =>
    { u with kerne := fun k =>
      if _ : (s.kerne k).laeuft = some c then
        { u.kerne k with maske := Function.update (u.kerne k).maske vektor aus }
      else u.kerne k }
  | .prioritaet grenze =>
    { u with kerne := fun k =>
      if _ : (s.kerne k).laeuft = some c then { u.kerne k with untergrenze := grenze }
      else u.kerne k }
  | .sende vektor kern => { u with software := u.software ++ [(kern, .maskierbar vektor 0)] }
  | .leite leitung kern prio =>
    { u with leitung := Function.update u.leitung leitung (kern, prio) }
  | .warte _ | .sperre _ _ | .frage _ | .verbrauche _ | .rueckkehr | .starte | .verbinde _ |
    .beende | .wechsle _ _ => u

/-- **The machine transfer of a local or call step is the frame transfer**: its plan carries the
    internal action, so the machine state is unchanged. -/
theorem Befehl.maschinennach_lokal_ruf (b : Befehl) (h : b.klasse = .lokal ∨ b.klasse = .ruf)
    (c : Kontext) (s u : Zustand) : b.maschinennach c s u = u := by
  unfold Befehl.maschinennach
  rcases h with h | h <;>
    simp only [Befehl.plan, Schrittform.plan, Befehl.form, Wirkungsklasse.plan, h,
      Semantik.plan]

/-- The ideal step of a form of a frame-only class: the plan of its class and its frame transfer. -/
theorem Schrittform.ideal_privat (F : Schrittform)
    (h : F.klasse = .lokal ∨ F.klasse = .ruf ∨ F.klasse = .maskiere ∨ F.klasse = .prioritaet ∨
      F.klasse = .sendeUnterbrechung ∨ F.klasse = .leiteLeitung)
    (c : Kontext) (s : Zustand) (w : PUnit.{1}) (plans : List Plan) (u : Zustand) :
    F.ideal c s w plans u ↔ plans = [F.plan (s.lokal c) 0] ∧ u = F.nach c s 0 := by
  obtain ⟨k, o, t⟩ := F
  rcases h with h | h | h | h | h | h
  · change k = .lokal at h
    subst h
    exact Iff.rfl
  · change k = .ruf at h
    subst h
    exact Iff.rfl
  · change k = .maskiere at h
    subst h
    exact Iff.rfl
  · change k = .prioritaet at h
    subst h
    exact Iff.rfl
  · change k = .sendeUnterbrechung at h
    subst h
    exact Iff.rfl
  · change k = .leiteLeitung at h
    subst h
    exact Iff.rfl

/-- **The ideal step of a frame-only instruction**: the plan of its class and the frame transfer
    `Befehl.nach`. This is the unfolded step every proof over a generic instruction of the current set uses. -/
theorem Befehl.ideal_privat (b : Befehl) (h : b.Privat) (c : Kontext) (s : Zustand) (w : PUnit.{1})
    (plans : List Plan) (u : Zustand) :
    b.ideal c s w plans u ↔ plans = [b.plan (s.lokal c) 0] ∧ u = b.nach c s := by
  rw [← b.nach_form h c s 0]
  exact b.form.ideal_privat h c s w plans u

/-- The implementation step of a frame-only instruction is its ideal step. -/
theorem Befehl.impl_privat (b : Befehl) (h : b.Privat) (c : Kontext) (s : Zustand) (w : PUnit.{1})
    (plans : List Plan) (u : Zustand) :
    b.impl c s w plans u ↔ plans = [b.plan (s.lokal c) 0] ∧ u = b.nach c s :=
  b.ideal_privat h c s w plans u

/-- **No instruction issues a question or takes a lock: every step of every instruction is a still action** (the
    internal action, a lifecycle action (MK-07) or an interrupt-control action (MK-20)). A frame-only step
    has the plan of its class; the step of an access instruction has the plan of its class or the private
    plan of its refusal, and the classes `lesen`, `schreiben` and `rmw` plan the internal action; the step
    of a lifecycle instruction plans the action of its class. -/
theorem Befehl.impl_aktion_still (b : Befehl) {c : Kontext} {s : Zustand} {w : PUnit.{1}} {p : Plan}
    {u : Zustand} (h : b.impl c s w [p] u) : p.aktion.Still := by
  by_cases hp : b.Privat
  · have hplan : p = b.plan (s.lokal c) 0 :=
      (List.cons.inj ((b.impl_privat hp c s w [p] u).1 h).1).1
    subst hplan
    rcases b.plan_privat_aktion hp (s.lokal c) with h0 | ⟨_, _, h0⟩ | ⟨_, h0⟩ | ⟨_, _, h0⟩ |
      ⟨_, _, _, h0⟩
    · rw [h0]
      trivial
    · rw [h0]
      trivial
    · rw [h0]
      trivial
    · rw [h0]
      trivial
    · rw [h0]
      trivial
  · cases b with
    | zugriff z =>
      cases z <;> rcases h with ⟨_, same, _⟩ | ⟨_, v, _, same, _⟩ <;>
        (have e := (List.cons.inj same).1
         subst e
         trivial)
    | faden z =>
      cases z <;> rcases h with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;>
        (have e := (List.cons.inj same).1
         subst e
         trivial)
    | aussen form =>
      cases form with
      | frage ziel operation args =>
        simp only [Befehl.impl, Befehl.form, Schrittform.impl, Schrittform.ideal,
          AussenfrageformKlasse, Schrittform.zugriffsschritt, Schrittform.plan,
          Wirkungsklasse.plan, Befehl.operand, Operand.fragePlan] at h
        rcases h with ⟨_, same, _⟩ | ⟨_, _, _, same, _⟩
        · have e := (List.cons.inj same).1
          subst e
          trivial
        · have e := (List.cons.inj same).1
          subst e
          trivial
      | verbrauche ziel =>
        simp only [Befehl.impl, Befehl.form, Schrittform.impl, Schrittform.ideal,
          AussenfrageformKlasse] at h
        have e := (List.cons.inj h.1).1
        subst e
        trivial
    | maskiere _ _ | prioritaet _ | sendeUnterbrechung _ _ | leiteLeitung _ _ _ =>
      exact absurd (Befehl.privat_von_kein_zugriff (fun _ eq => by cases eq) (fun _ eq => by cases eq)
        (fun _ eq => by cases eq)) hp
    | _ => exact absurd (by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)) hp

/-- The same, for a rule that is the rule of the instruction. -/
theorem Befehl.regel_aktion_still (b : Befehl) {R : Regel} (hR : R = b.regel) {c : Kontext} {s : Zustand}
    {w : PUnit.{1}} {p : Plan} {u : Zustand} (h : R.impl c s w [p] u) : p.aktion.Still := by
  subst hR
  exact b.impl_aktion_still (w := w) h

/-- A frame-only instruction is in no access family. -/
theorem Befehl.privat_ne_zugriff_klasse (b : Befehl) (h : b.Privat) (z : Zugriffsform) : b ≠ .zugriff z := by
  rintro rfl
  rcases h with h | h | h | h | h | h <;> cases z <;> cases h

/-- A frame-only instruction is no lifecycle instruction. -/
theorem Befehl.privat_ne_faden_klasse (b : Befehl) (h : b.Privat) (z : Fadenform) : b ≠ .faden z := by
  rintro rfl
  rcases h with h | h | h | h | h | h <;> cases z <;> cases h

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

/-- The frame transfer preserves memory content: it touches only the acting frame. -/
theorem Befehl.nach_initial (b : Befehl) (c : Kontext) (s : Zustand) :
    (b.nach c s).initial = s.initial := rfl

/-- The write footprint is sound against the frame transfer: outside it, memory content is
    unchanged. The frame transfer touches only the acting frame, so this holds for every footprint; the footprint of
    an access instruction is sound against the step it takes (`Befehl.plan_schreibt_fussabdruck`). -/
theorem Befehl.fussabdruck_treu (b : Befehl) (c : Kontext) (s : Zustand) (z : Zelle)
    (_ : b.schreibtMoeglich z = false) : (b.nach c s).initial z = s.initial z :=
  congrFun (b.nach_initial c s) z

/-- Preservation across the frame transfer for predicates whose observed cells the command
    does not write. -/
theorem Praedikat.gilt_nach (q : Praedikat) (b : Befehl) (c : Kontext) (s : Zustand)
    (h : ∀ z ∈ q.beobachtet, b.schreibtMoeglich z = false) : q.gilt s → q.gilt (b.nach c s) := by
  intro hq
  exact q.haelt_stabil _ _ (fun z mem => (b.fussabdruck_treu c s z (h z mem)).symm) hq



def system (code : List Befehl) : LokalSystem :=
  ⟨Befehl.regel, kopf code, fun s c => kopf code s c = none, fun _ _ _ => False⟩

end Gabbro.Core.Ast.Semantik
