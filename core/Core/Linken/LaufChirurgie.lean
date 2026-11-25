module

public import Core.Linken.DeckungsSchluss

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- A guard use at a state, tied to the acting context `c`. Keeping the context explicit makes the
    projection of a context step through `zustandImModul` a statement about the same frame. -/
def zustandsBedarfBei (p : Fragment) (c : Kontext) (s : Zustand)
    (op : PartielleOperation) (args : Operanden op) : Prop :=
  ∃ b, kopf p.code s c = some b ∧ b.guard (s.lokal c) = some ⟨op, args⟩

/-- The acting frame's head and guard survive a frame-only step of another context. The step
    touches only the local state of `c'`; with `c' ≠ c` the frame of `c` is unchanged. -/
theorem zustandsBedarfBei_nach_anderer (p : Fragment) (c c' : Kontext) (b : Befehl)
    (s : Zustand) (hne : c' ≠ c) (op : PartielleOperation) (args : Operanden op)
    (need : zustandsBedarfBei p c s op args) :
    zustandsBedarfBei p c (b.nach c' s) op args := by
  rcases need with ⟨cmd, head, guard⟩
  refine ⟨cmd, ?_, ?_⟩
  · unfold kopf at head ⊢
    rw [Befehl.nach_lokal_anderer b hne s]
    rw [show (b.nach c' s).status c = s.status c from rfl]
    exact head
  · rw [Befehl.nach_lokal_anderer b hne s]
    exact guard

/-- Projection of a whole state onto a module commutes with a frame-only step of a context other
    than the projected one. The two local updates are at distinct keys and commute; the acting
    frame of `c` in the stepped state is the original one because `c' ≠ c`. This is the
    context-step projection lemma for steps outside the acting module context. -/
theorem zustandImModul_nach_anderer (off : Nat) (c c' : Kontext) (b : Befehl)
    (s : Zustand) (hne : c' ≠ c) :
    zustandImModul off c (b.nach c' s) = b.nach c' (zustandImModul off c s) := by
  simp only [zustandImModul, Befehl.nach, frameZurueck, Zustand.regionLive,
    Function.update_of_ne hne, Function.update_comm hne]

/-- The acting frame's head and guard survive the projection and a frame-only step of another
    context: the step commutes with `zustandImModul`, and the projected frame of `c` is the one the
    guard already held at. -/
theorem zustandsBedarfBei_projiziert_nach_anderer (p : Fragment) (off : Nat)
    (c c' : Kontext) (b : Befehl) (s : Zustand) (hne : c' ≠ c)
    (op : PartielleOperation) (args : Operanden op)
    (need : zustandsBedarfBei p c (zustandImModul off c s) op args) :
    zustandsBedarfBei p c (zustandImModul off c (b.nach c' s)) op args := by
  rw [zustandImModul_nach_anderer off c c' b s hne]
  exact zustandsBedarfBei_nach_anderer p c c' b (zustandImModul off c s) hne op args need

/-- From any state, a maximal ideal-style timeline exists for an arbitrary step relation: the
    canonical timeline pauses exactly when no step exists. This supplies the maximality half of
    run surgery once a start state has been fixed. -/
theorem Zeitlauf.existiert_maximal {S Ev : Type} (schritt : Nat → S → Ev → S → Prop) (s : S) :
    ∃ ρ : Zeitlauf schritt, ρ.zustand 0 = s ∧ ρ.Maximal (fun _ => True) := by
  obtain ⟨ρ, h0⟩ := Zeitlauf.existiert schritt s
  refine ⟨ρ, h0, ?_, ?_⟩
  · intro t _idle _frei
    exact (ρ.wartet _idle).2
  · intro _endlich
    exact ⟨0, fun _ _ => trivial⟩

/-- Linker acceptance for frame-only code follows from uniform guard validity of the parts. The
    state-level coverage of `DeckungsZustand` attributes every guard use of the whole to a state
    of some module; the uniform premise discharges that state's guard without needing a run of the
    module to reach it. The gap to the pinned statement is exactly that uniform guard validity is
    stronger than per-module acceptance. -/
theorem linker_akzeptiert_aus_guardsUeberall (plan : Bauplan) (frag : Fragment)
    (hlink : linke plan = some frag)
    (hpriv : ∀ b ∈ (verknuepfteFragmente plan).code, b.Privat)
    (hparts : ∀ m ∈ plan.module, Akzeptiert (m.fragment.einheit plan.plattform))
    (hguards : ∀ m ∈ plan.module, ∀ (s : Zustand) (op : PartielleOperation) (args : Operanden op),
      zustandsBedarf m.fragment s op args → waechterBedarf op args) :
    Akzeptiert (frag.einheit plan.plattform) := by
  apply linker_akzeptiert_aus_guard_transfer plan frag hlink hparts hpriv
  intro ρ hρ t op args need
  obtain ⟨_hok, hfrag⟩ := linke_eq_some hlink
  subst frag
  rw [bedarf_ist_zustandsBedarf] at need
  obtain ⟨m, hm, s', needm⟩ :=
    zustandsBedarf_hat_modul plan (ρ.zeit.zustand t.val) op args need
  exact hguards m hm s' op args needm

end Gabbro.Core.Linken
