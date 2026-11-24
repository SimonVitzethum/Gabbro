/-
  File:      core/Core/Maschine/Kontext.lean
  Subject:   CONTEXTS AND CORES (PERFECT-MODEL §3.4, step M4): the contexts that step -- threads, interrupt
             handlers and NMI handlers, each bound to a core -- and the per-core state both machines carry
             from the start: the running context, the privilege level, the active address space, the
             interrupt mask, the NMI state and the stack of preempted contexts. Preemption by an interrupt is
             allowed exactly when its vector is unmasked and no NMI runs; an NMI preempts unless an NMI
             runs; a return resumes exactly the preempted context (`zurueck_unterbrechen`).
-/
module

public import Mathlib.Data.Nat.Pairing

@[expose] public section

namespace Gabbro.Core.Maschine

/-- A core. -/
abbrev Kern := Nat

/-- **A context**: a thread, an interrupt handler for a vector on a core, or the NMI handler of a
    core. -/
inductive Kontext where
  | faden (n : Nat)
  | handler (kern : Kern) (vektor : Nat)
  | nmi (kern : Kern)
  deriving DecidableEq, Repr

/-- The context identity at the catalogue boundary. -/
def Kontext.nummer : Kontext → Nat
  | .faden n => Nat.pair 0 n
  | .handler k v => Nat.pair 1 (Nat.pair k v)
  | .nmi k => Nat.pair 2 k

theorem Kontext.nummer_injektiv : Function.Injective Kontext.nummer := by
  intro c d h
  cases c <;> cases d <;> simp only [Kontext.nummer, Nat.pair_eq_pair] at h <;>
    rcases h with ⟨tag, args⟩ <;> cases tag
  all_goals first | (cases args <;> rfl) | (rcases args with ⟨rfl, rfl⟩; rfl)

/-- **A privilege level**: user, system (kernel), hypervisor. Which of them a core has is a
    catalogue row's statement. -/
inductive Stufe where
  | nutzer
  | system
  | hyper
  deriving DecidableEq, Repr

/-- **The state of one core**: the running context (`none`: idle), its privilege level, the active
    address space, the mask (`true`: the vector is masked), whether an NMI runs, and the stack of
    preempted contexts with their NMI state. -/
structure KernZustand (Raum : Type) where
  laeuft : Option Kontext
  stufe : Stufe
  raum : Raum
  maske : Nat → Bool
  nmiAktiv : Bool
  stapel : List (Option Kontext × Bool)

namespace KernZustand

variable {Raum : Type}

/-- An interrupt with vector `v` may preempt: the vector is unmasked and no NMI runs. -/
def NimmtAn (z : KernZustand Raum) (v : Nat) : Prop := z.maske v = false ∧ z.nmiAktiv = false

/-- An NMI may preempt unless an NMI runs. -/
def NimmtNmiAn (z : KernZustand Raum) : Prop := z.nmiAktiv = false

/-- Preemption by the handler `h`: the running context and the NMI state go onto the stack. -/
def unterbrechen (z : KernZustand Raum) (h : Kontext) (nmi : Bool) : KernZustand Raum :=
  { z with laeuft := some h, nmiAktiv := nmi || z.nmiAktiv,
           stapel := (z.laeuft, z.nmiAktiv) :: z.stapel }

/-- Return from a handler: the preempted context and its NMI state come back. -/
def zurueck (z : KernZustand Raum) : KernZustand Raum :=
  match z.stapel with
  | [] => { z with laeuft := none }
  | (c, n) :: r => { z with laeuft := c, nmiAktiv := n, stapel := r }

/-- **A return resumes exactly the preempted context**, its NMI state and its stack. -/
theorem zurueck_unterbrechen (z : KernZustand Raum) (h : Kontext) (nmi : Bool) :
    (z.unterbrechen h nmi).zurueck.laeuft = z.laeuft ∧
      (z.unterbrechen h nmi).zurueck.nmiAktiv = z.nmiAktiv ∧
      (z.unterbrechen h nmi).zurueck.stapel = z.stapel ∧
      (z.unterbrechen h nmi).zurueck.maske = z.maske :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- While an NMI runs, no interrupt and no further NMI is taken. -/
theorem nmi_sperrt (z : KernZustand Raum) (h : Kontext) (v : Nat) :
    ¬ (z.unterbrechen h true).NimmtAn v ∧ ¬ (z.unterbrechen h true).NimmtNmiAn := by
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have h2 := hn.2
    simp only [unterbrechen, Bool.true_or, Bool.true_eq_false] at h2
  · simp only [NimmtNmiAn, unterbrechen, Bool.true_or, Bool.true_eq_false] at hn

/-- A masked vector is never taken. -/
theorem maskiert_nicht (z : KernZustand Raum) {v : Nat} (h : z.maske v = true) : ¬ z.NimmtAn v :=
  fun hn => by rw [hn.1] at h; exact Bool.false_ne_true h

end KernZustand

end Gabbro.Core.Maschine
