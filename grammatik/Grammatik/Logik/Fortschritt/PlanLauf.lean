/-
  File:      Grammatik/Logik/Fortschritt/PlanLauf.lean
  Subject:   SCHEDULED RUNS OF MACHINE G, DEFINITIONS ONLY (2026-10-22): the infinite runs the liveness statements
             speak about, the ticket lock as a property of the run, and weak fairness. Imported by the goal statement
             (Zielsatz/Kern/Spec.lean, `GabbroZielLeben`); the theorems are in Lebendigkeit.lean and Hungerfrei.lean.

  * `PlanLauf` -- an infinite sequence of machines; each scheduler step is a step of machine G by one thread, or a
    stutter where no thread can step.
  * `FifoLauf` -- a `PlanLauf` with one queue per lock: the threads standing at `locks L` (`glied`), each once
    (`eindeutig`); only the head takes `L` (`kopf`); the threads that stay keep their order ahead of every newcomer
    (`ordnung`). That is the ticket lock of Code/Conc/Lock.lean (`fetch_add` on `next`, spin on `serving`).
  * `Fair` -- weak fairness: a thread that can step at every scheduler step from some point on takes a step.
-/
import Grammatik.Logik.Ruf.Maschine.RufMaschineG
import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Scheduled runs -/

section Lauf

variable (P : Programm D) (O : Orakel D) (passes : Nat)

/-- Thread `t` can step at `M`. -/
def Bereit (M : RufMaschineG D) (t : Faden) : Prop := ∃ M', RufSchrittG P O passes M t M'

/-- **A scheduled run**: an infinite sequence of machines; at every scheduler
    step either thread `u` takes a step of machine G (`akt n = some u`), or the
    machine stutters (`akt n = none`), which is allowed only where no thread
    can step. -/
structure PlanLauf where
  M : Nat → RufMaschineG D
  akt : Nat → Option Faden
  schritt : ∀ n u, akt n = some u → RufSchrittG P O passes (M n) u (M (n + 1))
  stotter : ∀ n, akt n = none → M (n + 1) = M n ∧ ∀ u, ¬ Bereit P O passes (M n) u

end Lauf

/-! ## 2. The ticket lock as a run, and fairness -/

section Lauf

variable (P : Programm D) (O : Orakel D) (passes : Nat)

open Classical in
/-- **A run of the ticket lock**: a scheduled run of machine G with one queue per lock. -/
structure FifoLauf extends PlanLauf P O passes where
  q : Nat → D.Lock → List Faden
  /-- The queue holds exactly the threads standing at `locks L`. -/
  glied : ∀ n L u, u ∈ q n L ↔ AnSperre (M n) u L
  /-- Each once. -/
  eindeutig : ∀ n L, (q n L).Nodup
  /-- **Only the head takes the lock.** -/
  kopf : ∀ n u L, akt n = some u → AnSperre (M n) u L → (q n L).head? = some u
  /-- **First come, first served**: the threads that stay are, in their order, ahead of every newcomer. -/
  ordnung : ∀ n L, (q n L).filter (fun u => decide (u ∈ q (n + 1) L)) <+: q (n + 1) L

/-- **Weak fairness**: a thread that can step at every scheduler step from `n` on takes a step. -/
def Fair (R : PlanLauf P O passes) : Prop :=
  ∀ (t : Faden) (n : Nat), (∀ j, n ≤ j → Bereit P O passes (R.M j) t) → ∃ j, n ≤ j ∧ R.akt j = some t

end Lauf

end Gabbro.Grammatik
