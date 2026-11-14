/- The small wait interface used by safety: a binding step either leaves the
   lock state alone or performs one existing ticket-machine step. Fairness is
   deliberately separate from this interface. -/
module
public import Stage0.Senke.Sperre.Faeden.Fifo
public import Stage0.Senke.Sperre.Faeden.Karte
public import Stage0.Senke.Sperre.Faeden.GeistLauf
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden
open Gabbro.Code (Conf)
open Gabbro.Code.Lower (Tkt)
variable {N : Nat}

/-- Places reachable without registering a sleeper. This excludes every
    waiter-counter, futex and wake-all place of the hosted binding. -/
def Ort.spin : Ort → Prop
  | .frei | .ladeN | .casN _ | .ladeS _ | .drin _ | .gibL _ | .gibC _ _ | .gibW => True
  | _ => False

def SpinState (σ : Zustand N) : Prop := ∀ t, (σ.pc t).spin

/-- The existing machine for Linux; for spin, its common steps between spin
    states and a failed serving read that retries without registering a waiter. -/
def BindingStep (strategy : LockWait) (σ : Zustand N) (t : Fin N) (σ' : Zustand N) : Prop :=
  match strategy with
  | .futex => Schritt σ t σ'
  | .spin =>
      (Schritt σ t σ' ∧ SpinState σ ∧ SpinState σ') ∨
      (∃ k, σ.pc t = .ladeS k ∧
        σ.w.serv % 18446744073709551616 ≠ k % 18446744073709551616 ∧ σ' = σ)

/-- This is the entire interface needed by invariant, FIFO and ghost proofs.
    Implementations may stutter but cannot alter ticket draws, entry or release. -/
structure WaitModel (N : Nat) where
  step : Zustand N → Fin N → Zustand N → Prop
  refines : ∀ {σ t σ'}, step σ t σ' → σ' = σ ∨ Schritt σ t σ'

/-- Both concrete bindings satisfy the same interface, without a kernel or
    fairness assumption. The spin case cannot reach a blocking place. -/
def waitModel (strategy : LockWait) : WaitModel N where
  step := BindingStep strategy
  refines := by
    intro σ t σ' h
    cases strategy with
    | futex => exact Or.inr h
    | spin =>
      rcases h with ⟨step, _, _⟩ | ⟨_, _, _, same⟩
      · exact Or.inr step
      · exact Or.inl same

/-- A run over an arbitrary binding satisfying the small safety interface. -/
structure WaitRun (M : WaitModel N) where
  z : Nat → Zustand N
  akt : Nat → Option (Fin N)
  step : ∀ n t, akt n = some t → M.step (z n) t (z (n + 1))
  stutter : ∀ n, akt n = none → z (n + 1) = z n

variable {M : WaitModel N}

/-- The same cross-thread invariant for every wait binding. -/
theorem WaitRun.inv (R : WaitRun M) (hN : N ≤ 2147483647) (h0 : Inv N (R.z 0)) :
    ∀ n, Inv N (R.z n)
  | 0 => h0
  | n + 1 => by
    cases ha : R.akt n with
    | none => rw [R.stutter n ha]; exact R.inv hN h0 n
    | some t =>
      rcases M.refines (R.step n t ha) with same | step
      · rw [same]; exact R.inv hN h0 n
      · exact (R.inv hN h0 n).schritt hN step

/-- The same simulation statement: a scheduled binding step is an abstract
    stutter or one ticket-lock step of that very thread. -/
theorem WaitRun.abbild (R : WaitRun M) (hN : N ≤ 2147483647) (h0 : Inv N (R.z 0)) (n : Nat) :
    (R.akt n = none ∧ bild (R.z (n + 1)) = bild (R.z n)) ∨
      ∃ t, R.akt n = some t ∧ Opt (AbsSchritt t) (bild (R.z n)) (bild (R.z (n + 1))) := by
  cases ha : R.akt n with
  | none => exact Or.inl ⟨rfl, by rw [R.stutter n ha]⟩
  | some t =>
    refine Or.inr ⟨t, rfl, ?_⟩
    rcases M.refines (R.step n t ha) with same | step
    · exact Or.inl (by rw [same])
    · exact step.abbild hN (R.inv hN h0 n)

/-- The source of the ghost is independent of the binding, at access granularity.
    A window/coupling to machine G is still the existing, separate obligation. -/
def WaitRun.abstract (R : WaitRun M) (hN : N ≤ 2147483647) (h0 : Inv N (R.z 0)) :
    AbsLauf (fun n => (R.akt n).map Fin.val) (fun n => (bild (R.z n)).karte Fin.val) where
  ok0 := (bild_ok h0).karte fin_val_inj
  schritt := by
    intro n u hu
    rcases R.abbild hN h0 n with ⟨ha, same⟩ | ⟨t, ha, step⟩
    · simp only [ha, Option.map_none] at hu; cases hu
    · rw [ha] at hu
      cases hu
      exact (Opt.karte fin_val_inj (fun _ _ h => h.karte fin_val_inj) step).weg
  stotter := by
    intro n hn
    cases ha : R.akt n with
    | none => rw [R.stutter n ha]
    | some t => simp only [ha, Option.map_some] at hn; cases hn

/-- Every binding carries the model's same ticket ghost, with exactly the
    existing word-width bound. No per-program translation validation is used. -/
theorem WaitRun.tkt [Conf] (R : WaitRun M) (hN : N ≤ 2147483647) (h0 : Inv N (R.z 0))
    (bound : ∀ n, (bild (R.z n)).queue.length + 2 < 2 ^ Conf.wbits) :
    ∃ gh : Nat → Tkt, (∀ n, Passt (gh n) ((bild (R.z n)).karte Fin.val)) ∧
      ∀ n, Nach ((R.akt n).map Fin.val) (gh n) (gh (n + 1)) := by
  apply (R.abstract hN h0).tkt
  intro n
  simpa only [Abs.karte, List.length_map] using bound n

/-- Mutual exclusion has the identical invariant and bound for both bindings. -/
theorem WaitRun.ausschluss (R : WaitRun M) (hN : N ≤ 2147483647) (h0 : Inv N (R.z 0))
    (n : Nat) {t u : Fin N} (ht : ((R.z n).pc t).haelt = true)
    (hu : ((R.z n).pc u).haelt = true) : t = u :=
  (R.inv hN h0 n).ausschluss ht hu

end Gabbro.Stage0.Senke.Faeden
