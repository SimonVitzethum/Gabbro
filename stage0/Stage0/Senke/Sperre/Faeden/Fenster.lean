/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Fenster.lean
  Subject:   THE EMITTED LOCK AT THE GRANULARITY OF MACHINE G. A run of the emitted lock (Faeden/Maschine.lean) is
             finer than a run of machine G: the waiter count, FUTEX_WAIT and FUTEX_WAKE, the failed `cas` loops are
             steps of their own. `φ n` names the step of the emitted run at which G's scheduler step `n` begins; the
             WINDOW `[φ n, φ (n + 1))` holds the emitted steps of G's step `n`. `Fenster F φ akt`: in each window at
             most one step changes the abstract lock, and that step is a step of the thread G schedules at `n`
             (`akt`, threads named by number). Then
             * `Lauf.absLauf` -- the emitted lock seen at the window starts (`Lauf.bei`) is a run of the abstract
               lock at G granularity (`AbsLauf`), so the queue facts of `FifoLauf` hold for it;
             * `Lauf.tkt` -- it carries a ghost run of the model's ticket lock `Tkt` (Code/Conc/LockRel.lean), moved
               only by the scheduled thread's `take`/`enter`/`leave` (`Faeden/GeistLauf.lean`);
             * `Fenster.id` -- every run of the emitted lock is such a run for its own scheduler (`φ = id`).
             Premise: at most 2147483647 threads (the WAKE count, and the ticket and low-32 word exactness of
             `Inv`; it also keeps the ghost's `n - s` below `2 ^ wbits`).
-/
module
public import Stage0.Senke.Sperre.Faeden.Karte
public import Stage0.Senke.Sperre.Faeden.GeistLauf
public import Stage0.Senke.Sperre.Faeden.Fifo
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Code (Conf)
open Gabbro.Code.Lower (Tkt)

variable {N : Nat}

/-- The emitted lock at the start of G's step `n`, its threads named by number. -/
def Lauf.bei (F : Lauf N) (φ : Nat → Nat) (n : Nat) : Abs Nat := (bild (F.z (φ n))).karte Fin.val

/-- **The window condition**: the windows follow each other, and in the window of G's step `n` every emitted step
    but at most one (`j`) leaves the abstract lock alone; step `j`, if it lies in the window, is a step of the thread
    G schedules at `n` (or a stutter of both). -/
def Fenster (F : Lauf N) (φ : Nat → Nat) (akt : Nat → Option Nat) : Prop :=
  ∀ n, φ n ≤ φ (n + 1) ∧ ∃ j, (φ n ≤ j → j < φ (n + 1) → (F.akt j).map Fin.val = akt n) ∧
    ∀ i, φ n ≤ i → i < φ (n + 1) → i ≠ j → bild (F.z (i + 1)) = bild (F.z i)

/-- Steps that leave the abstract lock alone leave it alone together. -/
theorem Lauf.bild_stet (F : Lauf N) {i : Nat} : ∀ d,
    (∀ k, i ≤ k → k < i + d → bild (F.z (k + 1)) = bild (F.z k)) → bild (F.z (i + d)) = bild (F.z i)
  | 0, _ => rfl
  | d + 1, h => by
    rw [← Nat.add_assoc, h (i + d) (by omega) (by omega)]
    exact Lauf.bild_stet F d (fun k h1 h2 => h k h1 (by omega))

section

variable (hN : N ≤ 2147483647) (F : Lauf N) (h0 : Inv N (F.z 0))
include hN h0

/-- **One window is a stutter or one abstract step of G's thread.** -/
theorem Lauf.fenster_fall {φ : Nat → Nat} {akt : Nat → Option Nat} (hW : Fenster F φ akt) (n : Nat) :
    bild (F.z (φ (n + 1))) = bild (F.z (φ n)) ∨
      ∃ t : Fin N, akt n = some t.val ∧ Opt (AbsSchritt t) (bild (F.z (φ n))) (bild (F.z (φ (n + 1)))) := by
  obtain ⟨hle, j, hj, hst⟩ := hW n
  by_cases hjw : φ n ≤ j ∧ j < φ (n + 1)
  · obtain ⟨hj1, hj2⟩ := hjw
    have e1 := F.bild_stet (i := j + 1) (φ (n + 1) - (j + 1))
      (fun k h1 h2 => hst k (by omega) (by omega) (by omega))
    rw [Nat.add_sub_of_le (show j + 1 ≤ φ (n + 1) by omega)] at e1
    have e2 := F.bild_stet (i := φ n) (j - φ n) (fun k h1 h2 => hst k h1 (by omega) (by omega))
    rw [Nat.add_sub_of_le hj1] at e2
    rcases F.abbild hN h0 j with ⟨hn, he⟩ | ⟨t, ht, ho⟩
    · left
      rw [e1, he, e2]
    · right
      have hk := hj hj1 hj2
      rw [ht] at hk
      refine ⟨t, hk.symm, ?_⟩
      rw [e1, ← e2]
      exact ho
  · left
    have e := F.bild_stet (i := φ n) (φ (n + 1) - φ n)
      (fun k h1 h2 => hst k h1 (by omega) (fun hk => hjw ⟨by omega, by omega⟩))
    rw [Nat.add_sub_of_le hle] at e
    exact e

/-- **The emitted lock is a run of the abstract lock at G granularity.** -/
theorem Lauf.absLauf {φ : Nat → Nat} {akt : Nat → Option Nat} (hW : Fenster F φ akt) : AbsLauf akt (F.bei φ) where
  ok0 := (bild_ok (Inv.lauf hN F h0 (φ 0))).karte fin_val_inj
  schritt := fun n u hu => by
    rcases F.fenster_fall hN h0 hW n with e | ⟨t, ht, ho⟩
    · unfold Lauf.bei
      rw [e]
      exact ⟨_, _, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    · rw [hu] at ht
      cases ht
      have hr : ∀ a b, AbsSchritt t a b → AbsSchritt t.val (a.karte Fin.val) (b.karte Fin.val) :=
        fun _ _ h => h.karte fin_val_inj
      exact Opt.weg (Opt.karte fin_val_inj hr ho)
  stotter := fun n hn => by
    rcases F.fenster_fall hN h0 hW n with e | ⟨t, ht, _⟩
    · unfold Lauf.bei
      rw [e]
    · rw [hn] at ht
      cases ht

/-- Fewer than `2 ^ wbits - 2` threads wait at any step. -/
theorem Lauf.bei_schranke [Conf] (φ : Nat → Nat) (n : Nat) :
    (F.bei φ n).queue.length + 2 < 2 ^ Conf.wbits := by
  have h1 : (F.bei φ n).queue.length ≤ N := by
    show ((bild (F.z (φ n))).queue.map Fin.val).length ≤ N
    rw [List.length_map]
    exact Nat.le_trans (bild_laenge _) (Inv.lauf hN F h0 (φ n)).laenge
  have h2 : 2147483649 < 2 ^ Conf.wbits := by
    rcases Conf.wide with h | h <;> rw [h] <;> decide
  omega

/-- **THE EMITTED LOCK CARRIES THE MODEL'S GHOST**: a ghost run of `Tkt` that shows the emitted lock at the start of
    every G step (`Passt`, with `Tkt.Ok`) and moves only by the scheduled thread's `take`/`enter`/`leave`. -/
theorem Lauf.tkt [Conf] {φ : Nat → Nat} {akt : Nat → Option Nat} (hW : Fenster F φ akt) :
    ∃ gh : Nat → Tkt, (∀ n, Passt (gh n) (F.bei φ n)) ∧ ∀ n, Nach (akt n) (gh n) (gh (n + 1)) :=
  (F.absLauf hN h0 hW).tkt (Lauf.bei_schranke hN F h0 φ)

end

/-- **Every run of the emitted lock is a run at its own granularity**: each step its own window. -/
theorem Fenster.id (F : Lauf N) : Fenster F (fun n => n) (fun n => (F.akt n).map Fin.val) :=
  fun n => ⟨Nat.le_succ n, n, fun _ _ => rfl,
    fun i h1 h2 h3 => absurd (Nat.le_antisymm (Nat.le_of_lt_succ h2) h1) h3⟩

/-- The holder at a window start is the thread holding the emitted lock. -/
theorem Lauf.bei_halter (hN : N ≤ 2147483647) (F : Lauf N) (h0 : Inv N (F.z 0)) (φ : Nat → Nat) (n : Nat)
    (t : Fin N) : (F.bei φ n).holder = some t.val ↔ ((F.z (φ n)).pc t).haelt = true := by
  rw [← bild_halter (Inv.lauf hN F h0 (φ n)) t]
  constructor
  · exact karte_some fin_val_inj
  · intro h
    show (bild (F.z (φ n))).holder.map Fin.val = some t.val
    simp only [h, Option.map_some]

end Gabbro.Stage0.Senke.Faeden
