/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Fifo.lean
  Subject:   THE CROSS-THREAD LOCK THEOREM, safety half: every run of threads executing the emitted lock code
             (contended paths included: FUTEX_WAIT blocking, returning at once and spuriously, FUTEX_WAKE of all
             waiters, the waiter count, the failed `cas` loops) is, step by step, a run of the abstract ticket lock
             with stuttering (`Lauf.abbild`): each scheduler step is a stutter or one abstract step of the scheduled
             thread. Along it the four facts of the queue of the model's `FifoLauf` (Logik/Fortschritt/PlanLauf.lean)
             hold for the emitted lock, ADAPTED to access granularity (`Lauf.kopf` asks only the entering step to
             be the head; the link to the model's `Tkt` and `FifoLauf` is Faeden/Geist*.lean and Transfer.lean):
             * `Lauf.glied` -- the waiting threads are exactly the threads with a ticket that do not hold the lock;
               a thread blocked in FUTEX_WAIT is one of them (`Lauf.schlaeft_wartet`);
             * `Lauf.eindeutig` -- each once;
             * `Lauf.kopf` -- only the head of the queue takes the lock;
             * `Lauf.ordnung` -- the threads that stay keep their ticket order, ahead of every newcomer;
             and mutual exclusion (`Lauf.ausschluss`). Premises: at most 2147483647 threads (the count the emitted
             FUTEX_WAKE passes), and the invariant at the start (`Inv.start`).
-/
module
public import Stage0.Senke.Sperre.Faeden.Bild
public import Stage0.Senke.Sperre.Faeden.Fair
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

variable {N : Nat}

/-- The threads waiting for the emitted lock at scheduler step `n`, in ticket order. -/
def Lauf.warte (R : Lauf N) (n : Nat) : List (Fin N) := (bild (R.z n)).queue

/-- The thread holding the emitted lock at scheduler step `n`. -/
def Lauf.halter (R : Lauf N) (n : Nat) : Option (Fin N) := (bild (R.z n)).holder

section

variable (hN : N ≤ 2147483647) (R : Lauf N) (h0 : Inv N (R.z 0))
include hN h0

/-- **The refinement**: each scheduler step is a stutter of the abstract ticket lock or one of its steps by the
    scheduled thread. -/
theorem Lauf.abbild (n : Nat) :
    (R.akt n = none ∧ bild (R.z (n + 1)) = bild (R.z n)) ∨
      ∃ t, R.akt n = some t ∧ Opt (AbsSchritt t) (bild (R.z n)) (bild (R.z (n + 1))) := by
  cases hk : R.akt n with
  | none =>
    left
    exact ⟨rfl, by rw [R.stotter n hk]⟩
  | some t =>
    right
    exact ⟨t, rfl, (R.schritt n t hk).abbild hN (Inv.lauf hN R h0 n)⟩

/-- The holder is the thread that holds the emitted lock. -/
theorem Lauf.halter_iff (n : Nat) (u : Fin N) : R.halter n = some u ↔ ((R.z n).pc u).haelt = true :=
  bild_halter (Inv.lauf hN R h0 n) u

/-- **The waiting threads** are exactly the threads with a ticket that do not hold the lock. -/
theorem Lauf.glied (n : Nat) (u : Fin N) :
    u ∈ R.warte n ↔ ((R.z n).pc u).ticket.isSome = true ∧ ((R.z n).pc u).haelt = false :=
  bild_glied (Inv.lauf hN R h0 n) u

/-- **A thread blocked in FUTEX_WAIT is a thread waiting at the lock.** -/
theorem Lauf.schlaeft_wartet (n : Nat) {u : Fin N} (hs : ((R.z n).pc u).schlaeft = true) : u ∈ R.warte n :=
  bild_schlaeft (Inv.lauf hN R h0 n) hs

/-- Each waiting thread once. -/
theorem Lauf.eindeutig (n : Nat) : (R.warte n).Nodup := (bild_ok (Inv.lauf hN R h0 n)).nodup

/-- The holder does not wait. -/
theorem Lauf.halter_wartet_nicht (n : Nat) {u : Fin N} (h : R.halter n = some u) : u ∉ R.warte n :=
  (bild_ok (Inv.lauf hN R h0 n)).frei u h

/-- **Only the head takes the lock**: a waiting thread that holds the lock after its step headed the queue. -/
theorem Lauf.kopf (n : Nat) {u : Fin N} (ha : R.akt n = some u) (hu : u ∈ R.warte n)
    (hh : R.halter (n + 1) = some u) : (R.warte n).head? = some u :=
  Weg.kopf (Opt.weg ((R.schritt n u ha).abbild hN (Inv.lauf hN R h0 n))) (bild_ok (Inv.lauf hN R h0 n)) hu hh

/-- **First come, first served**: the threads that stay keep their order, ahead of every newcomer. -/
theorem Lauf.ordnung (n : Nat) :
    (R.warte n).filter (fun u => decide (u ∈ R.warte (n + 1))) <+: R.warte (n + 1) := by
  show (bild (R.z n)).queue.filter (fun u => decide (u ∈ (bild (R.z (n + 1))).queue)) <+:
    (bild (R.z (n + 1))).queue
  rcases R.abbild hN h0 n with ⟨_, he⟩ | ⟨t, _, ho⟩
  · rw [he]
    have hf : (bild (R.z n)).queue.filter (fun u => decide (u ∈ (bild (R.z n)).queue)) =
        (bild (R.z n)).queue :=
      List.filter_eq_self.2 (fun x hx => decide_eq_true hx)
    exact (congrArg (fun l => l <+: (bild (R.z n)).queue) hf).mpr (List.prefix_refl _)
  · exact Weg.ordnung (Opt.weg ho) (bild_ok (Inv.lauf hN R h0 n)) _ (fun x => decide_eq_true_iff)

/-- **A waiting thread leaves the queue only by taking the lock.** -/
theorem Lauf.verlaesst (n : Nat) {u : Fin N} (hu : u ∈ R.warte n) (hu' : u ∉ R.warte (n + 1)) :
    R.akt n = some u ∧ R.halter (n + 1) = some u := by
  rcases R.abbild hN h0 n with ⟨_, he⟩ | ⟨t, ht, ho⟩
  · exact absurd (by unfold Lauf.warte; rw [he]; exact hu) hu'
  · rcases ho with e | hs
    · exact absurd (by unfold Lauf.warte; rw [← e]; exact hu) hu'
    · cases hs with
      | zieht hz =>
        obtain ⟨_, _, hb⟩ := hz
        refine absurd ?_ hu'
        show u ∈ (bild (R.z (n + 1))).queue
        rw [hb]
        exact List.mem_append.2 (Or.inl hu)
      | tritt ht' =>
        obtain ⟨_, hq, hb⟩ := ht'
        have hut : u = t := by
          obtain ⟨r, hr⟩ := List.head?_eq_some_iff.1 hq
          have hu2 : u ∈ (bild (R.z n)).queue := hu
          rw [hr] at hu2
          rcases List.mem_cons.1 hu2 with e | e
          · exact e
          · refine absurd ?_ hu'
            show u ∈ (bild (R.z (n + 1))).queue
            rw [hb, hr]
            exact e
        rw [hut]
        refine ⟨ht, ?_⟩
        show (bild (R.z (n + 1))).holder = some t
        simp only [hb]
      | gibt hg =>
        obtain ⟨_, hb⟩ := hg
        refine absurd ?_ hu'
        show u ∈ (bild (R.z (n + 1))).queue
        rw [hb]
        exact hu

/-- **Mutual exclusion** of the emitted lock along every run. -/
theorem Lauf.ausschluss (n : Nat) {t u : Fin N} (ht : ((R.z n).pc t).haelt = true)
    (hu : ((R.z n).pc u).haelt = true) : t = u :=
  (Inv.lauf hN R h0 n).ausschluss ht hu

end

end Gabbro.Stage0.Senke.Faeden
