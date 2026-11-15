/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Fenster.lean
  Subject:   THE EMITTED LOCK AT THE GRANULARITY OF MACHINE G. A run of the emitted lock (Faeden/Maschine.lean) is
             finer than a run of machine G: the waiter count, FUTEX_WAIT and FUTEX_WAKE, the failed `cas` loops are
             steps of their own. `φ n` names the step of the emitted run at which G's scheduler step `n` begins; the
             WINDOW `[φ n, φ (n + 1))` holds the emitted steps of G's step `n`.
             One G step of a thread can do up to THREE things to one lock (`Weg`): give it, draw a ticket, enter. A
             step that leaves `locks L { .. }` with a further `locks L { .. }` as the next statement gives `L` (the
             rule `freiGib` of machine G) and exposes the next `locks L` as the thread's head, which is the draw
             (`GSicht`: the threads standing at `locks L` are the waiting threads) -- two changes of the abstract lock
             in one G step. `Fenster F φ akt`: the window of G's step `n` is cut into three consecutive segments, the
             first holds at most one change of the abstract lock and that change is a give, the second a draw, the
             third an enter, each by the thread G schedules at `n` (`akt`, threads named by number). Then
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

/-- **A segment of a window changes the abstract lock at most once, by a step of kind `K` of thread `who`**: every
    emitted step of `[a, b)` but at most one (`j`) leaves the abstract lock alone; step `j`, if it lies in the segment,
    is a step of the thread `who` (the one G schedules) and, if that thread acts, is a step of kind `K` or a
    stutter. -/
def Einmal (F : Lauf N) (K : Fin N → Abs (Fin N) → Abs (Fin N) → Prop) (a b : Nat) (who : Option Nat) : Prop :=
  ∃ j, (a ≤ j → j < b → (F.akt j).map Fin.val = who ∧
      ∀ t, F.akt j = some t → Opt (K t) (bild (F.z j)) (bild (F.z (j + 1)))) ∧
    ∀ i, a ≤ i → i < b → i ≠ j → bild (F.z (i + 1)) = bild (F.z i)

/-- **The window condition**: the windows follow each other, and the window of G's step `n` is cut into a give
    segment, a draw segment and an enter segment (`Einmal` with `Gibt`, `Zieht`, `Tritt`), all by the thread G
    schedules at `n`. A G step that only enters, or only draws, uses one segment; a G step that gives and exposes a
    further `locks L` uses the first two. -/
def Fenster (F : Lauf N) (φ : Nat → Nat) (akt : Nat → Option Nat) : Prop :=
  ∀ n, φ n ≤ φ (n + 1) ∧ ∃ p q, φ n ≤ p ∧ p ≤ q ∧ q ≤ φ (n + 1) ∧
    Einmal F Gibt (φ n) p (akt n) ∧ Einmal F Zieht p q (akt n) ∧ Einmal F Tritt q (φ (n + 1)) (akt n)

/-- Steps that leave the abstract lock alone leave it alone together. -/
theorem Lauf.bild_stet (F : Lauf N) {i : Nat} : ∀ d,
    (∀ k, i ≤ k → k < i + d → bild (F.z (k + 1)) = bild (F.z k)) → bild (F.z (i + d)) = bild (F.z i)
  | 0, _ => rfl
  | d + 1, h => by
    rw [← Nat.add_assoc, h (i + d) (by omega) (by omega)]
    exact Lauf.bild_stet F d (fun k h1 h2 => h k h1 (by omega))

/-- **One segment is one step of its kind, or nothing happens**: a thread that acts in the segment makes at most one
    step of kind `K`; the segment as a whole is that `Opt`. -/
theorem Einmal.opt {F : Lauf N} {K : Fin N → Abs (Fin N) → Abs (Fin N) → Prop} {a b : Nat} {who : Option Nat}
    (h : Einmal F K a b who) (hab : a ≤ b) (t : Fin N) (ht : who = some t.val) :
    Opt (K t) (bild (F.z a)) (bild (F.z b)) := by
  obtain ⟨j, hj, hst⟩ := h
  by_cases hjw : a ≤ j ∧ j < b
  · obtain ⟨hj1, hj2⟩ := hjw
    obtain ⟨hm, hk⟩ := hj hj1 hj2
    have hat : F.akt j = some t := by
      rw [ht] at hm
      cases hx : F.akt j with
      | none => rw [hx] at hm; simp only [Option.map_none, reduceCtorEq] at hm
      | some y =>
        rw [hx] at hm
        simp only [Option.map_some, Option.some.injEq] at hm
        rw [fin_val_inj hm]
    have e1 := F.bild_stet (i := j + 1) (b - (j + 1))
      (fun k h1 h2 => hst k (by omega) (by omega) (by omega))
    rw [Nat.add_sub_of_le (show j + 1 ≤ b by omega)] at e1
    have e2 := F.bild_stet (i := a) (j - a) (fun k h1 h2 => hst k h1 (by omega) (by omega))
    rw [Nat.add_sub_of_le hj1] at e2
    rw [e1, ← e2]
    exact hk t hat
  · have e := F.bild_stet (i := a) (b - a)
      (fun k h1 h2 => hst k h1 (by omega) (fun hk => hjw ⟨by omega, by omega⟩))
    rw [Nat.add_sub_of_le hab] at e
    exact Or.inl e.symm

/-- **A segment whose thread is no thread of the emitted run leaves the abstract lock alone.** -/
theorem Einmal.stet (hN : N ≤ 2147483647) {F : Lauf N} (h0 : Inv N (F.z 0))
    {K : Fin N → Abs (Fin N) → Abs (Fin N) → Prop} {a b : Nat} {who : Option Nat}
    (h : Einmal F K a b who) (hab : a ≤ b) (hx : ∀ t : Fin N, who ≠ some t.val) :
    bild (F.z b) = bild (F.z a) := by
  obtain ⟨j, hj, hst⟩ := h
  by_cases hjw : a ≤ j ∧ j < b
  · obtain ⟨hj1, hj2⟩ := hjw
    obtain ⟨hm, -⟩ := hj hj1 hj2
    have hj' : bild (F.z (j + 1)) = bild (F.z j) := by
      rcases F.abbild hN h0 j with ⟨_, he⟩ | ⟨t, ht, _⟩
      · exact he
      · rw [ht] at hm
        simp only [Option.map_some] at hm
        exact absurd hm.symm (hx t)
    have e1 := F.bild_stet (i := j + 1) (b - (j + 1))
      (fun k h1 h2 => hst k (by omega) (by omega) (by omega))
    rw [Nat.add_sub_of_le (show j + 1 ≤ b by omega)] at e1
    have e2 := F.bild_stet (i := a) (j - a) (fun k h1 h2 => hst k h1 (by omega) (by omega))
    rw [Nat.add_sub_of_le hj1] at e2
    rw [e1, hj', e2]
  · have e := F.bild_stet (i := a) (b - a)
      (fun k h1 h2 => hst k h1 (by omega) (fun hk => hjw ⟨by omega, by omega⟩))
    rw [Nat.add_sub_of_le hab] at e
    exact e

section

variable (hN : N ≤ 2147483647) (F : Lauf N) (h0 : Inv N (F.z 0))
include hN h0

/-- **One window is a stutter or one `Weg` of G's thread**: a give, a draw and an enter, each optional, in this
    order. -/
theorem Lauf.fenster_fall {φ : Nat → Nat} {akt : Nat → Option Nat} (hW : Fenster F φ akt) (n : Nat) :
    bild (F.z (φ (n + 1))) = bild (F.z (φ n)) ∨
      ∃ t : Fin N, akt n = some t.val ∧ Weg t (bild (F.z (φ n))) (bild (F.z (φ (n + 1)))) := by
  obtain ⟨hle, p, q, h1, h2, h3, e1, e2, e3⟩ := hW n
  by_cases hx : ∃ t : Fin N, akt n = some t.val
  · obtain ⟨t, ht⟩ := hx
    exact Or.inr ⟨t, ht, bild (F.z p), bild (F.z q), e1.opt h1 t ht, e2.opt h2 t ht, e3.opt h3 t ht⟩
  · left
    have hx' : ∀ t : Fin N, akt n ≠ some t.val := fun t ht => hx ⟨t, ht⟩
    rw [e3.stet hN h0 (by omega) hx', e2.stet hN h0 (by omega) hx', e1.stet hN h0 (by omega) hx']

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
      exact ho.karte fin_val_inj
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

/-- **Every run of the emitted lock is a run at its own granularity**: each step its own window; the one step of the
    window is placed in the segment of its kind (give, draw or enter), the other two segments are empty. -/
theorem Fenster.id (hN : N ≤ 2147483647) (F : Lauf N) (h0 : Inv N (F.z 0)) :
    Fenster F (fun n => n) (fun n => (F.akt n).map Fin.val) := by
  intro n
  refine ⟨Nat.le_succ n, ?_⟩
  have hleer : ∀ (K : Fin N → Abs (Fin N) → Abs (Fin N) → Prop) (a : Nat) (who : Option Nat),
      Einmal F K a a who :=
    fun K a who => ⟨a, fun h1 h2 => absurd h2 (Nat.not_lt.2 h1), fun i h1 h2 => absurd h2 (Nat.not_lt.2 h1)⟩
  have hein : ∀ K : Fin N → Abs (Fin N) → Abs (Fin N) → Prop,
      (∀ t, F.akt n = some t → Opt (K t) (bild (F.z n)) (bild (F.z (n + 1)))) →
      Einmal F K n (n + 1) ((F.akt n).map Fin.val) :=
    fun K hK => ⟨n, fun _ _ => ⟨rfl, hK⟩,
      fun i h1 h2 h3 => absurd (Nat.le_antisymm (Nat.le_of_lt_succ h2) h1) h3⟩
  rcases F.abbild hN h0 n with ⟨hn, _⟩ | ⟨t, ht, ho⟩
  · exact ⟨n, n, Nat.le_refl n, Nat.le_refl n, Nat.le_succ n, hleer _ _ _, hleer _ _ _,
      hein Tritt (fun t' h => by rw [hn] at h; cases h)⟩
  · rcases ho with e | h
    · exact ⟨n, n, Nat.le_refl n, Nat.le_refl n, Nat.le_succ n, hleer _ _ _, hleer _ _ _,
        hein Tritt (fun t' h' => by
          obtain rfl := Option.some.inj (ht.symm.trans h')
          exact Or.inl e)⟩
    · cases h with
      | zieht hz =>
        exact ⟨n, n + 1, Nat.le_refl n, Nat.le_succ n, Nat.le_refl (n + 1), hleer _ _ _,
          hein Zieht (fun t' h' => by
            obtain rfl := Option.some.inj (ht.symm.trans h')
            exact Or.inr hz), hleer _ _ _⟩
      | tritt hq =>
        exact ⟨n, n, Nat.le_refl n, Nat.le_refl n, Nat.le_succ n, hleer _ _ _, hleer _ _ _,
          hein Tritt (fun t' h' => by
            obtain rfl := Option.some.inj (ht.symm.trans h')
            exact Or.inr hq)⟩
      | gibt hg =>
        exact ⟨n + 1, n + 1, Nat.le_succ n, Nat.le_refl (n + 1), Nat.le_refl (n + 1),
          hein Gibt (fun t' h' => by
            obtain rfl := Option.some.inj (ht.symm.trans h')
            exact Or.inr hg), hleer _ _ _, hleer _ _ _⟩

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
