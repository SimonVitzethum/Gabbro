/-
  File:      Grammatik/Speichermodell/Zaehler.lean
  Subject:   A RELAXED COUNTER incremented by two threads with `fetch_add` (Opus lane O25,
             2026-09-26): the final value is 2 -- when the read-modify-write is ATOMIC in the
             view machine; and why machine W as it stands cannot prove it.

  THE MACHINE. One location, two threads, each runs ONE `fetch_add(1)` (relaxed; the order
  plays no role for one location). A message is `⟨ts, wert⟩` as in `Sicht.lean`; a thread has
  a view (a timestamp). Two step rules:
  * `ZSchritt` -- the ATOMIC RMW of RC11's timestamp machine: read ANY message `m` at or above
    the view, write `m.wert + 1` at timestamp `m.ts + 1`, which must be free. Nothing can ever
    be placed between the read message and the write in modification order (timestamps are
    natural numbers), which is RMW atomicity.
  * `ZSchrittW` -- the shape machine W gives an `exchange` today (`SchrittW`, MaschineW.lean:
    the step reads any message at or above the view, and writes at ANY fresh timestamp above
    the view after the read -- `Frisch` over `vorSicht`); no adjacency.

  PROVED:
  * `zaehler_zwei` -- under `ZSchritt`, on EVERY run in which both threads have done their
    increment, the newest message holds 2 (and a message with 2 exists); the invariant is
    `ZInv`: the history is exactly the timestamps `0 … n` with `wert = ts`.
  * `zaehler_verloren` -- under `ZSchrittW`, the LOST UPDATE is reachable: both threads read
    the initial 0, both write 1, the newest message holds 1 and no message holds 2.
  So the counter's final value is a theorem of an atomic-RMW view machine, and NOT of machine
  W: W over-approximates RC11 at `exchange` (the safe direction for the DRF leg `schwach`,
  which quantifies over W's steps) but is too weak for a user relying on `fetch_add`
  atomicity. Closing it means adding the adjacency to `SchrittW` for a step that reads and
  writes the same atomic -- a change of the machine `Spec.lean` imports, so a reviewed
  Spec diff, not made here (`messung/OPUS-O25-ATOMICS.md` §6).
-/
import Grammatik.Speichermodell.Sicht

namespace Gabbro.Grammatik.Speichermodell

/-- A message of the counter: timestamp and value. -/
structure ZNachricht where
  ts : Nat
  wert : Int

/-- The state: per thread whether it has done its increment and its view; the history; and the
    number `n` of increments done so far. -/
structure ZZustand where
  fertig : Nat → Bool
  sicht : Nat → Nat
  hist : List ZNachricht
  n : Nat

/-- The start: the initial message `⟨0, 0⟩`, nobody done, every view 0. -/
def ZZustand.start : ZZustand := ⟨fun _ => false, fun _ => 0, [⟨0, 0⟩], 0⟩

/-- The state after thread `t` wrote `w` at timestamp `ts`. -/
def ZZustand.nach (Z : ZZustand) (t : Nat) (ts : Nat) (w : Int) : ZZustand :=
  ⟨fun u => if u = t then true else Z.fertig u, fun u => if u = t then ts else Z.sicht u,
   ⟨ts, w⟩ :: Z.hist, Z.n + 1⟩

/-- **The atomic RMW step** (thread 0 or 1, once): read `m` at or above the view, write
    `m.wert + 1` at `m.ts + 1`, which must be free. -/
inductive ZSchritt : ZZustand → ZZustand → Prop
  | rmw (Z : ZZustand) (t : Nat) (m : ZNachricht) (ht : t < 2) (hf : Z.fertig t = false)
      (hm : m ∈ Z.hist) (hv : Z.sicht t ≤ m.ts) (hfrei : ∀ m' ∈ Z.hist, m'.ts ≠ m.ts + 1) :
      ZSchritt Z (Z.nach t (m.ts + 1) (m.wert + 1))

/-- **W's shape of an `exchange`**: read `m` at or above the view, write `m.wert + 1` at ANY
    fresh timestamp above the view after the read. -/
inductive ZSchrittW : ZZustand → ZZustand → Prop
  | rmw (Z : ZZustand) (t : Nat) (m : ZNachricht) (ts : Nat) (ht : t < 2)
      (hf : Z.fertig t = false) (hm : m ∈ Z.hist) (hv : Z.sicht t ≤ m.ts) (hts : m.ts < ts)
      (hfrei : ∀ m' ∈ Z.hist, m'.ts ≠ ts) :
      ZSchrittW Z (Z.nach t ts (m.wert + 1))

/-- Reflexive-transitive closure. -/
inductive ZErreichbar (R : ZZustand → ZZustand → Prop) : ZZustand → Prop
  | start : ZErreichbar R ZZustand.start
  | schritt (Z Z' : ZZustand) : ZErreichbar R Z → R Z Z' → ZErreichbar R Z'

/-- The number of threads (of the two) that are done. -/
def ZZustand.fertige (Z : ZZustand) : Nat :=
  (if Z.fertig 0 then 1 else 0) + (if Z.fertig 1 then 1 else 0)

/-- **The invariant of the atomic counter**: the history holds exactly the timestamps `0 … n`,
    every message's value is its timestamp, `n` counts the threads that are done, and only
    threads 0 and 1 are ever done. -/
structure ZInv (Z : ZZustand) : Prop where
  genau : ∀ i, (∃ m ∈ Z.hist, m.ts = i) ↔ i ≤ Z.n
  wert : ∀ m ∈ Z.hist, m.wert = m.ts
  zahl : Z.n = Z.fertige
  sonst : ∀ u, 2 ≤ u → Z.fertig u = false

theorem zInv_start : ZInv ZZustand.start where
  genau i := by
    constructor
    · rintro ⟨m, hm, rfl⟩
      rw [List.mem_singleton.mp hm]
      exact Nat.le_refl 0
    · intro h
      exact ⟨⟨0, 0⟩, List.mem_singleton_self _, (Nat.le_zero.mp h).symm⟩
  wert m hm := by rw [List.mem_singleton.mp hm]; rfl
  zahl := rfl
  sonst _ _ := rfl

theorem zInv_schritt {Z Z' : ZZustand} (hI : ZInv Z) (hs : ZSchritt Z Z') : ZInv Z' := by
  cases hs with
  | rmw t m ht hf hm hv hfrei =>
      -- the message read is the newest: `m.ts + 1` is free, so `m.ts = n`
      have hle : m.ts ≤ Z.n := (hI.genau m.ts).mp ⟨m, hm, rfl⟩
      have hn : m.ts = Z.n := by
        apply Classical.byContradiction
        intro hne
        obtain ⟨m', hm', he⟩ := (hI.genau (m.ts + 1)).mpr (by omega)
        exact hfrei m' hm' he
      have hw := hI.wert m hm
      refine ⟨fun i => ?_, fun m' hm' => ?_, ?_, fun u hu => ?_⟩
      · show (∃ m' ∈ (⟨m.ts + 1, m.wert + 1⟩ :: Z.hist : List ZNachricht), m'.ts = i) ↔ i ≤ Z.n + 1
        constructor
        · rintro ⟨m', hm', rfl⟩
          rcases List.mem_cons.mp hm' with rfl | hm'
          · show m.ts + 1 ≤ Z.n + 1; omega
          · exact Nat.le_trans ((hI.genau m'.ts).mp ⟨m', hm', rfl⟩) (Nat.le_succ _)
        · intro h
          by_cases hi : i = Z.n + 1
          · exact ⟨⟨m.ts + 1, m.wert + 1⟩, List.mem_cons_self, by show m.ts + 1 = i; omega⟩
          · obtain ⟨m', hm', he⟩ := (hI.genau i).mpr (by omega)
            exact ⟨m', List.mem_cons_of_mem _ hm', he⟩
      · rcases List.mem_cons.mp hm' with rfl | hm'
        · show m.wert + 1 = ((m.ts + 1 : Nat) : Int)
          rw [hw]; push_cast; rfl
        · exact hI.wert m' hm'
      · show Z.n + 1 = (if (if (0 : Nat) = t then true else Z.fertig 0) then 1 else 0) +
          (if (if (1 : Nat) = t then true else Z.fertig 1) then 1 else 0)
        have hz := hI.zahl
        unfold ZZustand.fertige at hz
        have ht' : t = 0 ∨ t = 1 := by omega
        rcases ht' with rfl | rfl
        · rw [hf] at hz; simp at hz ⊢; omega
        · rw [hf] at hz; simp at hz ⊢; omega
      · show (if u = t then true else Z.fertig u) = false
        rw [if_neg (by omega)]
        exact hI.sonst u hu

theorem zInv_erreichbar {Z : ZZustand} (hr : ZErreichbar ZSchritt Z) : ZInv Z := by
  induction hr with
  | start => exact zInv_start
  | schritt Z Z' _ hs ih => exact zInv_schritt ih hs

/-- **THE COUNTER IS 2.** Under the atomic RMW, on every run in which both threads have done
    their `fetch_add(1)`: a message with value 2 exists, and it is the newest (every message's
    timestamp is at most its). -/
theorem zaehler_zwei {Z : ZZustand} (hr : ZErreichbar ZSchritt Z) (h0 : Z.fertig 0 = true)
    (h1 : Z.fertig 1 = true) :
    ∃ m ∈ Z.hist, m.wert = 2 ∧ ∀ m' ∈ Z.hist, m'.ts ≤ m.ts := by
  have hI := zInv_erreichbar hr
  have hn : Z.n = 2 := by
    have := hI.zahl; unfold ZZustand.fertige at this; rw [h0, h1] at this; exact this
  obtain ⟨m, hm, hts⟩ := (hI.genau 2).mpr (by omega)
  refine ⟨m, hm, by rw [hI.wert m hm, hts]; rfl, fun m' hm' => ?_⟩
  have := (hI.genau m'.ts).mp ⟨m', hm', rfl⟩
  omega

/-- Non-degenerate: a run of the atomic counter in which both threads are done exists. -/
theorem zaehler_lauf :
    ∃ Z, ZErreichbar ZSchritt Z ∧ Z.fertig 0 = true ∧ Z.fertig 1 = true := by
  let Z1 := ZZustand.start.nach 0 1 1
  have s1 : ZSchritt ZZustand.start Z1 :=
    ZSchritt.rmw ZZustand.start 0 ⟨0, 0⟩ (by decide) rfl (List.mem_singleton_self _)
      (Nat.le_refl 0) (fun m' hm' => by rw [List.mem_singleton.mp hm']; decide)
  let Z2 := Z1.nach 1 2 2
  have s2 : ZSchritt Z1 Z2 := by
    have := ZSchritt.rmw Z1 1 ⟨1, 1⟩ (by decide) rfl List.mem_cons_self (Nat.zero_le _)
      (fun m' hm' => by
        rcases List.mem_cons.mp hm' with rfl | hm'
        · decide
        · rw [List.mem_singleton.mp hm']; decide)
    exact this
  exact ⟨Z2, .schritt _ _ (.schritt _ _ .start s1) s2, rfl, rfl⟩

/-- **THE LOST UPDATE ON W's SHAPE.** Under `ZSchrittW` (read any message at or above the view,
    write at any fresh timestamp above it) both threads read the initial 0 and write 1: both
    are done, the newest message holds 1, and no message holds 2. -/
theorem zaehler_verloren :
    ∃ Z, ZErreichbar ZSchrittW Z ∧ Z.fertig 0 = true ∧ Z.fertig 1 = true ∧
      (∃ m ∈ Z.hist, m.wert = 1 ∧ ∀ m' ∈ Z.hist, m'.ts ≤ m.ts) ∧ ∀ m ∈ Z.hist, m.wert ≠ 2 := by
  let Z1 := ZZustand.start.nach 0 1 1
  have s1 : ZSchrittW ZZustand.start Z1 :=
    ZSchrittW.rmw ZZustand.start 0 ⟨0, 0⟩ 1 (by decide) rfl (List.mem_singleton_self _)
      (Nat.le_refl 0) (by decide) (fun m' hm' => by rw [List.mem_singleton.mp hm']; decide)
  -- thread 1's view is still 0: it reads the INITIAL message and writes 1 at timestamp 2
  let Z2 := Z1.nach 1 2 1
  have s2 : ZSchrittW Z1 Z2 := by
    have := ZSchrittW.rmw Z1 1 ⟨0, 0⟩ 2 (by decide) rfl
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (Nat.le_refl 0) (by decide)
      (fun m' hm' => by
        rcases List.mem_cons.mp hm' with rfl | hm'
        · decide
        · rw [List.mem_singleton.mp hm']; decide)
    exact this
  refine ⟨Z2, .schritt _ _ (.schritt _ _ .start s1) s2, rfl, rfl,
    ⟨⟨2, 1⟩, List.mem_cons_self, rfl, fun m' hm' => ?_⟩, fun m hm => ?_⟩
  · simp only [Z2, Z1, ZZustand.nach, ZZustand.start, List.mem_cons, List.not_mem_nil, or_false] at hm'
    rcases hm' with rfl | rfl | rfl <;> decide
  · simp only [Z2, Z1, ZZustand.nach, ZZustand.start, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide

end Gabbro.Grammatik.Speichermodell

#print axioms Gabbro.Grammatik.Speichermodell.zaehler_zwei
#print axioms Gabbro.Grammatik.Speichermodell.zaehler_lauf
#print axioms Gabbro.Grammatik.Speichermodell.zaehler_verloren
