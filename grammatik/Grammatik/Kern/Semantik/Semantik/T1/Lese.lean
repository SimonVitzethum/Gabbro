/-
  File:      grammatik/Grammatik/Kern/Semantik/Semantik/T1/Lese.lean
  Subject:   **The trace without its read events**, the view of a world the outside answers from (`Orakel`,
             T1/Teil2.lean). A read event (`istLeseEv`: a table or global access with `schreibt = false`) is ghost
             bookkeeping of the thread: it changes no cell, takes no lock and asks nothing outside, so no physical
             environment can observe it. `spurOhneLese` deletes exactly those events; writes, `nimmt`, `gibt` and
             questions to the outside (`fremd`) stay, in order. `World.ohneLese` is a world with its trace erased,
             `World.rang` the length of the erased trace (the measure that keeps the records of the replay of the goal
             theorem apart: every question to the outside adds one to it, a read adds nothing).
-/
module
public import Grammatik.Kern.Semantik.Semantik.T1.Teil1
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Read events and their erasure -/

/-- **A read event**: an access to a table or a global that does not write. Every other event -- a write, taking or
    giving a lock, a question to the outside (`fremd`) -- is not a read. -/
def istLeseEv : Ereignis D → Bool
  | .zugriff _ schreibt _ _ => !schreibt
  | .gzugriff _ schreibt _ _ => !schreibt
  | .nimmt _ _ => false
  | .gibt _ => false
  | .fremd _ => false

/-- **The trace without its read events** (newest first, order kept). -/
def spurOhneLese : List (Ereignis D) → List (Ereignis D)
  | [] => []
  | e :: s => cond (istLeseEv e) (spurOhneLese s) (e :: spurOhneLese s)

/-- **An event that is not a read**: a read access turned into the same access writing; every other event stays.
    The replay of the goal theorem takes its fresh trace positions from it. -/
def nichtLese : Ereignis D → Ereignis D
  | .zugriff t _ Λ h => .zugriff t true Λ h
  | .gzugriff g _ Λ h => .gzugriff g true Λ h
  | e => e

theorem istLeseEv_nichtLese (e : Ereignis D) : istLeseEv (nichtLese e) = false := by
  cases e <;> rfl

/-- A table write is not a read. -/
theorem istLeseEv_schreibt (t : D.Tab) (Λ : List (Res D)) (hl : List D.Lock) :
    istLeseEv (Ereignis.zugriff t true Λ hl) = false := rfl

/-- A global write is not a read. -/
theorem istLeseEv_gschreibt (g : D.Glob) (Λ : List (Res D)) (hl : List D.Lock) :
    istLeseEv (Ereignis.gzugriff g true Λ hl) = false := rfl

/-- Taking a lock is not a read. -/
theorem istLeseEv_nimmt (L : D.Lock) (hl : List D.Lock) : istLeseEv (Ereignis.nimmt L hl) = false := rfl

/-- Giving a lock is not a read. -/
theorem istLeseEv_gibt (L : D.Lock) : istLeseEv (Ereignis.gibt (D := D) L) = false := rfl

/-- An answer from outside is not a read: it is never erased. -/
theorem istLeseEv_fremd (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : istLeseEv (Ereignis.fremd (D := D) q) = false := rfl

/-- A read vanishes from the erased trace. -/
theorem spurOhneLese_cons_lese (e : Ereignis D) (h : istLeseEv e = true) (s : List (Ereignis D)) :
    spurOhneLese (e :: s) = spurOhneLese s := by
  simp only [spurOhneLese, h, Bool.cond_true]

/-- Every other event stays, in place. -/
theorem spurOhneLese_cons_bleibt (e : Ereignis D) (h : istLeseEv e = false) (s : List (Ereignis D)) :
    spurOhneLese (e :: s) = e :: spurOhneLese s := by
  simp only [spurOhneLese, h, Bool.cond_false]

/-- The erasure distributes over appending (traces grow at their head). -/
theorem spurOhneLese_append : ∀ (a b : List (Ereignis D)),
    spurOhneLese (a ++ b) = spurOhneLese a ++ spurOhneLese b
  | [], _ => rfl
  | e :: a, b => by
      rw [List.cons_append]
      cases h : istLeseEv e
      · rw [spurOhneLese_cons_bleibt e h, spurOhneLese_cons_bleibt e h, spurOhneLese_append a b,
          List.cons_append]
      · rw [spurOhneLese_cons_lese e h, spurOhneLese_cons_lese e h, spurOhneLese_append a b]

/-- The erased trace has no read event left. -/
theorem spurOhneLese_frei : ∀ (s : List (Ereignis D)), ∀ e ∈ spurOhneLese s, istLeseEv e = false
  | [], _, h => absurd h List.not_mem_nil
  | x :: s, e, h => by
      cases hx : istLeseEv x
      · rw [spurOhneLese_cons_bleibt x hx] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact hx
        · exact spurOhneLese_frei s e h
      · rw [spurOhneLese_cons_lese x hx] at h
        exact spurOhneLese_frei s e h

/-- A trace without reads is its own erasure. -/
theorem spurOhneLese_von_frei : ∀ (s : List (Ereignis D)), (∀ e ∈ s, istLeseEv e = false) →
    spurOhneLese s = s
  | [], _ => rfl
  | x :: s, h => by
      rw [spurOhneLese_cons_bleibt x (h x List.mem_cons_self),
        spurOhneLese_von_frei s (fun e he => h e (List.mem_cons_of_mem _ he))]

/-- **The erasure is idempotent.** -/
theorem spurOhneLese_spurOhneLese (s : List (Ereignis D)) : spurOhneLese (spurOhneLese s) = spurOhneLese s :=
  spurOhneLese_von_frei _ (spurOhneLese_frei s)

/-- The erased trace is no longer than the trace. -/
theorem spurOhneLese_laenge : ∀ (s : List (Ereignis D)), (spurOhneLese s).length ≤ s.length
  | [] => Nat.le_refl _
  | e :: s => by
      have ih := spurOhneLese_laenge s
      cases h : istLeseEv e
      · rw [spurOhneLese_cons_bleibt e h, List.length_cons, List.length_cons]
        omega
      · rw [spurOhneLese_cons_lese e h, List.length_cons]
        omega

/-- **The held locks do not see reads**: the open locks of the erased trace are those of the trace. -/
theorem offen_spurOhneLese : ∀ s : List (Ereignis D), offen (spurOhneLese s) = offen s
  | [] => rfl
  | e :: s => by
      have ih := offen_spurOhneLese s
      cases e with
      | zugriff t w Λ hl =>
          cases w
          · rw [spurOhneLese_cons_lese (.zugriff t false Λ hl) rfl s]
            exact ih
          · rw [spurOhneLese_cons_bleibt (.zugriff t true Λ hl) rfl s]
            exact ih
      | gzugriff g w Λ hl =>
          cases w
          · rw [spurOhneLese_cons_lese (.gzugriff g false Λ hl) rfl s]
            exact ih
          · rw [spurOhneLese_cons_bleibt (.gzugriff g true Λ hl) rfl s]
            exact ih
      | nimmt L hl =>
          rw [spurOhneLese_cons_bleibt (.nimmt L hl) rfl s]
          show L :: offen (spurOhneLese s) = L :: offen s
          rw [ih]
      | gibt L =>
          rw [spurOhneLese_cons_bleibt (.gibt L) rfl s]
          show (offen (spurOhneLese s)).erase L = (offen s).erase L
          rw [ih]
      | fremd q =>
          rw [spurOhneLese_cons_bleibt (.fremd q) rfl s]
          exact ih

/-! ## 2. Worlds without reads, and the rank -/

/-- **The world the outside sees**: the same memory, the trace without its read events. -/
def World.ohneLese (σ : World D) : World D := { σ with spur := spurOhneLese σ.spur }

/-- **The rank of a world**: the length of its erased trace. -/
def World.rang (σ : World D) : Nat := (spurOhneLese σ.spur).length

/-- **`w`'s memory, `w`'s trace on top of `σ`'s**: how an answer of the outside (whose trace lists only the events it
    adds) lands on the asking world. -/
def World.auf (w σ : World D) : World D := ⟨w.slots, w.globs, w.spur ++ σ.spur⟩

theorem World.ohneLese_slots (σ : World D) : σ.ohneLese.slots = σ.slots := rfl

theorem World.ohneLese_globs (σ : World D) : σ.ohneLese.globs = σ.globs := rfl

theorem World.ohneLese_spur (σ : World D) : σ.ohneLese.spur = spurOhneLese σ.spur := rfl

/-- The held locks of the erased world are the world's. -/
theorem World.ohneLese_haelt (σ : World D) : σ.ohneLese.haelt = σ.haelt :=
  offen_spurOhneLese σ.spur

theorem World.ohneLese_ohneLese (σ : World D) : σ.ohneLese.ohneLese = σ.ohneLese := by
  show ({ σ with spur := spurOhneLese (spurOhneLese σ.spur) } : World D) = { σ with spur := spurOhneLese σ.spur }
  rw [spurOhneLese_spurOhneLese]

/-- Two worlds with one erasure have one rank. -/
theorem World.rang_eq {σ σ' : World D} (h : σ.ohneLese = σ'.ohneLese) : σ.rang = σ'.rang := by
  show (σ.ohneLese.spur).length = (σ'.ohneLese.spur).length
  rw [h]

/-- The rank is at most the trace's length. -/
theorem World.rang_le_laenge (σ : World D) : σ.rang ≤ σ.spur.length := spurOhneLese_laenge σ.spur

/-- **Equal erasures from memory and erased trace.** -/
theorem World.ohneLese_eq_of {σ σ' : World D} (hs : σ.slots = σ'.slots) (hg : σ.globs = σ'.globs)
    (hsp : spurOhneLese σ.spur = spurOhneLese σ'.spur) : σ.ohneLese = σ'.ohneLese := by
  show ({ slots := σ.slots, globs := σ.globs, spur := spurOhneLese σ.spur } : World D) =
    { slots := σ'.slots, globs := σ'.globs, spur := spurOhneLese σ'.spur }
  rw [hs, hg, hsp]

theorem World.slots_of_ohneLese {σ σ' : World D} (h : σ.ohneLese = σ'.ohneLese) : σ.slots = σ'.slots := by
  have e := congrArg World.slots h
  exact e

theorem World.globs_of_ohneLese {σ σ' : World D} (h : σ.ohneLese = σ'.ohneLese) : σ.globs = σ'.globs := by
  have e := congrArg World.globs h
  exact e

theorem World.spur_of_ohneLese {σ σ' : World D} (h : σ.ohneLese = σ'.ohneLese) :
    spurOhneLese σ.spur = spurOhneLese σ'.spur :=
  congrArg World.spur h

/-- The answer world keeps the outside's memory. -/
theorem World.auf_slots (w σ : World D) : (w.auf σ).slots = w.slots := rfl

theorem World.auf_globs (w σ : World D) : (w.auf σ).globs = w.globs := rfl

theorem World.auf_spur (w σ : World D) : (w.auf σ).spur = w.spur ++ σ.spur := rfl

/-- An answer that adds no event and keeps the memory is the asking world. -/
theorem World.auf_leer (σ : World D) : ({ σ.ohneLese with spur := [] } : World D).auf σ = σ := rfl

/-! ## 3. The rank along the steps of a thread -/

/-- A read (`World.lese`) adds only read events. -/
theorem spurOhneLese_lese (σ : World D) (Λ : List (Res D)) :
    ∀ os : List (D.Tab ⊕ D.Glob), spurOhneLese (σ.lese Λ os).spur = spurOhneLese σ.spur
  | [] => rfl
  | .inl t :: os => by
      have e : (σ.lese Λ (.inl t :: os)).spur =
          Ereignis.zugriff t false Λ σ.haelt :: (σ.lese Λ os).spur := rfl
      rw [e, spurOhneLese_cons_lese (.zugriff t false Λ σ.haelt) rfl, spurOhneLese_lese σ Λ os]
  | .inr g :: os => by
      have e : (σ.lese Λ (.inr g :: os)).spur =
          Ereignis.gzugriff g false Λ σ.haelt :: (σ.lese Λ os).spur := rfl
      rw [e, spurOhneLese_cons_lese (.gzugriff g false Λ σ.haelt) rfl, spurOhneLese_lese σ Λ os]

/-- A read keeps the erasure. -/
theorem World.lese_ohneLese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ os).ohneLese = σ.ohneLese :=
  World.ohneLese_eq_of rfl rfl (spurOhneLese_lese σ Λ os)

/-- A read keeps the rank. -/
theorem World.rang_lese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ os).rang = σ.rang := by
  show (spurOhneLese (σ.lese Λ os).spur).length = (spurOhneLese σ.spur).length
  rw [spurOhneLese_lese]

/-- The rank of a world with events on top. -/
theorem World.rang_merke (σ : World D) (es : List (Ereignis D)) :
    (σ.merke es).rang = (spurOhneLese es).length + σ.rang := by
  show (spurOhneLese (es ++ σ.spur)).length = (spurOhneLese es).length + (spurOhneLese σ.spur).length
  rw [spurOhneLese_append, List.length_append]

/-- **A question to the outside adds one to the rank.** -/
theorem World.rang_fragt (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : (σ.fragt q).rang = σ.rang + 1 := by
  show (spurOhneLese (Ereignis.fremd q :: σ.spur)).length = (spurOhneLese σ.spur).length + 1
  rw [spurOhneLese_cons_bleibt (Ereignis.fremd q) rfl, List.length_cons]

theorem World.rang_nimmt (σ : World D) (L : D.Lock) : (σ.nimmt L).rang = σ.rang + 1 := by
  show (spurOhneLese (Ereignis.nimmt L σ.haelt :: σ.spur)).length = (spurOhneLese σ.spur).length + 1
  rw [spurOhneLese_cons_bleibt (Ereignis.nimmt L σ.haelt) rfl, List.length_cons]

theorem World.rang_gibt (σ : World D) (L : D.Lock) : (σ.gibt L).rang = σ.rang + 1 := by
  show (spurOhneLese (Ereignis.gibt L :: σ.spur)).length = (spurOhneLese σ.spur).length + 1
  rw [spurOhneLese_cons_bleibt (Ereignis.gibt L) rfl, List.length_cons]

/-- The rank does not fall below a world's when events land on top of it. -/
theorem World.rang_auf (w σ : World D) : σ.rang ≤ (w.auf σ).rang := by
  show (spurOhneLese σ.spur).length ≤ (spurOhneLese (w.spur ++ σ.spur)).length
  rw [spurOhneLese_append, List.length_append]
  exact Nat.le_add_left _ _

/-- A question to the outside does not lower the rank. -/
theorem World.rang_le_fragt (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : σ.rang ≤ (σ.fragt q).rang := by
  rw [World.rang_fragt]
  exact Nat.le_succ _

theorem World.rang_le_nimmt (σ : World D) (L : D.Lock) : σ.rang ≤ (σ.nimmt L).rang := by
  rw [World.rang_nimmt]
  exact Nat.le_succ _

theorem World.rang_le_gibt (σ : World D) (L : D.Lock) : σ.rang ≤ (σ.gibt L).rang := by
  rw [World.rang_gibt]
  exact Nat.le_succ _

/-- Events on top do not lower the rank. -/
theorem World.rang_le_merke (σ : World D) (es : List (Ereignis D)) : σ.rang ≤ (σ.merke es).rang := by
  rw [World.rang_merke]
  exact Nat.le_add_left _ _

/-- A read does not lower the rank. -/
theorem World.rang_le_lese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    σ.rang ≤ (σ.lese Λ os).rang :=
  Nat.le_of_eq (World.rang_lese σ Λ os).symm

/-- A trace that grows at its head does not lose rank. -/
theorem rang_append_le (neu s : List (Ereignis D)) :
    (spurOhneLese s).length ≤ (spurOhneLese (neu ++ s)).length := by
  rw [spurOhneLese_append, List.length_append]
  exact Nat.le_add_left _ _

/-- A non-read event on top adds one to the erased length. -/
theorem rang_nichtLese_cons (e : Ereignis D) (s : List (Ereignis D)) :
    (spurOhneLese (nichtLese e :: s)).length = (spurOhneLese s).length + 1 := by
  rw [spurOhneLese_cons_bleibt _ (istLeseEv_nichtLese e), List.length_cons]

/-- The open locks do not see which access a fresh event is. -/
theorem offen_nichtLese_cons (e : Ereignis D) (s : List (Ereignis D)) :
    offen (nichtLese e :: s) = offen (e :: s) := by
  cases e <;> rfl

end Gabbro.Grammatik
