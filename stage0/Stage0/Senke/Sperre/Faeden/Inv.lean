/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Inv.lean
  Subject:   THE INVARIANT of the emitted lock run by many threads (`Faeden/Maschine.lean`), and the lemmas that
             carry it over a step that moves one thread:
             * the ghost queue `q` holds exactly the threads with a ticket, without duplicates, the `i`-th with the
               ticket `serving + i`, and `next = serving + |q|` (so `|q| ≤ N` and the word tests are exact);
             * a thread holding the lock heads the queue (mutual exclusion);
             * the waiter word is exactly the number of threads between their increment and their decrement;
             * a waiting thread's loaded serving value `s0` lies below its ticket and at most `N` below it;
             * NO LOST WAKE-UP: a thread blocked in FUTEX_WAIT with value `s0` either sees the serving word still
               equal to `s0` in its low 32 bits, or some thread is a pending waker (it advanced `serving` and has
               not done its WAKE yet).
-/
module
public import Stage0.Senke.Sperre.Faeden.Maschine
public import Mathlib.Data.Fintype.Card
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

/-- A waiting thread with ticket `k` loaded the serving value `s0`: not after now, below its ticket, at most `N`
    below it. -/
def Wartet (N : Nat) (w : Wort) (k s0 : Nat) : Prop := s0 ≤ w.serv ∧ s0 < k ∧ k < s0 + N

/-- What the frame values of a thread at `o` satisfy against the words. -/
def OrtOK (N : Nat) (w : Wort) : Ort → Prop
  | .frei => True
  | .ladeN => True
  | .casN _ => True
  | .ladeS _ => True
  | .incL k s0 => Wartet N w k s0
  | .incC k s0 _ => Wartet N w k s0
  | .futexW k s0 => Wartet N w k s0
  | .blockiert k s0 => Wartet N w k s0
  | .decL k s0 => Wartet N w k s0
  | .decC k s0 _ => Wartet N w k s0
  | .drin _ => True
  | .gibL _ => True
  | .gibC _ ls => ls = w.serv % 18446744073709551616
  | .gibW => True
  | .weck => True

variable {N : Nat}

/-- **The invariant of the emitted lock.** -/
structure Inv (N : Nat) (σ : Zustand N) : Prop where
  nodup : σ.q.Nodup
  mem : ∀ t, t ∈ σ.q ↔ (σ.pc t).ticket.isSome = true
  tk : ∀ (i : Nat) (u : Fin N), σ.q[i]? = some u → (σ.pc u).ticket = some (σ.w.serv + i)
  next : σ.w.next = σ.w.serv + σ.q.length
  haelt : ∀ t, (σ.pc t).haelt = true → σ.q.head? = some t
  wait : σ.w.wait = σ.q.countP (fun u => (σ.pc u).gezaehlt)
  ort : ∀ t, OrtOK N σ.w (σ.pc t)
  nolost : ∀ t k s0, σ.pc t = .blockiert k s0 →
    σ.w.serv % 4294967296 = s0 % 4294967296 ∨ ∃ g, (σ.pc g).weckt = true

theorem Inv.start : Inv N (start N) := by
  refine ⟨List.nodup_nil, ?_, ?_, rfl, ?_, rfl, ?_, ?_⟩
  · intro t
    simp [Faeden.start, Ort.ticket]
  · intro i u h
    simp [Faeden.start] at h
  · intro t h
    simp [Faeden.start, Ort.haelt] at h
  · intro t
    exact trivial
  · intro t k s0 h
    simp [Faeden.start] at h

/-! ## 1. Consequences -/

theorem Inv.laenge {σ : Zustand N} (hI : Inv N σ) : σ.q.length ≤ N := by
  have h := List.Nodup.length_le_card hI.nodup
  rwa [Fintype.card_fin] at h

/-- A thread with a ticket stands in the queue at the place its ticket names. -/
theorem Inv.platz {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {k : Nat} (h : (σ.pc t).ticket = some k) :
    ∃ i, σ.q[i]? = some t ∧ k = σ.w.serv + i ∧ i < σ.q.length := by
  have hm : t ∈ σ.q := (hI.mem t).2 (by simp [h])
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
  have ht := hI.tk i t hi
  rw [h] at ht
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 hi
  exact ⟨i, hi, Option.some.inj ht, hlt⟩

/-- **Mutual exclusion**: two threads holding the lock are the same thread. -/
theorem Inv.ausschluss {σ : Zustand N} (hI : Inv N σ) {t u : Fin N} (ht : (σ.pc t).haelt = true)
    (hu : (σ.pc u).haelt = true) : t = u :=
  Option.some.inj ((hI.haelt t ht).symm.trans (hI.haelt u hu))

/-! ## 2. Counting -/

/-- Changing the predicate at one member of a list without duplicates changes the count by that member only. -/
theorem countP_upd {α : Type} (p p' : α → Bool) (t : α) (h : ∀ u, u ≠ t → p' u = p u) :
    ∀ (l : List α), l.Nodup → t ∈ l →
      l.countP p' + (if p t = true then 1 else 0) = l.countP p + (if p' t = true then 1 else 0)
  | [], _, ht => absurd ht List.not_mem_nil
  | x :: l, hl, ht => by
    rw [List.nodup_cons] at hl
    rw [List.countP_cons, List.countP_cons]
    by_cases hx : x = t
    · rw [hx] at hl
      have hc : l.countP p' = l.countP p :=
        List.countP_congr (fun u hu => by rw [h u (fun e => hl.1 (e ▸ hu))])
      rw [hc, hx]
      omega
    · have ht' : t ∈ l := by
        rcases List.mem_cons.1 ht with e | e
        · exact absurd e.symm hx
        · exact e
      have ih := countP_upd p p' t h l hl.2 ht'
      rw [h x hx]
      omega

theorem countP_auf {α : Type} {p p' : α → Bool} {t : α} (h : ∀ u, u ≠ t → p' u = p u) {l : List α}
    (hl : l.Nodup) (ht : t ∈ l) (h0 : p t = false) (h1 : p' t = true) : l.countP p' = l.countP p + 1 := by
  have := countP_upd p p' t h l hl ht
  rw [h0, h1] at this
  simpa using this

theorem countP_ab {α : Type} {p p' : α → Bool} {t : α} (h : ∀ u, u ≠ t → p' u = p u) {l : List α}
    (hl : l.Nodup) (ht : t ∈ l) (h0 : p t = true) (h1 : p' t = false) : l.countP p' + 1 = l.countP p := by
  have := countP_upd p p' t h l hl ht
  rw [h0, h1] at this
  simpa using this

/-! ## 3. The frame values against new words -/

theorem OrtOK.wort {w w' : Wort} (h : w'.serv = w.serv) : (o : Ort) → OrtOK N w o → OrtOK N w' o
  | .frei, ho => ho
  | .ladeN, ho => ho
  | .casN _, ho => ho
  | .ladeS _, ho => ho
  | .incL k s0, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    rw [h]
    exact ho
  | .incC k s0 _, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    rw [h]
    exact ho
  | .futexW k s0, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    rw [h]
    exact ho
  | .blockiert k s0, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    rw [h]
    exact ho
  | .decL k s0, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    rw [h]
    exact ho
  | .decC k s0 _, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    rw [h]
    exact ho
  | .drin _, ho => ho
  | .gibL _, ho => ho
  | .gibC _ ls, ho => by
    show ls = w'.serv % 18446744073709551616
    rw [h]
    exact ho
  | .gibW, ho => ho
  | .weck, ho => ho

/-- After `serving + 1`, the frame values of every thread that does not hold the lock still fit. -/
theorem OrtOK.succ {w w' : Wort} (h : w'.serv = w.serv + 1) :
    (o : Ort) → o.haelt = false → OrtOK N w o → OrtOK N w' o
  | .frei, _, ho => ho
  | .ladeN, _, ho => ho
  | .casN _, _, ho => ho
  | .ladeS _, _, ho => ho
  | .incL k s0, _, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    have ho' : s0 ≤ w.serv ∧ s0 < k ∧ k < s0 + N := ho
    rw [h]
    exact ⟨Nat.le_succ_of_le ho'.1, ho'.2⟩
  | .incC k s0 _, _, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    have ho' : s0 ≤ w.serv ∧ s0 < k ∧ k < s0 + N := ho
    rw [h]
    exact ⟨Nat.le_succ_of_le ho'.1, ho'.2⟩
  | .futexW k s0, _, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    have ho' : s0 ≤ w.serv ∧ s0 < k ∧ k < s0 + N := ho
    rw [h]
    exact ⟨Nat.le_succ_of_le ho'.1, ho'.2⟩
  | .blockiert k s0, _, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    have ho' : s0 ≤ w.serv ∧ s0 < k ∧ k < s0 + N := ho
    rw [h]
    exact ⟨Nat.le_succ_of_le ho'.1, ho'.2⟩
  | .decL k s0, _, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    have ho' : s0 ≤ w.serv ∧ s0 < k ∧ k < s0 + N := ho
    rw [h]
    exact ⟨Nat.le_succ_of_le ho'.1, ho'.2⟩
  | .decC k s0 _, _, ho => by
    show s0 ≤ w'.serv ∧ s0 < k ∧ k < s0 + N
    have ho' : s0 ≤ w.serv ∧ s0 < k ∧ k < s0 + N := ho
    rw [h]
    exact ⟨Nat.le_succ_of_le ho'.1, ho'.2⟩
  | .drin _, hh, _ => by simp [Ort.haelt] at hh
  | .gibL _, hh, _ => by simp [Ort.haelt] at hh
  | .gibC _ _, hh, _ => by simp [Ort.haelt] at hh
  | .gibW, _, ho => ho
  | .weck, _, ho => ho

/-! ## 4. Steps that move threads but leave `next`, `serving` and the queue -/

/-- The general case: new places `pc'` with the same tickets, a new waiter word that counts them, `next` and
    `serving` kept. -/
theorem Inv.lokal {σ : Zustand N} (hI : Inv N σ) (w' : Wort) (pc' : Fin N → Ort)
    (hn : w'.next = σ.w.next) (hs : w'.serv = σ.w.serv)
    (hT : ∀ u, (pc' u).ticket = (σ.pc u).ticket)
    (hH : ∀ u, (pc' u).haelt = true → σ.q.head? = some u)
    (hW : w'.wait = σ.q.countP (fun u => (pc' u).gezaehlt))
    (hO : ∀ u, OrtOK N w' (pc' u))
    (hL : ∀ u k s0, pc' u = .blockiert k s0 →
      w'.serv % 4294967296 = s0 % 4294967296 ∨ ∃ g, (pc' g).weckt = true) :
    Inv N ⟨w', pc', σ.q⟩ := by
  refine ⟨hI.nodup, fun t => ?_, fun i u h => ?_, ?_, hH, hW, hO, hL⟩
  · show t ∈ σ.q ↔ (pc' t).ticket.isSome = true
    rw [hT t]
    exact hI.mem t
  · show (pc' u).ticket = some (w'.serv + i)
    rw [hT u, hs]
    exact hI.tk i u h
  · show w'.next = w'.serv + σ.q.length
    rw [hn, hs]
    exact hI.next

theorem upd_eq_of {β : Type} (f : Ort → β) (pc : Fin N → Ort) (t : Fin N) (o : Ort) (h : f o = f (pc t))
    (u : Fin N) : f (upd pc t o u) = f (pc u) := by
  by_cases hu : u = t
  · rw [hu, upd_self]
    exact h
  · rw [upd_ne pc o hu]

/-- No lost wake-up survives a move of thread `t` to a place `o` where it is not blocked, as long as `t` stays a
    waker if it was one and `serving` is kept. -/
theorem Inv.nolost_upd {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {o : Ort} (hs : o.schlaeft = false)
    (hw : (σ.pc t).weckt = true → o.weckt = true) (w' : Wort) (hserv : w'.serv = σ.w.serv) :
    ∀ u k s0, upd σ.pc t o u = .blockiert k s0 →
      w'.serv % 4294967296 = s0 % 4294967296 ∨ ∃ g, (upd σ.pc t o g).weckt = true := by
  intro u k s0 hu
  by_cases h : u = t
  · rw [h, upd_self] at hu
    rw [hu] at hs
    simp [Ort.schlaeft] at hs
  · rw [upd_ne σ.pc o h] at hu
    rcases hI.nolost u k s0 hu with e | ⟨g, hg⟩
    · left
      rw [hserv]
      exact e
    · right
      by_cases hgt : g = t
      · refine ⟨t, ?_⟩
        rw [upd_self]
        rw [hgt] at hg
        exact hw hg
      · refine ⟨g, ?_⟩
        rw [upd_ne σ.pc o hgt]
        exact hg

/-- Thread `t` moves to `o` with its ticket; the waiter word `w'.wait` counts the new places. -/
theorem Inv.updW {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {o : Ort} (w' : Wort)
    (hn : w'.next = σ.w.next) (hs : w'.serv = σ.w.serv)
    (hT : o.ticket = (σ.pc t).ticket) (hH : o.haelt = true → σ.q.head? = some t)
    (hW : w'.wait = σ.q.countP (fun u => (upd σ.pc t o u).gezaehlt))
    (hO : OrtOK N w' o) (hS : o.schlaeft = false) (hK : (σ.pc t).weckt = true → o.weckt = true) :
    Inv N ⟨w', upd σ.pc t o, σ.q⟩ := by
  refine hI.lokal w' (upd σ.pc t o) hn hs (upd_eq_of Ort.ticket σ.pc t o hT) ?_ hW ?_
    (hI.nolost_upd hS hK w' hs)
  · intro u hu
    by_cases h : u = t
    · rw [h] at hu ⊢
      rw [upd_self] at hu
      exact hH hu
    · rw [upd_ne σ.pc o h] at hu
      exact hI.haelt u hu
  · intro u
    by_cases h : u = t
    · rw [h, upd_self]
      exact hO
    · rw [upd_ne σ.pc o h]
      exact OrtOK.wort hs _ (hI.ort u)

/-- The common case: a step that moves only thread `t`, keeping its ticket, its holding, its count, not into
    the futex sleep, and keeping it a waker if it was one. -/
theorem Inv.still {σ : Zustand N} (hI : Inv N σ) {t : Fin N} {p o : Ort} (hpc : σ.pc t = p)
    (hT : o.ticket = p.ticket) (hH : o.haelt = p.haelt) (hG : o.gezaehlt = p.gezaehlt)
    (hS : o.schlaeft = false) (hK : o.weckt = p.weckt) (hO : OrtOK N σ.w o) : Inv N (σ.mit t o) := by
  subst hpc
  have hf : (fun u => (upd σ.pc t o u).gezaehlt) = (fun u => (σ.pc u).gezaehlt) :=
    funext (upd_eq_of Ort.gezaehlt σ.pc t o hG)
  refine hI.updW σ.w rfl rfl hT (fun hh => hI.haelt t (by rw [← hH]; exact hh)) ?_ hO hS
    (fun hk => by rw [hK]; exact hk)
  rw [hf]
  exact hI.wait

end Gabbro.Stage0.Senke.Faeden
