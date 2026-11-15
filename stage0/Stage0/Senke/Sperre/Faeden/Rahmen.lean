/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Rahmen.lean
  Subject:   What ONE step of the emitted lock (Faeden/Maschine.lean) does: to the threads that do not step (they
             stay, or a FUTEX_WAKE wakes them), to the serving counter (it only grows), to a holder and a ticket
             while `serving` stays, to a thread waiting with its ticket; and the inversions -- what the step of a
             thread at each place of the waiting and give paths is -- that the liveness proof walks along.
-/
module
public import Stage0.Senke.Sperre.Faeden.InvLauf
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

variable {N : Nat}

/-- Thread with ticket `k` that does not hold the lock: it waits for it. -/
def WartetMit (k : Nat) (o : Ort) : Prop := o.ticket = some k ∧ o.haelt = false

theorem geweckt_fest {o : Ort} (h : o.schlaeft = false) : o.geweckt = o := by
  cases o with
  | blockiert k s0 => simp [Ort.schlaeft] at h
  | _ => rfl

theorem weckt_ort {o : Ort} (h : o.weckt = true) : o = .gibW ∨ o = .weck := by
  cases o with
  | gibW => exact Or.inl rfl
  | weck => exact Or.inr rfl
  | _ => simp [Ort.weckt] at h

/-! ## 1. The threads that do not step -/

/-- A thread that does not step stays, or is woken by the FUTEX_WAKE of the stepping thread. -/
theorem Schritt.andere {σ σ' : Zustand N} {t v : Fin N} (hs : Schritt σ t σ') (hv : v ≠ t) :
    σ'.pc v = σ.pc v ∨ σ'.pc v = (σ.pc v).geweckt := by
  cases hs with
  | weckt h =>
    right
    simp [upd, wecke, hv]
  | _ =>
    left
    simp [Zustand.mit, upd, hv]

/-- Unless the stepping thread makes its FUTEX_WAKE, the other threads stay. -/
theorem Schritt.andere_fest {σ σ' : Zustand N} {t v : Fin N} (hs : Schritt σ t σ') (hv : v ≠ t)
    (hw : σ.pc t ≠ .weck) : σ'.pc v = σ.pc v := by
  cases hs with
  | weckt h => exact absurd h hw
  | _ => simp [Zustand.mit, upd, hv]

/-! ## 2. The serving counter, a holder, a ticket -/

/-- The serving counter never decreases. -/
theorem Schritt.serv_le {σ σ' : Zustand N} {t : Fin N} (hs : Schritt σ t σ') : σ.w.serv ≤ σ'.w.serv := by
  cases hs <;> first | exact Nat.le_refl _ | exact Nat.le_succ _

/-- A thread that does not hold the lock and holds it after its own step entered it: the serving word showed
    its ticket. -/
theorem Schritt.wird_haelt {σ σ' : Zustand N} {v : Fin N} (hs : Schritt σ v σ') (h0 : (σ.pc v).haelt = false)
    (h1 : (σ'.pc v).haelt = true) :
    ∃ k, σ.pc v = .ladeS k ∧ σ.w.serv % 18446744073709551616 = k % 18446744073709551616 := by
  cases hs with
  | tritt h e => exact ⟨_, h, e⟩
  | _ => simp_all [Zustand.mit, upd, Ort.haelt]

/-- A holder keeps the lock over every step that leaves `serving`. -/
theorem Schritt.haelt_bleibt {σ σ' : Zustand N} {t h : Fin N} (hI : Inv N σ) (hs : Schritt σ t σ')
    (hh : (σ.pc h).haelt = true) (hserv : σ'.w.serv = σ.w.serv) : (σ'.pc h).haelt = true := by
  have hO := hI.ort h
  by_cases hth : h = t
  · subst hth
    cases hs <;> simp_all [Zustand.mit, upd, Ort.haelt, OrtOK]
  · rcases hs.andere hth with e | e
    · rw [e]
      exact hh
    · rw [e, geweckt_haelt]
      exact hh

/-- A ticket stays over every step that leaves `serving`. -/
theorem Schritt.ticket_bleibt {σ σ' : Zustand N} {t h : Fin N} (hI : Inv N σ) (hs : Schritt σ t σ') {k : Nat}
    (hk : (σ.pc h).ticket = some k) (hserv : σ'.w.serv = σ.w.serv) : (σ'.pc h).ticket = some k := by
  have hO := hI.ort h
  by_cases hth : h = t
  · subst hth
    cases hs <;> simp_all [Zustand.mit, upd, Ort.ticket, OrtOK]
  · rcases hs.andere hth with e | e
    · rw [e]
      exact hk
    · rw [e, geweckt_ticket]
      exact hk

/-- A thread waiting with ticket `k` still waits with it after any step, or it entered. -/
theorem Schritt.wartetMit {σ σ' : Zustand N} {u t : Fin N} (hs : Schritt σ u σ') {k : Nat}
    (hw : WartetMit k (σ.pc t)) : WartetMit k (σ'.pc t) ∨ σ'.pc t = .drin k := by
  by_cases htu : t = u
  · subst htu
    cases hs <;> simp_all [WartetMit, Zustand.mit, upd, Ort.ticket, Ort.haelt]
  · left
    rcases hs.andere htu with e | e
    · rw [e]
      exact hw
    · rw [e]
      exact ⟨by rw [geweckt_ticket]; exact hw.1, by rw [geweckt_haelt]; exact hw.2⟩

/-! ## 3. Inversions: the step of a thread at a place of the waiting and give paths -/

section Inversion

variable {σ σ' : Zustand N} {t : Fin N}

theorem Schritt.von_ladeS (hs : Schritt σ t σ') {k : Nat} (h : σ.pc t = .ladeS k) :
    σ'.pc t = .drin k ∨
      (σ.w.serv % 18446744073709551616 ≠ k % 18446744073709551616 ∧ σ'.pc t = .incL k σ.w.serv) := by
  cases hs <;> simp_all [Zustand.mit, upd]

theorem Schritt.von_incL (hs : Schritt σ t σ') {k s0 : Nat} (h : σ.pc t = .incL k s0) :
    σ'.pc t = .incC k s0 σ.w.wait := by
  cases hs <;> simp_all [Zustand.mit, upd]

theorem Schritt.von_incC (hs : Schritt σ t σ') {k s0 lw : Nat} (h : σ.pc t = .incC k s0 lw) :
    (σ.w.wait = lw ∧ σ'.w.wait = (lw + 1) % 18446744073709551616) ∨
      (σ.w.wait ≠ lw ∧ σ'.pc t = .incL k s0) := by
  cases hs <;> simp_all [Zustand.mit, upd]

theorem Schritt.von_futexW (hs : Schritt σ t σ') {k s0 : Nat} (h : σ.pc t = .futexW k s0) :
    σ.w.serv % 4294967296 = s0 % 4294967296 ∨ σ'.pc t = .decL k s0 := by
  cases hs <;> simp_all [Zustand.mit, upd]

theorem Schritt.von_decL (hs : Schritt σ t σ') {k s0 : Nat} (h : σ.pc t = .decL k s0) :
    σ'.pc t = .decC k s0 σ.w.wait := by
  cases hs <;> simp_all [Zustand.mit, upd]

theorem Schritt.von_decC (hs : Schritt σ t σ') {k s0 lw : Nat} (h : σ.pc t = .decC k s0 lw) :
    (σ.w.wait = lw ∧ σ'.w.wait = wrapDec lw) ∨
      (σ.w.wait ≠ lw ∧ σ'.pc t = .decL k s0) := by
  cases hs <;> simp_all [Zustand.mit, upd]

theorem Schritt.von_gibW (hs : Schritt σ t σ') (h : σ.pc t = .gibW) :
    (σ.w.wait = 0 ∧ σ'.pc t = .frei) ∨ (σ.w.wait ≠ 0 ∧ σ'.pc t = .weck) := by
  cases hs <;> simp_all [Zustand.mit, upd]

end Inversion

end Gabbro.Stage0.Senke.Faeden
