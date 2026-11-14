/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Potential.lean
  Subject:   Two potentials of a thread of the emitted lock, used by the liveness proof while the serving counter
             stays at `s`:
             * `Ort.chi` -- a pending waker (2 before its waiter test, 1 before its FUTEX_WAKE): it never grows while
               `serving` stays (a thread becomes a waker only by advancing `serving`), and drops at every WAKE;
             * `Ort.psi s` -- the steps on the waiter word a thread can still make: it never grows while `serving`
               stays at `s`, nobody returns spuriously, wakes or enters, and drops at every successful `cas` on the
               waiter word. A thread that loaded `serving = s` (`s0 = s`) blocks for good in FUTEX_WAIT; one that
               loaded an older value returns from FUTEX_WAIT at once and loads `serving` again.
             So, finitely often each: WAKEs, and then changes of the waiter word.
-/
module
public import Stage0.Senke.Sperre.Faeden.Rahmen
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

variable {N : Nat}

/-- Pending wakers. -/
def Ort.chi : Ort → Nat
  | .frei => 0
  | .ladeN => 0
  | .casN _ => 0
  | .ladeS _ => 0
  | .incL _ _ => 0
  | .incC _ _ _ => 0
  | .futexW _ _ => 0
  | .blockiert _ _ => 0
  | .decL _ _ => 0
  | .decC _ _ _ => 0
  | .drin _ => 0
  | .gibL _ => 0
  | .gibC _ _ => 0
  | .gibW => 2
  | .weck => 1

/-- The waiter-word steps a thread can still make while `serving` stays at `s`. -/
def Ort.psi (s : Nat) : Ort → Nat
  | .frei => 10
  | .ladeN => 10
  | .casN _ => 10
  | .ladeS _ => 4
  | .incL _ s0 => if s0 = s then 3 else 8
  | .incC _ s0 _ => if s0 = s then 3 else 8
  | .futexW _ s0 => if s0 = s then 2 else 7
  | .blockiert _ s0 => if s0 = s then 1 else 7
  | .decL _ _ => 6
  | .decC _ _ _ => 6
  | .drin _ => 10
  | .gibL _ => 10
  | .gibC _ _ => 10
  | .gibW => 10
  | .weck => 10

theorem chi_geweckt (o : Ort) : o.geweckt.chi = o.chi := by cases o <;> rfl

/-! ## 1. Pending wakers -/

theorem Schritt.chi_selbst {σ σ' : Zustand N} {t : Fin N} (hI : Inv N σ) (hs : Schritt σ t σ')
    (hserv : σ'.w.serv = σ.w.serv) :
    (σ'.pc t).chi ≤ (σ.pc t).chi ∧ (σ.pc t = .weck → (σ'.pc t).chi < (σ.pc t).chi) := by
  cases hs with
  | gibt h e =>
    exfalso
    have h2 : σ.w.serv + 1 = σ.w.serv := hserv
    omega
  | gibtNicht h e => exact absurd (show _ = _ from hI.ort_an h).symm e
  | ruht h => exact ⟨Nat.le_refl _, fun hw => by rw [h] at hw; cases hw⟩
  | arbeitet h => exact ⟨Nat.le_refl _, fun hw => by rw [h] at hw; cases hw⟩
  | weckt h => simp [upd_self, h, Ort.chi]
  | _ => simp_all [Zustand.mit, upd_self, Ort.chi]

/-- While `serving` stays, no thread's waker potential grows, and the WAKE of a thread drops its own. -/
theorem Schritt.chi {σ σ' : Zustand N} {t u : Fin N} (hI : Inv N σ) (hs : Schritt σ t σ')
    (hserv : σ'.w.serv = σ.w.serv) :
    (σ'.pc u).chi ≤ (σ.pc u).chi ∧ (t = u → σ.pc u = .weck → (σ'.pc u).chi < (σ.pc u).chi) := by
  by_cases hu : u = t
  · subst hu
    have hc := Schritt.chi_selbst hI hs hserv
    exact ⟨hc.1, fun _ => hc.2⟩
  · refine ⟨?_, fun e => absurd e.symm hu⟩
    rcases hs.andere hu with e | e
    · exact Nat.le_of_eq (by rw [e])
    · exact Nat.le_of_eq (by rw [e, chi_geweckt])

/-! ## 2. Steps on the waiter word -/

theorem Schritt.psi_selbst {σ σ' : Zustand N} {t : Fin N} (s : Nat) (hs : Schritt σ t σ')
    (h1 : σ.w.serv = s) (h2 : σ'.w.serv = s) (hS : (σ.pc t).schlaeft = false) (hW : σ.pc t ≠ .weck)
    (hT : (σ'.pc t).haelt = true → (σ.pc t).haelt = true) :
    (σ'.pc t).psi s ≤ (σ.pc t).psi s ∧ (σ'.w.wait ≠ σ.w.wait → (σ'.pc t).psi s < (σ.pc t).psi s) := by
  cases hs with
  | beginnt h => simp [Zustand.mit, upd_self, h, Ort.psi]
  | ruht h => exact ⟨Nat.le_refl _, fun hw => absurd rfl hw⟩
  | liestN h => simp [Zustand.mit, upd_self, h, Ort.psi]
  | zieht h e => simp [upd_self, h, Ort.psi]
  | verfehlt h e => simp [Zustand.mit, upd_self, h, Ort.psi]
  | tritt h e =>
    exfalso
    have hx := hT (by simp [Zustand.mit, upd_self, Ort.haelt])
    simp [h, Ort.haelt] at hx
  | wartet h e => simp [Zustand.mit, upd_self, h, h1, Ort.psi]
  | liestInc h => simp [Zustand.mit, upd_self, h, Ort.psi]
  | @erhoeht k s0 lw h e =>
    by_cases hs0 : s0 = s <;> simp [upd_self, h, hs0, Ort.psi]
  | erhoehtNicht h e => simp [Zustand.mit, upd_self, h, Ort.psi]
  | @schlaeft k s0 h e =>
    by_cases hs0 : s0 = s <;> simp [Zustand.mit, upd_self, h, hs0, Ort.psi]
  | @kehrtZurueck k s0 h e =>
    by_cases hs0 : s0 = s
    · exact absurd (by rw [h1, hs0]) e
    · simp [Zustand.mit, upd_self, h, hs0, Ort.psi]
  | scheinbar h =>
    exfalso
    simp [h, Ort.schlaeft] at hS
  | liestDec h => simp [Zustand.mit, upd_self, h, Ort.psi]
  | senkt h e => simp [upd_self, h, Ort.psi]
  | senktNicht h e => simp [Zustand.mit, upd_self, h, Ort.psi]
  | arbeitet h => exact ⟨Nat.le_refl _, fun hw => absurd rfl hw⟩
  | verlaesst h => simp [Zustand.mit, upd_self, h, Ort.psi]
  | liestGib h => simp [Zustand.mit, upd_self, h, Ort.psi]
  | gibt h e =>
    exfalso
    have h2' : σ.w.serv + 1 = s := h2
    omega
  | gibtNicht h e => simp [Zustand.mit, upd_self, h, Ort.psi]
  | keinWarter h e => simp [Zustand.mit, upd_self, h, Ort.psi]
  | warter h e => simp [Zustand.mit, upd_self, h, Ort.psi]
  | weckt h => exact absurd h hW

/-- **The waiter-word potential**: while `serving` stays at `s` and the stepping thread is neither blocked (no
    spurious return) nor at its WAKE nor entering, no thread's potential grows, and a change of the waiter word
    by a thread drops its own. -/
theorem Schritt.psi {σ σ' : Zustand N} {t u : Fin N} (s : Nat) (hs : Schritt σ t σ')
    (h1 : σ.w.serv = s) (h2 : σ'.w.serv = s) (hS : (σ.pc t).schlaeft = false) (hW : σ.pc t ≠ .weck)
    (hT : (σ'.pc t).haelt = true → (σ.pc t).haelt = true) :
    (σ'.pc u).psi s ≤ (σ.pc u).psi s ∧
      (t = u → σ'.w.wait ≠ σ.w.wait → (σ'.pc u).psi s < (σ.pc u).psi s) := by
  by_cases hu : u = t
  · subst hu
    have hc := Schritt.psi_selbst s hs h1 h2 hS hW hT
    exact ⟨hc.1, fun _ => hc.2⟩
  · have e := hs.andere_fest hu hW
    rw [e]
    exact ⟨Nat.le_refl _, fun htu => absurd htu.symm hu⟩

end Gabbro.Stage0.Senke.Faeden
