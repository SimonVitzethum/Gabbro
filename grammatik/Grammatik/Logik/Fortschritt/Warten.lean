/-
  File:      Grammatik/Logik/Fortschritt/Warten.lean
  Subject:   THE WAITING BOUND, DEFINITIONS ONLY (moved out of Lebendigkeit/T1.lean on 2026-10-23 so that the goal
             statement can read them): counting on a run, the bound `wartezeit` recursive over ranks, and the named
             premises of a run -- the FIFO lock, bounded fairness, the hold time, the contenders. The theorems are in
             Lebendigkeit.lean; the statement `GabbroZielWarten` in Zielsatz/Kern/Spec.lean.
-/
import Grammatik.Logik.Fortschritt.PlanLauf

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Counting on a run -/

open Classical in
/-- The number of `j ∈ [a, a + n)` with `p j`. -/
noncomputable def zaehl (p : Nat → Prop) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => zaehl p a n + if p (a + n) then 1 else 0

/-! ## 2. The bound, recursive over ranks -/

/-- The largest `f L'` over the locks of `ls` ranking above `L` (`0` if none). -/
def wMaxH (L : D.Lock) (f : D.Lock → Nat) : List D.Lock → Nat
  | [] => 0
  | a :: l => max (if D.rang L < D.rang a then f a else 0) (wMaxH L f l)

/-- **The waiting bound with fuel `n`** (the fuel counts rank levels):
    `wF (n+1) L = (c L - 1) * (h L * F + k L * Wn + F) + F`, where `Wn` is
    the largest bound one fuel level down over the locks ranking above `L`
    and `c L = (Ts L).length` the number of contenders. -/
def wF (ls : List D.Lock) (Ts : D.Lock → List Faden) (h k : D.Lock → Nat) (F : Nat) :
    Nat → D.Lock → Nat
  | 0, _ => 0
  | n + 1, L =>
      ((Ts L).length - 1) * (h L * F + k L * wMaxH L (wF ls Ts h k F n) ls + F) + F

/-- **The waiting bound**: `wF` at fuel `ls.length` (enough: every chain of
    strictly rising ranks in `ls` is shorter). -/
def wartezeit (ls : List D.Lock) (Ts : D.Lock → List Faden) (h k : D.Lock → Nat) (F : Nat)
    (L : D.Lock) : Nat :=
  wF ls Ts h k F ls.length L

/-! ## 3. The premises of a run -/

section Annahmen

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **A FIFO (ticket) lock.** If thread `t` stands at `locks L` at every
    scheduler step from `a` to `n`, and thread `u` takes `L` at step `n`
    (it acts standing at `locks L`), then `u` has stood there since `a`
    too: nobody overtakes a waiting thread. -/
def FifoSperre (R : PlanLauf P O passes) : Prop :=
  ∀ (t u : Faden) (L : D.Lock) (a n : Nat), t ≠ u →
    (∀ j, a ≤ j → j ≤ n → AnSperre (R.M j) t L) →
    R.akt n = some u → AnSperre (R.M n) u L →
    ∀ j, a ≤ j → j ≤ n → AnSperre (R.M j) u L

/-- **Bounded fairness with window `F`.** A thread that can step at each of
    the `F` scheduler steps from `n` on takes one of them. (`F = 0` is
    unsatisfiable: the window is empty.) -/
def FairF (R : PlanLauf P O passes) (F : Nat) : Prop :=
  ∀ (t : Faden) (n : Nat), (∀ j, n ≤ j → j < n + F → Bereit P O passes (R.M j) t) →
    ∃ j, n ≤ j ∧ j < n + F ∧ R.akt j = some t

/-- **THE RUNTIME ASSUMPTION for the waiting bound** -- the entry "a FIFO or
    ticket lock for the waiting bound" of the ONE assumption list
    (PLAN-ZIELSATZ §8), together with the scheduler's fairness window `F`. -/
def LaufzeitAnnahme (R : PlanLauf P O passes) (F : Nat) : Prop :=
  FifoSperre R ∧ FairF R F

/-- **The hold-time premise.** On every stretch of `n` scheduler steps from
    `a` on which thread `u` holds `L`, `u` takes at most `h L` own steps, at
    most `k L` of them at a `locks` head. -/
def Haltezeit (R : PlanLauf P O passes) (h k : D.Lock → Nat) : Prop :=
  ∀ (u : Faden) (L : D.Lock) (a n : Nat),
    (∀ i, i < n → L ∈ offen ((R.M (a + i)).faeden u).spur) →
    zaehl (fun j => R.akt j = some u) a n ≤ h L ∧
    zaehl (fun j => R.akt j = some u ∧ ∃ L', AnSperre (R.M j) u L') a n ≤ k L

/-- **The contenders for `L`**: every thread that ever holds `L` or stands
    at `locks L` on the run is in `Ts L`. -/
def Anwaerter (R : PlanLauf P O passes) (Ts : D.Lock → List Faden) : Prop :=
  ∀ n u L, (L ∈ offen ((R.M n).faeden u).spur ∨ AnSperre (R.M n) u L) → u ∈ Ts L

end Annahmen

end Gabbro.Grammatik
