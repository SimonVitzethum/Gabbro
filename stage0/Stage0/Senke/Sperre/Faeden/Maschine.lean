/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Maschine.lean
  Subject:   THE EMITTED TICKET LOCK RUN BY MANY THREADS, at the granularity of its shared-word accesses, with a
             futex that BLOCKS. The runner's futex model (`Runner.IR.FutexOK`) only classifies the return of one
             thread's WAIT; it has no blocked threads, no WAKE that releases them and no interleaving of threads.
             This machine is that missing piece, stated as a named model of the environment (the OS futex), never
             as a hardware assumption:
             * one step of a thread is ONE access of the emitted code (`nimmT`, `gibT` in Ticket/Code.lean) to one
               of the three lock words -- a load, a `cas` (one `lock cmpxchg`), the WAIT or the WAKE request --
               together with the frame-local instructions around it (they touch no shared word; the table at the
               end pins every step to its instruction index);
             * FUTEX_WAIT on the serving word with value `v` compares the low 32 bits of the word with `v`
               ATOMICALLY with going to sleep: unequal returns at once (`kehrtZurueck`), equal blocks
               (`schlaeft`); a blocked thread may return at any time (`scheinbar`: spurious wake-ups, signals);
             * FUTEX_WAKE with count 2147483647 (the emitted constant) wakes EVERY thread blocked on the word
               (`weckt`; the machine has fewer threads than that, `Inv.schritt` takes `N ≤ 2147483647`); a woken
               thread continues at the decrement of the waiter count, as after any return of WAIT.
             The words `next` and `serving` are kept as unbounded GHOST counters: the word in memory is the counter
             modulo 2^64, and every test of the code compares words (`% 18446744073709551616`; the futex compares
             `% 4294967296`). The waiter word is kept as the word itself. The queue `q` of ticket holders in
             ticket order is ghost state: it never steers a step.
-/
module
public import Stage0.Senke.Sperre.Ticket.Code
public import Stage0.Senke.Sperre.Faeden.Abstrakt
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

/-- **Where a thread stands in the code of ONE lock**, with the values it holds in its frame: its ticket `k`
    (ghost: the counter whose word is the ticket register), the serving value `s0` it loaded before waiting
    (ghost counter of the word it passes to WAIT), and a loaded word `l`/`lw`/`ls` before a `cas`. -/
inductive Ort where
  /-- Outside the lock code, not holding the lock. -/
  | frei
  /-- `nimmT` index 1: load `next`. -/
  | ladeN
  /-- `nimmT` index 4: `cas` on `next` with the loaded word `l`. -/
  | casN (l : Nat)
  /-- `nimmT` index 8: load `serving`, ticket `k`. -/
  | ladeS (k : Nat)
  /-- `nimmT` index 13: load the waiter word before `waiters + 1`. -/
  | incL (k s0 : Nat)
  /-- `nimmT` index 16: `cas` on the waiter word with the loaded word `lw`. -/
  | incC (k s0 lw : Nat)
  /-- `nimmT` index 26: FUTEX_WAIT on `serving` with the loaded serving word. -/
  | futexW (k s0 : Nat)
  /-- Blocked in FUTEX_WAIT. -/
  | blockiert (k s0 : Nat)
  /-- `nimmT` index 28: load the waiter word before `waiters - 1`. -/
  | decL (k s0 : Nat)
  /-- `nimmT` index 31: `cas` on the waiter word with the loaded word `lw`. -/
  | decC (k s0 lw : Nat)
  /-- `nimmT` index 35: the guarded body. -/
  | drin (k : Nat)
  /-- `gibT` index 1: load `serving`. -/
  | gibL (k : Nat)
  /-- `gibT` index 4: `cas` on `serving` with the loaded word `ls`. -/
  | gibC (k ls : Nat)
  /-- `gibT` index 6: load the waiter word; zero ends the give. -/
  | gibW
  /-- `gibT` index 15: FUTEX_WAKE of all waiters. -/
  | weck
  deriving DecidableEq

/-- The ticket a thread holds (from its draw to its release). -/
def Ort.ticket : Ort → Option Nat
  | .frei => none
  | .ladeN => none
  | .casN _ => none
  | .ladeS k => some k
  | .incL k _ => some k
  | .incC k _ _ => some k
  | .futexW k _ => some k
  | .blockiert k _ => some k
  | .decL k _ => some k
  | .decC k _ _ => some k
  | .drin k => some k
  | .gibL k => some k
  | .gibC k _ => some k
  | .gibW => none
  | .weck => none

/-- The thread holds the lock (from its enter to its release `cas`). -/
def Ort.haelt : Ort → Bool
  | .frei => false
  | .ladeN => false
  | .casN _ => false
  | .ladeS _ => false
  | .incL _ _ => false
  | .incC _ _ _ => false
  | .futexW _ _ => false
  | .blockiert _ _ => false
  | .decL _ _ => false
  | .decC _ _ _ => false
  | .drin _ => true
  | .gibL _ => true
  | .gibC _ _ => true
  | .gibW => false
  | .weck => false

/-- The thread is counted in the waiter word (from its increment to its decrement). -/
def Ort.gezaehlt : Ort → Bool
  | .frei => false
  | .ladeN => false
  | .casN _ => false
  | .ladeS _ => false
  | .incL _ _ => false
  | .incC _ _ _ => false
  | .futexW _ _ => true
  | .blockiert _ _ => true
  | .decL _ _ => true
  | .decC _ _ _ => true
  | .drin _ => false
  | .gibL _ => false
  | .gibC _ _ => false
  | .gibW => false
  | .weck => false

/-- The thread is blocked in FUTEX_WAIT. -/
def Ort.schlaeft : Ort → Bool
  | .frei => false
  | .ladeN => false
  | .casN _ => false
  | .ladeS _ => false
  | .incL _ _ => false
  | .incC _ _ _ => false
  | .futexW _ _ => false
  | .blockiert _ _ => true
  | .decL _ _ => false
  | .decC _ _ _ => false
  | .drin _ => false
  | .gibL _ => false
  | .gibC _ _ => false
  | .gibW => false
  | .weck => false

/-- The thread is a pending waker: it advanced `serving` and has not yet done its WAKE. -/
def Ort.weckt : Ort → Bool
  | .frei => false
  | .ladeN => false
  | .casN _ => false
  | .ladeS _ => false
  | .incL _ _ => false
  | .incC _ _ _ => false
  | .futexW _ _ => false
  | .blockiert _ _ => false
  | .decL _ _ => false
  | .decC _ _ _ => false
  | .drin _ => false
  | .gibL _ => false
  | .gibC _ _ => false
  | .gibW => true
  | .weck => true

/-- FUTEX_WAKE: a blocked thread returns from WAIT to the decrement of the waiter count. -/
def Ort.geweckt : Ort → Ort
  | .frei => .frei
  | .ladeN => .ladeN
  | .casN l => .casN l
  | .ladeS k => .ladeS k
  | .incL k s0 => .incL k s0
  | .incC k s0 lw => .incC k s0 lw
  | .futexW k s0 => .futexW k s0
  | .blockiert k s0 => .decL k s0
  | .decL k s0 => .decL k s0
  | .decC k s0 lw => .decC k s0 lw
  | .drin k => .drin k
  | .gibL k => .gibL k
  | .gibC k ls => .gibC k ls
  | .gibW => .gibW
  | .weck => .weck

/-- The three words of the lock: `next` and `serving` as ghost counters, the waiter word as a word. -/
structure Wort where
  next : Nat
  serv : Nat
  wait : Nat
  deriving DecidableEq

/-- The state of one lock and `N` threads. -/
structure Zustand (N : Nat) where
  w : Wort
  pc : Fin N → Ort
  q : List (Fin N)

variable {N : Nat}

/-- Thread `t` moves to `o`. -/
def upd (pc : Fin N → Ort) (t : Fin N) (o : Ort) : Fin N → Ort := fun u => if u = t then o else pc u

theorem upd_self (pc : Fin N → Ort) (t : Fin N) (o : Ort) : upd pc t o t = o := by
  simp [upd]

theorem upd_ne (pc : Fin N → Ort) {t u : Fin N} (o : Ort) (h : u ≠ t) : upd pc t o u = pc u := by
  simp [upd, h]

/-- Only the place of thread `t` changes. -/
def Zustand.mit (σ : Zustand N) (t : Fin N) (o : Ort) : Zustand N := ⟨σ.w, upd σ.pc t o, σ.q⟩

/-- All threads blocked on the serving word are woken. -/
def wecke (pc : Fin N → Ort) : Fin N → Ort := fun u => (pc u).geweckt

theorem wecke_apply (pc : Fin N → Ort) (u : Fin N) : wecke pc u = (pc u).geweckt := rfl

/-- The waiter word after a successful decrement: minus one, wrapping at 2^64. Defined by cases so
    that the kernel never unfolds the literal addition on a variable (`wrapDec_eq` gives the closed form). -/
def wrapDec : Nat → Nat
  | 0 => 18446744073709551615
  | n + 1 => n % 18446744073709551616

theorem wrapDec_eq (lw : Nat) : wrapDec lw = (lw + 18446744073709551615) % 18446744073709551616 := by
  cases lw with
  | zero => rfl
  | succ n =>
    show n % 18446744073709551616 = (n + 1 + 18446744073709551615) % 18446744073709551616
    omega

/-- **One step of thread `t`.** -/
inductive Schritt : Zustand N → Fin N → Zustand N → Prop where
  | beginnt {σ : Zustand N} {t : Fin N} : σ.pc t = .frei → Schritt σ t (σ.mit t .ladeN)
  | ruht {σ : Zustand N} {t : Fin N} : σ.pc t = .frei → Schritt σ t σ
  | liestN {σ : Zustand N} {t : Fin N} : σ.pc t = .ladeN →
      Schritt σ t (σ.mit t (.casN (σ.w.next % 18446744073709551616)))
  | zieht {σ : Zustand N} {t : Fin N} {l : Nat} : σ.pc t = .casN l →
      σ.w.next % 18446744073709551616 = l →
      Schritt σ t ⟨⟨σ.w.next + 1, σ.w.serv, σ.w.wait⟩, upd σ.pc t (.ladeS σ.w.next), σ.q ++ [t]⟩
  | verfehlt {σ : Zustand N} {t : Fin N} {l : Nat} : σ.pc t = .casN l →
      σ.w.next % 18446744073709551616 ≠ l → Schritt σ t (σ.mit t .ladeN)
  | tritt {σ : Zustand N} {t : Fin N} {k : Nat} : σ.pc t = .ladeS k →
      σ.w.serv % 18446744073709551616 = k % 18446744073709551616 → Schritt σ t (σ.mit t (.drin k))
  | wartet {σ : Zustand N} {t : Fin N} {k : Nat} : σ.pc t = .ladeS k →
      σ.w.serv % 18446744073709551616 ≠ k % 18446744073709551616 →
      Schritt σ t (σ.mit t (.incL k σ.w.serv))
  | liestInc {σ : Zustand N} {t : Fin N} {k s0 : Nat} : σ.pc t = .incL k s0 →
      Schritt σ t (σ.mit t (.incC k s0 σ.w.wait))
  | erhoeht {σ : Zustand N} {t : Fin N} {k s0 lw : Nat} : σ.pc t = .incC k s0 lw → σ.w.wait = lw →
      Schritt σ t ⟨⟨σ.w.next, σ.w.serv, (lw + 1) % 18446744073709551616⟩, upd σ.pc t (.futexW k s0), σ.q⟩
  | erhoehtNicht {σ : Zustand N} {t : Fin N} {k s0 lw : Nat} : σ.pc t = .incC k s0 lw → σ.w.wait ≠ lw →
      Schritt σ t (σ.mit t (.incL k s0))
  | schlaeft {σ : Zustand N} {t : Fin N} {k s0 : Nat} : σ.pc t = .futexW k s0 →
      σ.w.serv % 4294967296 = s0 % 4294967296 → Schritt σ t (σ.mit t (.blockiert k s0))
  | kehrtZurueck {σ : Zustand N} {t : Fin N} {k s0 : Nat} : σ.pc t = .futexW k s0 →
      σ.w.serv % 4294967296 ≠ s0 % 4294967296 → Schritt σ t (σ.mit t (.decL k s0))
  | scheinbar {σ : Zustand N} {t : Fin N} {k s0 : Nat} : σ.pc t = .blockiert k s0 →
      Schritt σ t (σ.mit t (.decL k s0))
  | liestDec {σ : Zustand N} {t : Fin N} {k s0 : Nat} : σ.pc t = .decL k s0 →
      Schritt σ t (σ.mit t (.decC k s0 σ.w.wait))
  | senkt {σ : Zustand N} {t : Fin N} {k s0 lw : Nat} : σ.pc t = .decC k s0 lw → σ.w.wait = lw →
      Schritt σ t ⟨⟨σ.w.next, σ.w.serv, wrapDec lw⟩,
        upd σ.pc t (.ladeS k), σ.q⟩
  | senktNicht {σ : Zustand N} {t : Fin N} {k s0 lw : Nat} : σ.pc t = .decC k s0 lw → σ.w.wait ≠ lw →
      Schritt σ t (σ.mit t (.decL k s0))
  | arbeitet {σ : Zustand N} {t : Fin N} {k : Nat} : σ.pc t = .drin k → Schritt σ t σ
  | verlaesst {σ : Zustand N} {t : Fin N} {k : Nat} : σ.pc t = .drin k → Schritt σ t (σ.mit t (.gibL k))
  | liestGib {σ : Zustand N} {t : Fin N} {k : Nat} : σ.pc t = .gibL k →
      Schritt σ t (σ.mit t (.gibC k (σ.w.serv % 18446744073709551616)))
  | gibt {σ : Zustand N} {t : Fin N} {k ls : Nat} : σ.pc t = .gibC k ls →
      σ.w.serv % 18446744073709551616 = ls →
      Schritt σ t ⟨⟨σ.w.next, σ.w.serv + 1, σ.w.wait⟩, upd σ.pc t .gibW, σ.q.tail⟩
  | gibtNicht {σ : Zustand N} {t : Fin N} {k ls : Nat} : σ.pc t = .gibC k ls →
      σ.w.serv % 18446744073709551616 ≠ ls → Schritt σ t (σ.mit t .gibW)
  | keinWarter {σ : Zustand N} {t : Fin N} : σ.pc t = .gibW → σ.w.wait = 0 → Schritt σ t (σ.mit t .frei)
  | warter {σ : Zustand N} {t : Fin N} : σ.pc t = .gibW → σ.w.wait ≠ 0 → Schritt σ t (σ.mit t .weck)
  | weckt {σ : Zustand N} {t : Fin N} : σ.pc t = .weck → Schritt σ t ⟨σ.w, upd (wecke σ.pc) t .frei, σ.q⟩

/-- The lock at the start: all words zero, every thread outside. -/
def start (N : Nat) : Zustand N := ⟨⟨0, 0, 0⟩, fun _ => .frei, []⟩

/-- **A run of the lock**: at every scheduler step one thread steps, or nothing changes. -/
structure Lauf (N : Nat) where
  z : Nat → Zustand N
  akt : Nat → Option (Fin N)
  schritt : ∀ n t, akt n = some t → Schritt (z n) t (z (n + 1))
  stotter : ∀ n, akt n = none → z (n + 1) = z n

/-- A thread can be scheduled: it is not blocked in FUTEX_WAIT. -/
def Bereit (σ : Zustand N) (t : Fin N) : Prop := (σ.pc t).schlaeft = false

/-- **Weak fairness of the scheduler over the threads that are not blocked**: a thread that is not blocked at
    every step from `n` on takes a step. A blocked thread is never required to step; its spurious returns are
    allowed, never demanded. -/
def Lauf.Fair (R : Lauf N) : Prop :=
  ∀ (t : Fin N) (n : Nat), (∀ j, n ≤ j → Bereit (R.z j) t) → ∃ j, n ≤ j ∧ R.akt j = some t

/-! ## The steps are the emitted instructions

    The shared accesses of `nimmT`/`gibT` at the indices the steps name: the word address (`a` = next,
    `a + 8` = serving, `a + 16` = waiters) is loaded into scratch slot `s + 1` (or `s + 7`) just before. -/

section Code

open Gabbro.Grammatik

variable {D : Deklaration} (L : Lay D) (a s : Nat)

theorem nimmT_ladeN : (nimmT L a s)[0]? = some (ci 1 ((s + 1 : Nat) : Int) a 0) ∧
    (nimmT L a s)[1]? = some (ci 15 ((s + 2 : Nat) : Int) ((s + 1 : Nat) : Int) 0) :=
  ⟨rfl, rfl⟩

theorem nimmT_casN : (nimmT L a s)[4]? =
    some (ci 22 ((s + 5 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int)) := rfl

theorem nimmT_ladeS : (nimmT L a s)[7]? = some (ci 1 ((s + 1 : Nat) : Int) ((a + 8 : Nat) : Int) 0) ∧
    (nimmT L a s)[8]? = some (ci 15 ((s + 5 : Nat) : Int) ((s + 1 : Nat) : Int) 0) :=
  ⟨rfl, rfl⟩

theorem nimmT_inc : (nimmT L a s)[12]? = some (ci 1 ((s + 7 : Nat) : Int) ((a + 16 : Nat) : Int) 0) ∧
    (nimmT L a s)[13]? = some (ci 15 ((s + 7 + 1 : Nat) : Int) ((s + 7 : Nat) : Int) 0) ∧
    (nimmT L a s)[16]? =
      some (ci 22 ((s + 7 + 4 : Nat) : Int) ((s + 7 : Nat) : Int) ((s + 7 + 1 : Nat) : Int)) :=
  ⟨rfl, rfl, rfl⟩

theorem nimmT_futexW : (nimmT L a s)[20]? = some (ci 1 ((s + 10 + 1 : Nat) : Int) ((a + 8 : Nat) : Int) 0) ∧
    (nimmT L a s)[21]? = some (ci 1 ((s + 10 + 2 : Nat) : Int) ((128 : Nat) : Int) 0) ∧
    (nimmT L a s)[22]? = some (ci 2 ((s + 10 + 3 : Nat) : Int) ((s + 5 : Nat) : Int) 0) ∧
    (nimmT L a s)[26]? = some (ci 23 ((s + 10 + 7 : Nat) : Int) ((s + 10 : Nat) : Int) 0) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem nimmT_dec : (nimmT L a s)[28]? = some (ci 15 ((s + 7 + 1 : Nat) : Int) ((s + 7 : Nat) : Int) 0) ∧
    (nimmT L a s)[31]? =
      some (ci 22 ((s + 7 + 4 : Nat) : Int) ((s + 7 : Nat) : Int) ((s + 7 + 1 : Nat) : Int)) ∧
    (nimmT L a s)[34]? = some (ci 18 (-(16 * 27)) 0 0) :=
  ⟨rfl, rfl, rfl⟩

theorem gibT_schritte : (gibT L a s)[0]? = some (ci 1 ((s + 1 : Nat) : Int) ((a + 8 : Nat) : Int) 0) ∧
    (gibT L a s)[1]? = some (ci 15 ((s + 2 : Nat) : Int) ((s + 1 : Nat) : Int) 0) ∧
    (gibT L a s)[4]? = some (ci 22 ((s + 5 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int)) ∧
    (gibT L a s)[5]? = some (ci 1 ((s + 1 : Nat) : Int) ((a + 16 : Nat) : Int) 0) ∧
    (gibT L a s)[6]? = some (ci 15 ((s + 2 : Nat) : Int) ((s + 1 : Nat) : Int) 0) ∧
    (gibT L a s)[7]? = some (ci 19 ((s + 2 : Nat) : Int) (16 * 9) 0) ∧
    (gibT L a s)[11]? = some (ci 1 ((s + 10 + 3 : Nat) : Int) 2147483647 0) ∧
    (gibT L a s)[15]? = some (ci 23 ((s + 10 + 7 : Nat) : Int) ((s + 10 : Nat) : Int) 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Code

end Gabbro.Stage0.Senke.Faeden
