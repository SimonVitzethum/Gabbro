/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Prozess.lean
  Subject:   The IR process at request granularity (multi-thread image theorem, package MT1). The runner's machine of
             threads (`Runner.Mach.Cfg`, `Tr` with `actI`) holds a memory-model state and the threads' states
             `Option (Res T)` (`none`: ended). `PCfg` is its configuration with the memory itself as the state, and
             `MSchritt i` the two steps of thread `i` that the memory answers alone: the start of an instruction
             (`priv`: `.next t` becomes `step t`) and the answer to a request (`ask`: the memory answers with
             `memAns`, the thread continues with `k a`). System calls (exit, clone, futex) and floating requests are
             the steps of later packages (MT5, MT6); the bridge from the memory model `SC` is `Mehr/SC.lean`.
-/
module
public import Runner.IR.NativeRun
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR

/-- A configuration of the IR process: the shared memory and the threads (`none`: ended). -/
structure PCfg where
  m : Mem
  ths : List (Option (Res T))

/-- **A step of thread `i` answered by the memory alone.** -/
inductive MSchritt (i : Nat) : PCfg → PCfg → Prop
  | priv {c : PCfg} {t : T} :
      c.ths[i]? = some (some (.next t)) → MSchritt i c ⟨c.m, c.ths.set i (some (step t))⟩
  | ask {c : PCfg} {o : Op} {k : Ans → Res T} {a : Ans} {m' : Mem} :
      c.ths[i]? = some (some (.ask o k)) → memAns c.m o = some (a, m') →
      MSchritt i c ⟨m', c.ths.set i (some (k a))⟩

/-- Setting the entry of a thread that exists: it reads back. -/
theorem set_selbst {α : Type} {l : List α} {i : Nat} {x a : α} (h : l[i]? = some x) : (l.set i a)[i]? = some a := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 h
  exact List.getElem?_set_self hlt

/-- Setting the entry of thread `i` leaves every other thread. -/
theorem set_fremd {α : Type} (l : List α) {i j : Nat} (a : α) (h : j ≠ i) : (l.set i a)[j]? = l[j]? :=
  List.getElem?_set_ne (Ne.symm h)

/-- A step of thread `i` leaves every other thread. -/
theorem MSchritt.fremd {i : Nat} {c c' : PCfg} (hs : MSchritt i c c') {j : Nat} (hj : j ≠ i) :
    c'.ths[j]? = c.ths[j]? := by
  cases hs with
  | priv _ => exact set_fremd _ _ hj
  | ask _ _ => exact set_fremd _ _ hj

end Gabbro.Stage0.Senke.BildMehr
