/- The selected binding survives the production image path. Statements concern
   lock code; startup and other declared gates have their own bindings. -/
module
public import Stage0.IRBild
public import Stage0.Senke.Sperre.Bindung.Code
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Relocation changes code and stack addresses, never the wait binding. -/
theorem bild_lockWait {D : Deklaration} {P : Programm D} {passes : Nat}
    {Y : Nat → Lay D} {fs : List D.Fn} {pos : D.Fn → Nat} {name : D.Fn → String}
    {main : D.Fn} {args : Env D (D.params main)}
    {starts : List (Σ f : D.Fn, Env D (D.params f))} {slots req : Nat} {b : Bild D}
    {strategy : LockWait} (binding : ∀ base, (Y base).lockWait = strategy)
    (emitted : bild passes P Y fs pos name main args starts slots req = .ok b) :
    b.Y.lockWait = strategy := by
  simp only [bild] at emitted
  split at emitted
  · cases emitted
  · split at emitted
    · cases emitted
    · split at emitted
      · simp only [Except.ok.injEq] at emitted
        subst b
        exact binding _
      · exfalso
        revert emitted
        repeat' split
        all_goals intro emitted; cases emitted

/-- Every lock instruction of the freestanding binding is syscall-free,
    including unreachable padding and the release block. -/
theorem ticket_spin_no_syscall {D : Deklaration} (L : Lay D) (a s : Nat)
    (binding : L.lockWait = .spin) :
    ((nimmT L a s ++ gibT L a s).all fun i => i.o != 23) = true := by
  simp [nimmT, gibT, binding, waitEntry, ticketWaitC, ticketWakeC, bindingCell, futexC, addC, ci]

/-- The scoped lock and all three release paths add no syscall to a
    syscall-free body in a freestanding image. -/
theorem locksCodeT_spin_no_syscall {D : Deklaration} (L : Lay D) (a s : Nat)
    (cb : List II) (x y : Int) (binding : L.lockWait = .spin)
    (body : (cb.all fun i => i.o != 23) = true) :
    ((locksCodeT L a s cb x y).all fun i => i.o != 23) = true := by
  simp [locksCodeT, nimmT, gibT, binding, waitEntry, ticketWaitC, ticketWakeC, bindingCell, futexC, addC, ci, body]

/-- Linux retains WAIT on contention and WAKE-all on release, at the same
    offsets as the existing sequential and cross-thread theorems. -/
theorem ticket_futex_syscalls {D : Deklaration} (L : Lay D) (a s : Nat)
    (binding : L.lockWait = .futex) :
    (nimmT L a s)[26]? = some (ci 23 ((s + 17 : Nat) : Int) ((s + 10 : Nat) : Int) 0) ∧
    (gibT L a s)[15]? = some (ci 23 ((s + 17 : Nat) : Int) ((s + 10 : Nat) : Int) 0) ∧
    (gibT L a s)[11]? = some (ci 1 ((s + 13 : Nat) : Int) 2147483647 0) := by
  simp [nimmT, gibT, binding, waitEntry, ticketWaitC, ticketWakeC, bindingCell, futexC, addC,
    Int.add_assoc]

end Gabbro.Stage0.Senke

namespace Gabbro.Stage0

/-- The production image uses precisely the checked profile's wait strategy. -/
theorem Emitted.lockWait {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) :
    output.image.Y.lockWait =
      (Profil.imageEnvironment options output.compiled.source.prepared.bindung).lockWait :=
  Senke.bild_lockWait (fun _ => rfl) output.emission

/-- A freestanding-profile emitted image has no syscall in its ticket-lock code. -/
theorem Emitted.lock_spin_no_syscall {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options)
    (binding : Profil.imageEnvironment options output.compiled.source.prepared.bindung = .freestanding)
    (a s : Nat) :
    ((Senke.nimmT output.image.Y a s ++ Senke.gibT output.image.Y a s).all fun i => i.o != 23) = true :=
  Senke.ticket_spin_no_syscall _ _ _ (by rw [output.lockWait, binding]; rfl)

end Gabbro.Stage0
