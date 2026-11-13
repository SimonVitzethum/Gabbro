/- A real encoded give with one waiting ticket and a WAKE-all return. -/
module
public import Stage0.Senke.Sperre.Warten.Fixture
public import Stage0.Senke.Sperre.Warten.Wake
@[expose] public section

namespace Gabbro.Stage0.Senke.WartenProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
set_option maxRecDepth 100000
variable [RootNativeFloat.Hardware]

/-- Two outstanding tickets, one holder and one waiter. Giving advances serving
    to one, WAKE-all returns, and the waiter count remains one until that waiter
    unregisters. Both word states satisfy the thread-independent invariant. -/
theorem gibT_waiters_zeuge :
    letI : Kern := futexKernel
    TicketInvW 2 2 0 1 ∧ TicketInvW 2 2 1 1 ∧
    ∃ mw fw m', Star ⟨0, 4096⟩ (memory true) ⟨240, 4096⟩ mw ∧
      StopAt ⟨240, 4096⟩ mw (futexReq 8200 129 2147483647) ∧
      Star ⟨240, 4096⟩ mw ⟨256, 4096⟩ m' ∧
      LS (memory true) m' 4096 4 8192 (upd fw 17 0) 2 1 1 ∧
      FutexArgs fw 8200 129 2147483647 ∧ m'.rd64 (slot 4096 3) = some 77 := by
  letI : Kern := futexKernel
  letI : FutexOK (fun _ _ _ _ => True) := futexOK_zeuge
  have E := environment true
  obtain ⟨f0, initial⟩ := ls_init E (o := 2) (c := 0) (w := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨mw, fw, stepsw, statew, args, entry⟩ :=
    gibT_waiters_entry E initial (At.whole wakeCode) (by decide)
  have answer : Kern.ans (futexReq 8200 129 2147483647) mw (some (0, 0)) mw :=
    ⟨rfl, 8200, 2147483647, Or.inr rfl, rfl⟩
  obtain ⟨_, m', stepsr, stater⟩ := gibT_waiters_return (spurious := fun _ _ _ _ => True)
    E statew (At.whole wakeCode) args answer statew
  refine ⟨by unfold TicketInvW; decide +kernel, by unfold TicketInvW; decide +kernel,
    mw, fw, m', stepsw, entry, stepsr, stater, args, ?_⟩
  exact (stater.ag.rd_low (i := 3) (by decide) E.far E.top).trans (by decide +kernel)

end Gabbro.Stage0.Senke.WartenProbe
