/- A complete real-memory WAIT entry, spurious return and retry cycle. -/
module
public import Stage0.Senke.Sperre.Warten.Fixture
@[expose] public section

namespace Gabbro.Stage0.Senke.WartenProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
set_option maxRecDepth 100000
variable [RootNativeFloat.Hardware]

/-- Draw ticket one behind serving zero; register the first waiter, WAIT,
    return spuriously, unregister, and reach the serving re-read at index seven.
    All environment and slot premises are discharged on encoded memory. -/
theorem nimmT_wait_retry_zeuge :
    letI : Kern := futexKernel
    ∃ mw fw m' f', Star ⟨0, 4096⟩ (memory false) ⟨416, 4096⟩ mw ∧
      StopAt ⟨416, 4096⟩ mw (futexReq 8200 128 0) ∧
      Star ⟨416, 4096⟩ mw ⟨112, 4096⟩ m' ∧
      LS (memory false) m' 4096 4 8192 f' 2 0 0 ∧ TicketInvW 2 2 0 0 ∧
      FutexArgs fw 8200 128 0 ∧ f' 2 = 1 ∧ f' 5 = 0 ∧
      m'.rd64 (slot 4096 3) = some 77 := by
  letI : Kern := futexKernel
  letI : FutexOK (fun _ _ _ _ => True) := futexOK_zeuge
  have E := environment false
  obtain ⟨f0, initial⟩ := ls_init E (o := 1) (c := 0) (w := 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨m1, f1, steps1, state1, ticket, seen, compared⟩ := nimmT_check E initial (At.whole takeCode)
  obtain ⟨mw, fw, stepsw, statew, invw, args, ticketw, seenw, entry⟩ :=
    nimmT_wait_entry E state1 (At.whole takeCode) ticket compared (by rw [seen]; decide)
      (T := 2) (by unfold TicketInvW; decide +kernel) (by decide)
  have args' : FutexArgs fw 8200 128 0 := by simpa [seen] using args
  have answer : Kern.ans (futexReq 8200 128 0) mw (some (0, 0)) mw :=
    ⟨rfl, 8200, 0, Or.inl rfl, rfl⟩
  obtain ⟨_, m', f', stepsr, stater, invr, ticketr, seenr⟩ :=
    nimmT_wait_retry (spurious := fun _ _ _ _ => True) E statew (At.whole takeCode)
      args' answer statew invw (by decide)
  refine ⟨mw, fw, m', f', steps1.trans stepsw, ?_, stepsr, stater, invr, args', ?_, ?_, ?_⟩
  · simpa [seen] using entry
  · exact ticketr.trans ticketw
  · exact seenr.trans (seenw.trans seen)
  · exact (stater.ag.rd_low (i := 3) (by decide) E.far E.top).trans (by decide +kernel)

end Gabbro.Stage0.Senke.WartenProbe
