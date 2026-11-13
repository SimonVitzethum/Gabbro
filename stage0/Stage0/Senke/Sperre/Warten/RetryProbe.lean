/- Real encoded memory witnesses for the CAS miss and the acquired branch. -/
module
public import Stage0.Senke.Sperre.Warten.Fixture
@[expose] public section

namespace Gabbro.Stage0.Senke.WartenProbe
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
set_option maxRecDepth 100000
variable [Kern]

/-- A stale expected ticket zero and its successor one, while next is one.
    These are actual frame bytes, not an abstract slot function premise. -/
def missMemory : Mem :=
  write (write (write (memory false) (slot 4096 5) 8 8192)
    (slot 4096 6) 8 0) (slot 4096 7) 8 1

theorem nimmT_cas_miss_zeuge :
    ∃ m' f', Star ⟨64, 4096⟩ missMemory ⟨0, 4096⟩ m' ∧
      LS (memory false) m' 4096 4 8192 f' 1 0 0 ∧ f' 5 = 0 ∧ f' 2 = 0 ∧
      m'.rd64 (slot 4096 3) = some 77 := by
  have E := environment false
  obtain ⟨f0, initial⟩ := ls_init E (o := 1) (c := 0) (w := 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h1 := initial.slot E (d := 1) (by decide) 8192
  have h2 := h1.slot E (d := 2) (by decide) 0
  have h3 := h2.slot E (d := 3) (by decide) 1
  have h3' : LS (memory false) missMemory 4096 4 8192
      (upd (upd (upd f0 1 8192) 2 0) 3 1) 1 0 0 := h3
  obtain ⟨m', f', steps, state, result, ticket, _⟩ := nimmT_cas_miss E h3'
    (At.whole takeCode) (by simp [upd]) (by simp [upd])
  refine ⟨m', f', steps, state, result, ?_, ?_⟩
  · simpa [upd] using ticket
  · exact (state.ag.rd_low (i := 3) (by decide) E.far E.top).trans (by decide +kernel)

/-- A free lock on the same real encoded memory fixture reaches index ten,
    then the acquired branch reaches index 35 with the ticket still in two. -/
theorem nimmT_acquired_zeuge :
    ∃ m' f', Star ⟨0, 4096⟩ (write (memory false) 8192 8 0) ⟨560, 4096⟩ m' ∧
      LS (memory false) m' 4096 4 8192 f' 1 0 0 ∧ f' 2 = 0 ∧
      m'.rd64 (slot 4096 3) = some 77 := by
  have E := environment false
  obtain ⟨f0, initial⟩ := ls_init E (o := 1) (c := 0) (w := 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have free := initial.owner E 0
  obtain ⟨m1, f1, steps1, state1, ticket, seen, compared⟩ := nimmT_check E free (At.whole takeCode)
  obtain ⟨steps2, _⟩ := nimmT_acquired E state1 (At.whole takeCode) compared seen
    (by rw [seen, ticket])
  refine ⟨m1, f1, steps1.trans steps2, state1, ticket, ?_⟩
  exact (state1.ag.rd_low (i := 3) (by decide) E.far E.top).trans (by decide +kernel)

end Gabbro.Stage0.Senke.WartenProbe
