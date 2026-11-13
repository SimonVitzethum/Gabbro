/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Paar.lean
  Subject:   Taking and giving as a pair for the ticket lock, from a FREE lock (`TicketOK`): the take runs and
              leaves it mine (next one higher, serving as it was); the give, from mine with no waiters, runs and
              leaves it free (both tickets one higher).
-/
module
public import Stage0.Senke.Sperre.Ticket.Nimm
public import Stage0.Senke.Sperre.Ticket.Gib
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

section
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {n u w : W}

/-- What `TicketOK` allows of one lock: free, next = serving. -/
def TicketSt (n u : W) : Prop :=
  n = u

/-- The take, from a free lock: mine, next one higher, serving as it was. -/
theorem nimmT_paar {L : Lay D} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f n u w) {p : Nat}
    (hc : At code p (nimmT L a s)) (hst : TicketSt n u) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 35)), fp⟩ m' ∧
      LS m0 m' fp s a f' (n + 1) n w := by
  have h' : LS m0 m fp s a f n n w := h.congr rfl (Eq.symm hst) rfl
  exact nimmT_frei E h' hc

/-- The give, from mine with no waiters: free, both tickets one higher. -/
theorem gibT_paar {L : Lay D} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f (n + 1) n 0) {p : Nat}
    (hc : At code p (gibT L a s)) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 16)), fp⟩ m' ∧
      LS m0 m' fp s a f' (n + 1) (n + 1) 0 :=
  gibT_ohne E h hc

end

end Gabbro.Stage0.Senke
