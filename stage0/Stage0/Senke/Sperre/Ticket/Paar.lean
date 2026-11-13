/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Paar.lean
  Subject:   Taking and giving as a pair for the ticket lock, from a FREE lock (`TicketOK`): the take runs and
              leaves it mine (next one higher, serving as it was); the give, from mine with no waiters, runs and
              leaves it free (both tickets one higher). Take, body and give keep the lock's class
              (`nimmT_gibT_klasse`).
-/
module
public import Stage0.Senke.Sperre.Ticket.Nimm
public import Stage0.Senke.Sperre.Ticket.Gib
public import Stage0.Senke.Sperre.Ticket.Klasse
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

/-- Take, body and give keep the lock's class: next and serving both grew by one, waiters unchanged.
    The take's endpoint is the caller's (`nimmT_paar`); the body is its class between the two endpoints. -/
theorem nimmT_gibT_klasse {L : Lay D} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f n n 0)
    {q : Nat} (hcG : At code q (gibT L a s))
    {m1 m2 : Mem} {f1 f2 : Nat → W} {u1 u2 w2 : W}
    (hL1 : LS m0 m1 fp s a f1 (n + 1) n 0) (hL2 : LS m0 m2 fp s a f2 u1 u2 w2)
    (h12 : TicketKlasse m1 m2 a) :
    ∃ m3, Star ⟨pc + BitVec.ofNat 64 (16 * q), fp⟩ m2
      ⟨pc + BitVec.ofNat 64 (16 * (q + 16)), fp⟩ m3 ∧
      TicketKlasse m m3 a := by
  obtain ⟨t2, v2, z2, e1, e2, e3, hd, hwq⟩ := h12 (n + 1) n 0 hL1.o hL1.c hL1.w
  have r1 : u1 = t2 := (Option.some_inj.mp (e1.symm.trans hL2.o)).symm
  have r2 : u2 = v2 := (Option.some_inj.mp (e2.symm.trans hL2.c)).symm
  have r3 : w2 = z2 := (Option.some_inj.mp (e3.symm.trans hL2.w)).symm
  subst r1 r2 r3
  have e : ∀ v : W, (v + 1) - v = 1 :=
    fun v => BitVec.sub_eq_iff_eq_add.mpr (BitVec.add_comm v 1)
  rw [e] at hd
  have hn2 : u1 = u2 + 1 := by
    have h1 := BitVec.sub_eq_iff_eq_add.mp hd
    rwa [BitVec.add_comm] at h1
  have hL2' : LS m0 m2 fp s a f2 (u2 + 1) u2 0 := hL2.congr hn2 rfl hwq
  obtain ⟨m3, f3, sG, hL3⟩ := gibT_ohne E hL2' hcG
  refine ⟨m3, sG, ?_⟩
  intro t0 v0 z0 g1 g2 g3
  have q1 : t0 = n := Option.some_inj.mp (g1.symm.trans h.o)
  have q2 : v0 = n := Option.some_inj.mp (g2.symm.trans h.c)
  have q3 : z0 = 0 := Option.some_inj.mp (g3.symm.trans h.w)
  subst q1 q2 q3
  exact ⟨u2 + 1, u2 + 1, 0, hL3.o, hL3.c, hL3.w, by simp only [BitVec.sub_self], rfl⟩

end

end Gabbro.Stage0.Senke
