/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Ausgang.lean
  Subject:   The give on a way out of `locks Lk { body }` in the ticket code: after the take (the lock read `n`,
              `n`, `0` before it and `n + 1`, `n`, `0` after it) and a body that changed the memory as a statement may
              (`AgreeW`), the lock still reads as mine (its class: next − serving = 1, no waiters), the give
              (`gibT_paar`) runs, and the whole is an `AgreeW` change. The taken lock's bytes are NOT restored (both
              tickets end one higher): the frame fact excludes them by `InSync` (they lie in `[L.hi, L.sye)`), and the
              lock keeps its class (next − serving and the waiters as at the start). Every other lock keeps its class
              through the take, the body and the give (`AgreeK.ticketKlasse`, `TicketKlasse.trans`).
-/
module
public import Stage0.Senke.Sperre.Ticket.Lauf
public import Stage0.Senke.Sperre.Ticket.Paar
public import Stage0.Senke.Sperre.Paar
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- **The give** at instruction `p` of the code, after the take and the body. -/
theorem locksT_give {L : Lay D} {fp : W} {K Ks lo : Nat} {H : List D.Lock} {Lk : D.Lock} {m m1 m2 : Mem} {pc : W}
    {s a : Nat} {code : List II} {f1 : Nat → W} {n : W}
    (ha : L.lk Lk = a) (hW : WIn L fp Ks K) (hy : TicketSync m L fp Ks H) (hs18 : s + 18 ≤ Ks) (hlo2 : lo ≤ s)
    (E0 : LE m pc fp s a code) (hcf : CodeFar pc code.length fp K)
    (h0n : m.rd64 (BitVec.ofNat 64 a) = some n) (h0u : m.rd64 (BitVec.ofNat 64 (a + 8)) = some n)
    (h0w : m.rd64 (BitVec.ofNat 64 (a + 16)) = some 0) (hL1 : LS m m1 fp s a f1 (n + 1) n 0)
    {p : Nat} (hAt : At code p (gibT L a s)) (a2 : AgreeW L fp lo K m1 m2) :
    ∃ m3, Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m2 ⟨pc + BitVec.ofNat 64 (16 * (p + 16)), fp⟩ m3 ∧
      AgreeW L fp lo K m m3 ∧ AgreeK fp s a m2 m3 := by
  have hla := hy.lay Lk
  rw [ha] at hla
  have hsye := hy.sye
  have htopW := hW.top
  have hord := hW.ord
  have hks := hW.ks
  have hfa := E0.far
  have ha31 := E0.top
  have hfh : fp.toNat + 8 * (s + 18) ≤ L.hi := by omega
  -- the body kept the class of the taken lock: next − serving = 1, no waiters
  have fern2 : LockFern L fp lo K a := fun k j hk hj => by
    have e := lk_byte (y := a + 8 * k) (by omega) hj
    exact ⟨fun ⟨_, h3⟩ => by rw [e] at h3; omega, fun ⟨_, h3⟩ => by rw [e] at h3; omega⟩
  have klasse2 : TicketKlasse m1 m2 a := by
    have kept := a2.sync Lk (by rw [ha]; exact fern2)
    rwa [ha] at kept
  obtain ⟨n2, u2, w2, e1, e2, e3, hd, hwq⟩ := klasse2 (n + 1) n 0 hL1.o hL1.c hL1.w
  have e11 : ∀ v : W, (v + 1) - v = 1 :=
    fun v => BitVec.sub_eq_iff_eq_add.mpr (BitVec.add_comm v 1)
  have hd1 : n2 - u2 = 1 := hd.trans (e11 n)
  have hn2 : n2 = u2 + 1 := by
    have h1 := BitVec.sub_eq_iff_eq_add.mp hd1
    rwa [BitVec.add_comm] at h1
  -- the give, from the state the body left
  have E2 : LE m2 pc fp s a code :=
    ⟨⟨E0.frame.lt, fun i hi => by rw [a2.rd, hL1.ag.rd]; exact E0.frame.rd i hi,
      fun i hi => by rw [a2.wr, hL1.ag.wr]; exact E0.frame.wr i hi⟩, E0.small, hfa, ha31,
     by rw [a2.wr, hL1.ag.wr]; exact E0.wr0, by rw [a2.wr, hL1.ag.wr]; exact E0.wr1,
     by rw [a2.wr, hL1.ag.wr]; exact E0.wr2, codeAt_agreeWIn hW a2 (hL1.ag.codeAt hfa ha31 E0.hcode hcf) hcf, E0.cfar⟩
  obtain ⟨f2, hL2⟩ := ls_init E2 e1 e2 e3
  have hL2' : LS m2 m2 fp s a f2 (u2 + 1) u2 0 := hL2.congr hn2 rfl hwq
  obtain ⟨m3, f3, s3, hL3⟩ := gibT_paar E2 hL2' hAt
  refine ⟨m3, s3, ⟨by rw [hL3.ag.rd, a2.rd, hL1.ag.rd], by rw [hL3.ag.wr, a2.wr, hL1.ag.wr],
    fun x hx hxw hxy => ?_, fun Lk' fern => ?_⟩, hL3.ag⟩
  · -- the lock's own bytes lie in the lock words; every other byte outside the frame and the world is kept
    by_cases hxl : InLk a x
    · exfalso
      obtain ⟨h1, h2⟩ := hxl
      exact hxy ⟨by omega, by omega, by omega, hsye⟩
    · have hxs : ¬ inSlots fp s (s + 18) x := fun ⟨h1, h2⟩ => hx ⟨by omega, by omega⟩
      rw [hL3.ag.b x hxs hxl, a2.b x hx hxw hxy, hL1.ag.b x hxs hxl]
  · by_cases hq : Lk' = Lk
    · -- the taken lock: free as at the start, both tickets one higher
      rw [hq, ha]
      intro t0 v0 z0 g1 g2 g3
      have q1 : t0 = n := Option.some_inj.mp (g1.symm.trans h0n)
      have q2 : v0 = n := Option.some_inj.mp (g2.symm.trans h0u)
      have q3 : z0 = 0 := Option.some_inj.mp (g3.symm.trans h0w)
      refine ⟨u2 + 1, u2 + 1, 0, hL3.o, hL3.c, hL3.w, ?_, q3.symm⟩
      rw [q1, q2]
      simp only [BitVec.sub_self]
    · -- every other lock: never touched by the take or the give
      have hd' := hy.dis Lk' Lk hq
      have hl' := hy.lay Lk'
      rw [ha] at hd'
      exact ((AgreeK.ticketKlasse hL1.ag (by omega) (by omega) hd').trans (a2.sync Lk' fern)).trans
        (AgreeK.ticketKlasse hL3.ag (by omega) (by omega) hd')

end Gabbro.Stage0.Senke
