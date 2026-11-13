/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Lauf.lean
  Subject:   What the ticket lock code keeps (`AgreeK`: only the scratch slots and the taken lock's own words
              change): every other lock keeps its class (`AgreeK.ticketKlasse`) and its ticket state against the
              held set (`AgreeK.ticketOK`); after the take of a free lock `Lk` the ticket state holds against
              `Lk :: H` (`TicketSync.nimmt`).
-/
module
public import Stage0.Senke.Sperre.Lauf
public import Stage0.Senke.Sperre.Ticket.Sync
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- The words of another lock, apart from the lock at `a` and above the scratch slots, keep their class. -/
theorem AgreeK.ticketKlasse {m m1 : Mem} {fp : W} {s a b : Nat} (h : AgreeK fp s a m m1)
    (hb31 : b + 24 < 2 ^ 31) (hf : fp.toNat + 8 * (s + 18) ≤ b) (hd : b + 24 ≤ a ∨ a + 24 ≤ b) :
    TicketKlasse m m1 b :=
  TicketKlasse.ofLock (h.klasse hb31 hf hd)

/-- The ticket state of another lock survives. -/
theorem AgreeK.ticketOK {m m1 : Mem} {fp : W} {s Ks : Nat} {L : Lay D} {H : List D.Lock}
    {waiters : D.Lock → W} {Lk Lk' : D.Lock}
    (h : AgreeK fp s (L.lk Lk) m m1) (hy : TicketSync m L fp Ks H waiters) (hne : Lk' ≠ Lk)
    (hf : fp.toNat + 8 * (s + 18) ≤ L.hi) :
    TicketOK m1 L H Lk' (waiters Lk') := by
  obtain ⟨n, u, hn, hu, hw, hz⟩ := hy.zust Lk'
  have hd := hy.dis Lk' Lk hne
  have hl := hy.lay Lk'
  have hsy := hy.sye
  have keep : ∀ y, L.lk Lk' ≤ y → y ≤ L.lk Lk' + 16 →
      m1.rd64 (BitVec.ofNat 64 y) = m.rd64 (BitVec.ofNat 64 y) :=
    fun y h1 h2 => rd64_keep h.rd fun j hj => h.b _ (fun ⟨_, h3⟩ => by
        rw [lk_byte (by omega) hj] at h3
        omega) (fun ⟨h3, h4⟩ => by rw [lk_byte (by omega) hj] at h3 h4; omega)
  exact ⟨n, u, by rw [keep _ (Nat.le_refl _) (by omega)]; exact hn, by rw [keep _ (by omega) (by omega)]; exact hu,
    by rw [keep _ (by omega) (Nat.le_refl _)]; exact hw, hz⟩

/-- **The take, in the invariant**: the lock `Lk` read as taken (next `n + 1`, serving `n`) after the take's
    change, every other lock untouched: the ticket state holds against `Lk :: H`. -/
theorem TicketSync.nimmt {m m1 : Mem} {L : Lay D} {fp : W} {Ks s : Nat} {H : List D.Lock}
    {waiters : D.Lock → W} {Lk : D.Lock} {n : W}
    (hy : TicketSync m L fp Ks H waiters) (ha : AgreeK fp s (L.lk Lk) m m1)
    (hf : fp.toNat + 8 * (s + 18) ≤ L.hi)
    (ho : m1.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some (n + 1))
    (hc : m1.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some n)
    (hw : m1.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some (waiters Lk)) :
    TicketSync m1 L fp Ks (Lk :: H) waiters := by
  refine ⟨hy.sb31, hy.st, hy.st31, hy.lo, hy.room, hy.band, hy.lay, hy.sye, hy.dis,
    fun Lk' k hk => by rw [ha.wr]; exact hy.wr Lk' k hk, fun Lk' => ?_⟩
  by_cases hq : Lk' = Lk
  · rw [hq]
    exact ⟨n + 1, n, ho, hc, hw, fun _ => rfl, fun hn => (hn (List.mem_cons.mpr (Or.inl rfl))).elim⟩
  · obtain ⟨n', u', hn', hu', hw', hmine, hfree⟩ := ha.ticketOK hy hq hf
    refine ⟨n', u', hn', hu', hw', fun hin => hmine ?_, fun hout => hfree ?_⟩
    · rcases List.mem_cons.mp hin with e | e
      · exact absurd e hq
      · exact e
    · exact fun e => hout (List.mem_cons.mpr (Or.inr e))

end Gabbro.Stage0.Senke
