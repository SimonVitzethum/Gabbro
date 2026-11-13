/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Sync.lean
  Subject:   `TicketSync m L fp Ks H`, what a thread's code may rely on about the ticket locks: the frame at `fp`
              lies in the thread's stack; every lock's three words lie above the world, apart from each other,
              writable; the specified waiter counts (zero by default), and a lock is mine (next = serving + 1)
              exactly when it lies in the thread's held set `H`, free (next = serving) otherwise. No thread number
              is needed. A statement keeps the difference (`TicketSync.keepWords`, `TicketSync.agreeW`); a change
              of the frame's slots alone keeps it (`TicketSync.agree`); a callee's frame inherits it
              (`TicketSync.call`).
-/
module
public import Stage0.Senke.Welt.WeltAt
public import Stage0.Senke.Welt.Schreib
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

theorem lk_byte {y j : Nat} (hy : y + 8 < 2 ^ 31) (hj : j < 8) :
    (BitVec.ofNat 64 y + BitVec.ofNat 64 j).toNat = y + j := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The frame of a callee at slot `F < Ks` lies in the same stack. -/
theorem meW_call {L : Lay D} {fp : W} {Ks F : Nat} (h : fp.toNat + 8 * Ks ≤ L.sb + L.st * ((fp.toNat - L.sb) / L.st + 1))
    (hlo : L.sb ≤ fp.toNat) (_hst : 0 < L.st) (hF : F < Ks) (hr : fp.toNat + 8 * Ks < 2 ^ 62) :
    (fp.toNat + 8 * F - L.sb) / L.st = (fp.toNat - L.sb) / L.st := by
  have hq := Nat.div_mul_le_self (fp.toNat - L.sb) L.st
  have e : L.st * ((fp.toNat - L.sb) / L.st + 1) = (fp.toNat - L.sb) / L.st * L.st + L.st := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [Nat.add_mul, Nat.one_mul]; omega

/-- The words of the ticket lock `Lk` against the held set `H`: next `n`, serving `s`, the specified waiters
    (zero by default); mine (`n = s + 1`) when `Lk ∈ H`, free (`n = s`) when not. -/
def TicketOK (m : Mem) (L : Lay D) (H : List D.Lock) (Lk : D.Lock) (waiters : W := 0) : Prop :=
  ∃ n s, m.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some n ∧ m.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some s ∧
    m.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some waiters ∧ (Lk ∈ H → n = s + 1) ∧ (Lk ∉ H → n = s)

structure TicketSync (m : Mem) (L : Lay D) (fp : W) (Ks : Nat) (H : List D.Lock)
    (waiters : D.Lock → W := fun _ => 0) : Prop where
  sb31 : L.sb < 2 ^ 31
  st : 0 < L.st
  st31 : L.st < 2 ^ 31
  lo : L.sb ≤ fp.toNat
  room : fp.toNat + 8 * Ks < 2 ^ 62
  band : fp.toNat + 8 * Ks ≤ L.sb + L.st * ((fp.toNat - L.sb) / L.st + 1)
  lay : ∀ Lk, L.hi ≤ L.lk Lk ∧ L.lk Lk + 24 ≤ L.sye
  sye : L.sye < 2 ^ 31
  dis : ∀ Lk Lk', Lk ≠ Lk' → L.lk Lk + 24 ≤ L.lk Lk' ∨ L.lk Lk' + 24 ≤ L.lk Lk
  wr : ∀ Lk k, k ≤ 2 → all m.wr (BitVec.ofNat 64 (L.lk Lk + 8 * k)) 8 = true
  zust : ∀ Lk, TicketOK m L H Lk (waiters Lk)

/-- The ticket state kept where the differences of every lock are. -/
theorem TicketSync.keepWords {m m' : Mem} {L : Lay D} {fp : W} {Ks : Nat} {H : List D.Lock}
    {waiters : D.Lock → W} (h : TicketSync m L fp Ks H waiters)
    (hrd : m'.rd = m.rd) (hwr : m'.wr = m.wr) (hk : ∀ Lk, TicketKlasse m m' (L.lk Lk)) :
    TicketSync m' L fp Ks H waiters := by
  refine ⟨h.sb31, h.st, h.st31, h.lo, h.room, h.band, h.lay, h.sye, h.dis, fun Lk k hk' => by
    rw [hwr]; exact h.wr Lk k hk', fun Lk => ?_⟩
  obtain ⟨n, s, hn, hs, hw, hmine, hfree⟩ := h.zust Lk
  obtain ⟨n', s', w', hn', hs', hw', hd, hwq⟩ := hk Lk n s (waiters Lk) hn hs hw
  refine ⟨n', s', hn', hs', ?_, fun hin => ?_, fun hout => ?_⟩
  · rw [hwq] at hw'
    exact hw'
  · rw [hmine hin] at hd
    have e1 : ∀ v : W, (v + 1) - v = 1 :=
      fun v => BitVec.sub_eq_iff_eq_add.mpr (BitVec.add_comm v 1)
    rw [e1] at hd
    have e2 := BitVec.sub_eq_iff_eq_add.mp hd
    rw [BitVec.add_comm] at e2
    exact e2
  · rw [hfree hout] at hd
    simp only [BitVec.sub_self] at hd
    have e := BitVec.sub_eq_iff_eq_add.mp hd
    rw [BitVec.zero_add] at e
    exact e

/-- A statement's change keeps the ticket state: every lock keeps its class. -/
theorem TicketSync.agreeW {m m' : Mem} {L : Lay D} {fp : W} {Ks lo K : Nat} {H : List D.Lock}
    {waiters : D.Lock → W} (h : TicketSync m L fp Ks H waiters)
    (ha : AgreeW L fp lo K m m') (hK : fp.toNat + 8 * K ≤ L.hi) : TicketSync m' L fp Ks H waiters :=
  h.keepWords ha.rd ha.wr fun Lk => ha.sync Lk fun k j hk hj => by
    have hl := h.lay Lk
    have hsy := h.sye
    have e := lk_byte (y := L.lk Lk + 8 * k) (by omega) hj
    exact ⟨fun ⟨_, h3⟩ => by rw [e] at h3; omega, fun ⟨_, h3⟩ => by rw [e] at h3; omega⟩

/-- The ticket state kept where the bytes from `L.hi` to `L.sye` are. -/
theorem TicketSync.keep {m m' : Mem} {L : Lay D} {fp : W} {Ks : Nat} {H : List D.Lock} {waiters : D.Lock → W}
    (h : TicketSync m L fp Ks H waiters) (hrd : m'.rd = m.rd) (hwr : m'.wr = m.wr)
    (hb : ∀ x : W, L.hi ≤ x.toNat → x.toNat < L.sye → m'.b x = m.b x) : TicketSync m' L fp Ks H waiters :=
  h.keepWords hrd hwr fun Lk => TicketKlasse.ofWords fun k hk => by
    have hl := h.lay Lk
    have hsy := h.sye
    exact rd64_keep hrd fun j hj => hb _ (by rw [lk_byte (by omega) hj]; omega) (by rw [lk_byte (by omega) hj]; omega)

/-- A change of the frame's slots alone keeps the ticket state. -/
theorem TicketSync.agree {m m' : Mem} {L : Lay D} {fp : W} {Ks lo K : Nat} {H : List D.Lock}
    {waiters : D.Lock → W} (h : TicketSync m L fp Ks H waiters) (ha : Agree fp lo K m m')
    (hK : fp.toNat + 8 * K ≤ L.hi) : TicketSync m' L fp Ks H waiters :=
  h.keep ha.rd ha.wr fun x h1 _ => ha.b x (fun ⟨_, h3⟩ => by omega)

theorem TicketSync.mono {m : Mem} {L : Lay D} {fp : W} {Ks Ks' : Nat} {H : List D.Lock}
    {waiters : D.Lock → W} (h : TicketSync m L fp Ks H waiters) (hs : Ks' ≤ Ks) :
    TicketSync m L fp Ks' H waiters := by
  refine ⟨h.sb31, h.st, h.st31, h.lo, by have := h.room; omega, by have := h.band; omega, h.lay, h.sye,
    h.dis, h.wr, h.zust⟩

/-- The frame of a callee at slot `F < Ks` lies in the same stack; the lock words do not depend on the frame. -/
theorem TicketSync.call {m : Mem} {L : Lay D} {fp : W} {Ks F : Nat} {H : List D.Lock} {waiters : D.Lock → W}
    (h : TicketSync m L fp Ks H waiters) (hF : F < Ks) :
    TicketSync m L (slot fp (BitVec.ofNat 64 F)) (Ks - F) H waiters := by
  have hr := h.room
  have hs := slot_toNat (fp := fp) (K := Ks) (i := F) (by omega) hF
  have hq := meW_call h.band h.lo h.st hF hr
  exact ⟨h.sb31, h.st, h.st31, by rw [hs]; have := h.lo; omega, by rw [hs]; omega,
    by rw [hs, hq]; have := h.band; omega, h.lay, h.sye, h.dis, h.wr, h.zust⟩

end Gabbro.Stage0.Senke
