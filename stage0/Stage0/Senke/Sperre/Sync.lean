/-
  File:      stage0/Stage0/Senke/Sperre/Sync.lean
  Subject:   `SyncOK m L fp Ks`, what a thread's code may rely on about the locks (`PLAN-SELF-HOSTING.md` §2.1.6):
             the frame at `fp` lies in the thread's stack (`meW L fp` is the thread's number + 1, also for every
             frame above it within `Ks` slots); every lock's three words lie above the world, apart from each
             other, writable; nobody waits, and a lock is free (owner 0, count 0) or mine with a count that leaves
             room for `Ks` more takes. A statement keeps the words (`SyncOK.agreeW`); a callee's frame inherits it
             (`SyncOK.call`).
-/
import Stage0.Senke.Sperre.Gib
import Stage0.Senke.Welt.WeltAt

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-- The words of the lock `Lk`: owner `o`, count `c`, nobody waiting; free, or mine with room for `Ks` takes. -/
def LockOK (m : Mem) (L : Lay D) (fp : W) (Ks : Nat) (Lk : D.Lock) : Prop :=
  ∃ o c, m.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some o ∧ m.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some c ∧
    m.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some 0 ∧
    ((o = 0 ∧ c = 0) ∨ (o = meW L fp ∧ 1 ≤ c.toNat ∧ c.toNat + Ks < 2 ^ 62))

structure SyncOK (m : Mem) (L : Lay D) (fp : W) (Ks : Nat) : Prop where
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
  zust : ∀ Lk, LockOK m L fp Ks Lk

theorem SyncOK.me {m : Mem} {L : Lay D} {fp : W} {Ks : Nat} (h : SyncOK m L fp Ks) : MeOK L fp :=
  ⟨h.lo, h.sb31, h.st, h.st31, by have := h.room; omega⟩

theorem lk_byte {y j : Nat} (hy : y + 8 < 2 ^ 31) (hj : j < 8) :
    (BitVec.ofNat 64 y + BitVec.ofNat 64 j).toNat = y + j := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The lock words kept where the bytes from `L.hi` to `L.sye` are. -/
theorem SyncOK.keep {m m' : Mem} {L : Lay D} {fp : W} {Ks : Nat} (h : SyncOK m L fp Ks) (hrd : m'.rd = m.rd)
    (hwr : m'.wr = m.wr) (hb : ∀ x : W, L.hi ≤ x.toNat → x.toNat < L.sye → m'.b x = m.b x) :
    SyncOK m' L fp Ks := by
  refine ⟨h.sb31, h.st, h.st31, h.lo, h.room, h.band, h.lay, h.sye, h.dis, fun Lk k hk => by
    rw [hwr]; exact h.wr Lk k hk, fun Lk => ?_⟩
  obtain ⟨o, c, ho, hc, hw, hs⟩ := h.zust Lk
  have hl := h.lay Lk
  have hsy := h.sye
  have keep : ∀ y, L.lk Lk ≤ y → y ≤ L.lk Lk + 16 → m'.rd64 (BitVec.ofNat 64 y) = m.rd64 (BitVec.ofNat 64 y) :=
    fun y h1 h2 => rd64_keep hrd fun j hj => hb _ (by rw [lk_byte (by omega) hj]; omega)
      (by rw [lk_byte (by omega) hj]; omega)
  exact ⟨o, c, by rw [keep _ (Nat.le_refl _) (by omega)]; exact ho, by rw [keep _ (by omega) (by omega)]; exact hc,
    by rw [keep _ (by omega) (Nat.le_refl _)]; exact hw, hs⟩

/-- A statement's change keeps the lock words. -/
theorem SyncOK.agreeW {m m' : Mem} {L : Lay D} {fp : W} {Ks lo K : Nat} (h : SyncOK m L fp Ks)
    (ha : AgreeW L fp lo K m m') (hK : fp.toNat + 8 * K ≤ L.hi) : SyncOK m' L fp Ks :=
  h.keep ha.rd ha.wr fun x h1 _ => ha.b x (fun ⟨_, h3⟩ => by omega) (fun ⟨_, h3⟩ => by omega)

theorem SyncOK.agree {m m' : Mem} {L : Lay D} {fp : W} {Ks lo K : Nat} (h : SyncOK m L fp Ks)
    (ha : Agree fp lo K m m') (hK : fp.toNat + 8 * K ≤ L.hi) : SyncOK m' L fp Ks :=
  h.keep ha.rd ha.wr fun x h1 _ => ha.b x (fun ⟨_, h3⟩ => by omega)

theorem SyncOK.mono {m : Mem} {L : Lay D} {fp : W} {Ks Ks' : Nat} (h : SyncOK m L fp Ks) (hs : Ks' ≤ Ks) :
    SyncOK m L fp Ks' := by
  refine ⟨h.sb31, h.st, h.st31, h.lo, by have := h.room; omega, by have := h.band; omega, h.lay, h.sye, h.dis,
    h.wr, fun Lk => ?_⟩
  obtain ⟨o, c, ho, hc, hw, hs'⟩ := h.zust Lk
  refine ⟨o, c, ho, hc, hw, ?_⟩
  rcases hs' with h0 | ⟨h1, h2, h3⟩
  · exact Or.inl h0
  · exact Or.inr ⟨h1, h2, by omega⟩

/-- The frame of a callee at slot `F < Ks` lies in the same stack: the same thread. -/
theorem meW_call {L : Lay D} {fp : W} {Ks F : Nat} (h : fp.toNat + 8 * Ks ≤ L.sb + L.st * ((fp.toNat - L.sb) / L.st + 1))
    (hlo : L.sb ≤ fp.toNat) (_hst : 0 < L.st) (hF : F < Ks) (hr : fp.toNat + 8 * Ks < 2 ^ 62) :
    (fp.toNat + 8 * F - L.sb) / L.st = (fp.toNat - L.sb) / L.st := by
  have hq := Nat.div_mul_le_self (fp.toNat - L.sb) L.st
  have e : L.st * ((fp.toNat - L.sb) / L.st + 1) = (fp.toNat - L.sb) / L.st * L.st + L.st := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [Nat.add_mul, Nat.one_mul]; omega

theorem SyncOK.call {m : Mem} {L : Lay D} {fp : W} {Ks F : Nat} (h : SyncOK m L fp Ks) (hF : F < Ks) :
    SyncOK m L (slot fp (BitVec.ofNat 64 F)) (Ks - F) := by
  have hr := h.room
  have hs := slot_toNat (fp := fp) (K := Ks) (i := F) (by omega) hF
  have hq := meW_call h.band h.lo h.st hF hr
  have hme : meW L (slot fp (BitVec.ofNat 64 F)) = meW L fp := by simp only [meW, hs, hq]
  refine ⟨h.sb31, h.st, h.st31, by rw [hs]; have := h.lo; omega, by rw [hs]; omega,
    by rw [hs, hq]; have := h.band; omega, h.lay, h.sye, h.dis, h.wr, fun Lk => ?_⟩
  obtain ⟨o, c, ho, hc, hw, hs'⟩ := h.zust Lk
  refine ⟨o, c, ho, hc, hw, ?_⟩
  rcases hs' with h0 | ⟨h1, h2, h3⟩
  · exact Or.inl h0
  · exact Or.inr ⟨by rw [hme]; exact h1, h2, by omega⟩

end Gabbro.Stage0.Senke
