/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Anfang.lean
  Subject:   The start of `locks Lk { body }` in the ticket code (`locksCodeT`): the lock is free (`HeldIn.frei`
              from the rank premise and the floor), the take (`nimmT_paar`) runs to the body at instruction 35,
              and there the body may rely on what `lowS_ok` gives a body (`Umf`), with the ticket state against
              `Lk :: H` (`TicketSync.nimmt`) and the held-set tie for `.held Lk :: Λ` (`HeldIn.nimmt`).
-/
module
public import Stage0.Senke.Sperre.Ticket.Lauf
public import Stage0.Senke.Sperre.Ticket.Frei
public import Stage0.Senke.Sperre.Ticket.Paar
public import Stage0.Senke.Sperre.Ticket.Lage
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- **The take**: from the start of the ticket code, with the lock `Lk` (words at `a`) not in the thread's held set,
    the code reaches the body at instruction 35 with the lock taken (next `n + 1`, serving `n`, no waiters; it
    was `n`, `n`, `0`), only the scratch slots and the lock's words changed, and everything the body relies on. -/
theorem locksT_take {reserved : Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {L : Lay D} {P : Programm D}
    {f : D.Fn} {fp : W} {K Ks lo : Nat} {rp cfp : W} {σ0 : World D} {ρ0 : Env D (D.params f)} {ex : Int × Int}
    {Γ : Ctx} {Λ : List (Res D)} {Lk : D.Lock} {H : List D.Lock} {bo : Option Int} {cb : List II} {m : Mem}
    {pc : W} {σ : World D} {ρ : Env D Γ} {a s : Nat}
    (ha : L.lk Lk = a) (hsd : frei Γ reserved = s) (hs18 : s + 18 ≤ Ks) (hW : WIn L fp Ks K)
    (hlo0 : lo = (functionFrame P f).internalResult) (hlo2 : lo ≤ s)
    (hp : PreS L m pc fp K s (locksCodeT L a s cb ex.1 ex.2) ρ reserved)
    (hu : Umf L A C dv m fp Ks K H) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ)
    (hH : HeldIn H Λ bo) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang Lk)
    (hb : ∀ c, bo = some c → c ≤ D.rang Lk) :
    ∃ m1 n f1, LE m pc fp s a (locksCodeT L a s cb ex.1 ex.2) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 35), fp⟩ m1 ∧
      m.rd64 (BitVec.ofNat 64 a) = some n ∧ m.rd64 (BitVec.ofNat 64 (a + 8)) = some n ∧
      m.rd64 (BitVec.ofNat 64 (a + 16)) = some 0 ∧ LS m m1 fp s a f1 (n + 1) n 0 ∧
      PreS L m1 (pc + BitVec.ofNat 64 (16 * 35)) fp K s cb ρ reserved ∧
      Umf L A C dv m1 fp (Ks - 1) K (Lk :: H) ∧ Kopf L f m1 fp K rp cfp ρ0 P σ0 ∧
      WeltAt m1 L (σ.nimmt Lk) := by
  have hy := hu.sync
  have hla := hy.lay Lk
  rw [ha] at hla
  have hsye := hy.sye
  have htopW := hW.top
  have hord := hW.ord
  have hks := hW.ks
  have hK31 := hp.small
  have hFB3 : FB = 4 := rfl
  have hFramePrefix := functionFrame_prefix P f
  have hfa : fp.toNat + 8 * (s + 18) ≤ a := by omega
  have hfh : fp.toNat + 8 * (s + 18) ≤ L.hi := by omega
  have hfl : fp.toNat + 8 * (s + 18) ≤ L.lo := by omega
  have ha31 : a + 24 < 2 ^ 31 := by omega
  obtain ⟨At0, Atb, -⟩ := locksT_at L a s cb ex.1 ex.2
  have hlen := locksCodeT_len L a s cb ex.1 ex.2
  have hw0 : all m.wr (BitVec.ofNat 64 a) 8 = true := by simpa [ha] using hy.wr Lk 0 (by omega)
  have hw1 : all m.wr (BitVec.ofNat 64 (a + 8)) 8 = true := by simpa [ha] using hy.wr Lk 1 (by omega)
  have hw2 : all m.wr (BitVec.ofNat 64 (a + 16)) 8 = true := by simpa [ha] using hy.wr Lk 2 (by omega)
  have hcf := hp.far
  have E0 : LE m pc fp s a (locksCodeT L a s cb ex.1 ex.2) :=
    ⟨frameOK_sub hp.frame (by omega), by omega, hfa, ha31, hw0, hw1, hw2, hp.code, codeFar_sub2 hcf (by omega)⟩
  obtain ⟨n, u, hn, hu', hwt, -, hfree⟩ := hy.zust Lk
  rw [ha] at hn hu' hwt
  have hnu : n = u := hfree (hH.frei hr hb)
  rw [← hnu] at hu'
  have hwt' : m.rd64 (BitVec.ofNat 64 (a + 16)) = some 0 := hwt
  obtain ⟨f0, hL0⟩ := ls_init E0 hn hu' hwt'
  obtain ⟨m1, f1, s1, hL1⟩ := nimmT_paar E0 hL0 (p := 0) At0 rfl
  have s1' : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 35), fp⟩ m1 := star_cast s1 (by simp) rfl
  -- the body's start
  have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * 35)) fp K s cb ρ reserved :=
    ⟨by omega, hp.small, ⟨hp.frame.lt, fun i hi => by rw [hL1.ag.rd]; exact hp.frame.rd i hi,
      fun i hi => by rw [hL1.ag.wr]; exact hp.frame.wr i hi⟩,
     At.codeAt (hL1.ag.codeAt hfa ha31 hp.code hcf) Atb, At.codeFar hcf (by rw [hlen]; omega),
     hL1.ag.envAt hp.env (by omega) hfa ha31, trivial, wstab_true _ _⟩
  have hag : AgreeK fp s (L.lk Lk) m m1 := by rw [ha]; exact hL1.ag
  have ho1 : m1.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some (n + 1) := by rw [ha]; exact hL1.o
  have hc1 : m1.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some n := by rw [ha]; exact hL1.c
  have hw1' : m1.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some 0 := by rw [ha]; exact hL1.w
  have sync1 : TicketSync m1 L fp (Ks - 1) (Lk :: H) :=
    (hy.mono (Nat.sub_le Ks 1)).nimmt hag hfh ho1 hc1 hw1'
  have hu1 : Umf L A C dv m1 fp (Ks - 1) K (Lk :: H) :=
    ⟨hL1.ag.pcode hu.code hfa ha31, by rw [hL1.ag.rd_low (i := 2) (by omega) hfa ha31]; exact hu.depth, hu.big,
     sync1, hu.hiK⟩
  have hk1 : Kopf L f m1 fp K rp cfp ρ0 P σ0 := AgreeK.kopf hk hL1.ag (by omega) hfa ha31
  have hWa1 : WeltAt m1 L (σ.nimmt Lk) := hL1.ag.weltAt hWa hW.lay hfl (by omega)
  exact ⟨m1, n, f1, E0, s1', hn, hu', hwt', hL1, hp1, hu1, hk1, hWa1⟩

end Gabbro.Stage0.Senke
