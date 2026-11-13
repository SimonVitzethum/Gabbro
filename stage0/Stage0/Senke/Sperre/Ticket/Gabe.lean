/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Gabe.lean
  Subject:   The two compositions of a change under pending releases (lock stage 3; `AgreeWR`, `RetZR`, `RetWhyR`
              in `Rueckkehr/Pending.lean`): a run of `Agree`, the chain and `Agree` again is one
              (`AgreeWR.ofKette`); the take of `locks Lk` before a change under `Lk :: Hs` makes one under `Hs`
              (`AgreeWR.nimmt`).
-/
module
public import Stage0.Senke.Sperre.Ticket.GibKette
public import Stage0.Senke.Rueckkehr.Pending
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- The internal result lies above the frame header: slot 4 or higher. -/
theorem functionFrame_lo4 (P : Programm D) (f : D.Fn) : 4 ≤ (functionFrame P f).internalResult := by
  simp only [functionFrame, FrameLayout.internalResult, FrameLayout.ensParams,
    FrameLayout.ensReserved, FrameLayout.parameterWords, FB]
  omega


/-- **A way out through the chain**: a change of the frame and the world (`AgreeW`), the chain of the held locks
    `Hs` (`AgreeKL`, each left free with both tickets one higher), a change of the frame and the world again: one
    change under the pending releases `Hs`. -/
theorem AgreeWR.ofKette {L : Lay D} {fp : W} {K Ks s : Nat} {H Hs : List D.Lock} {m m3 m4 m5 : Mem}
    (hy : TicketSync m L fp Ks H) (hHs : ∀ M, M ∈ Hs → M ∈ H) (hK : KetteOK L fp s) (hord : L.lo ≤ L.hi)
    (hKhi : fp.toNat + 8 * K ≤ L.hi) (h2s : 2 ≤ s) (hsK : s + 18 ≤ K)
    (a : AgreeW L fp 2 K m m3) (k : AgreeKL L fp s Hs m3 m4) (c : AgreeW L fp 2 K m4 m5)
    (hfin : ∀ Lk, Lk ∈ Hs → ∀ u : W, m3.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some u →
      m4.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some (u + 1) ∧
      m4.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some (u + 1) ∧ m4.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some 0) :
    AgreeWR L fp 2 K Hs m m5 := by
  refine ⟨c.rd.trans (k.rd.trans a.rd), c.wr.trans (k.wr.trans a.wr), fun x hx hw hs => ?_,
    fun Lk fern hn => ?_, fun Lk fern hm => ?_⟩
  · have nl : ∀ Lk, Lk ∈ Hs → ¬ InLk (L.lk Lk) x := fun Lk _ ⟨h1, h2⟩ => by
      obtain ⟨l1, l2⟩ := hK.lay Lk
      exact hs ⟨by omega, by omega, by omega, hK.sye⟩
    exact (c.b x hx hw hs).trans ((k.b x (fun ⟨h1, h2⟩ => hx ⟨by omega, by omega⟩) nl).trans (a.b x hx hw hs))
  · exact (a.sync Lk fern).trans ((k.ticketKlasse hK hn).trans (c.sync Lk fern))
  · have hy3 := hy.agreeW a hKhi
    have mid : TicketGabe m3 m4 (L.lk Lk) := fun n0 v0 w0 e1 e2 e3 => by
      obtain ⟨u, hn, hu, hw⟩ := hy3.mine (hHs Lk hm)
      have qn : n0 = u + 1 := Option.some_inj.mp (e1.symm.trans hn)
      have qs : v0 = u := Option.some_inj.mp (e2.symm.trans hu)
      have qw : w0 = 0 := Option.some_inj.mp (e3.symm.trans hw)
      obtain ⟨f1, f2, f3⟩ := hfin Lk hm u hu
      refine ⟨u + 1, u + 1, 0, f1, f2, f3, ?_, qw.symm⟩
      have key : ∀ a : W, a + 1 - (a + 1) + 1 = a + 1 - a := by intro a; bv_omega
      rw [qn, qs]
      exact key u
    exact ((a.sync Lk fern).gabe mid).klasse (c.sync Lk fern)

/-- **The take before a way out**: the take of the free lock `Lk` (`AgreeK`, the lock read `n`, `n`, `0` before and
    `n + 1`, `n`, `0` after), then a change under the pending releases `Lk :: Hs`, is a change under `Hs`: `Lk` ends
    with its class, every other lock as the later change left it. -/
theorem AgreeWR.nimmt {L : Lay D} {fp : W} {K Ks s : Nat} {H Hs : List D.Lock} {Lk : D.Lock} {m m1 m' : Mem}
    {n : W} (hy : TicketSync m L fp Ks H) (hord : L.lo ≤ L.hi) (hfh : fp.toNat + 8 * (s + 18) ≤ L.hi)
    (h2s : 2 ≤ s) (hsK : s + 18 ≤ K) (hnot : Lk ∉ Hs) (ha : AgreeK fp s (L.lk Lk) m m1)
    (h0n : m.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some n) (h0u : m.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some n)
    (h0w : m.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some 0)
    (h1n : m1.rd64 (BitVec.ofNat 64 (L.lk Lk)) = some (n + 1))
    (h1u : m1.rd64 (BitVec.ofNat 64 (L.lk Lk + 8)) = some n)
    (h1w : m1.rd64 (BitVec.ofNat 64 (L.lk Lk + 16)) = some 0)
    (h : AgreeWR L fp 2 K (Lk :: Hs) m1 m') : AgreeWR L fp 2 K Hs m m' := by
  refine ⟨h.rd.trans ha.rd, h.wr.trans ha.wr, fun x hx hxw hxy => ?_, fun Lk' fern hn => ?_,
    fun Lk' fern hm => ?_⟩
  · rw [h.b x hx hxw hxy]
    by_cases hxl : InLk (L.lk Lk) x
    · exfalso
      obtain ⟨h1, h2⟩ := hxl
      obtain ⟨l1, l2⟩ := hy.lay Lk
      exact hxy ⟨by omega, by omega, by omega, hy.sye⟩
    · exact ha.b x (fun ⟨h1, h2⟩ => hx ⟨by omega, by omega⟩) hxl
  · by_cases hq : Lk' = Lk
    · rw [hq] at fern ⊢
      intro t0 v0 z0 g1 g2 g3
      have q1 : t0 = n := Option.some_inj.mp (g1.symm.trans h0n)
      have q2 : v0 = n := Option.some_inj.mp (g2.symm.trans h0u)
      have q3 : z0 = 0 := Option.some_inj.mp (g3.symm.trans h0w)
      obtain ⟨n', s', w', e1, e2, e3, hd, hwq⟩ :=
        h.gabe Lk fern (List.mem_cons.mpr (Or.inl rfl)) (n + 1) n 0 h1n h1u h1w
      refine ⟨n', s', w', e1, e2, e3, ?_, by rw [hwq, q3]⟩
      have key : ∀ a b c : W, a + 1 = c + 1 - c → a = b - b := by intro a b c h; bv_omega
      rw [q1, q2]
      exact key _ n n hd
    · have hd' := hy.dis Lk' Lk hq
      obtain ⟨l1, l2⟩ := hy.lay Lk'
      have hsye := hy.sye
      have hn' : Lk' ∉ Lk :: Hs := fun hc => by
        rcases List.mem_cons.mp hc with e | e
        · exact hq e
        · exact hn e
      exact (AgreeK.ticketKlasse ha (by omega) (by omega) hd').trans (h.sync Lk' fern hn')
  · have hq : Lk' ≠ Lk := fun e => hnot (e ▸ hm)
    have hd' := hy.dis Lk' Lk hq
    obtain ⟨l1, l2⟩ := hy.lay Lk'
    have hsye := hy.sye
    exact (AgreeK.ticketKlasse ha (by omega) (by omega) hd').gabe
      (h.gabe Lk' fern (List.mem_cons.mpr (Or.inr hm)))

end Gabbro.Stage0.Senke
