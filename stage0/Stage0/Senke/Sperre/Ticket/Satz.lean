/-
  File:      stage0/Stage0/Senke/Sperre/Ticket/Satz.lean
  Subject:   `locks Lk { body }` on the ticket code (`locksCodeT`), the `locks` case of `lowS_ok` (`lowS_ok_locks`):
              take (`locksT_take`), the body, and on each way out -- its end, `leave`, `next` -- the give
              (`locksT_give`) before the jump; a stop in the body stops the whole. Stated over what the proof uses of
              the body's run (one hypothesis per outcome: its endpoint, an `AgreeW` change, the new environment and
              world, the protected slots), so that `lowS_ok_locks` takes each conjunct for one outcome of G.
-/
module
public import Stage0.Senke.Sperre.Ticket.Anfang
public import Stage0.Senke.Sperre.Ticket.Ausgang
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- **One way out**: the body leaves at `e`, the give at instruction `p` (where `e` points), the jump at `q = p + 16`
    to `tgt`. The whole reaches `tgt` with the body's environment and its world after the give. -/
theorem locksT_exit {reserved : Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {L : Lay D} {P : Programm D}
    {f : D.Fn} {fp : W} {K Ks lo : Nat} {rp cfp : W} {σ0 : World D} {ρ0 : Env D (D.params f)} {pr : List Nat}
    {ex : Int × Int} {Γ : Ctx} {Λ : List (Res D)} {Lk : D.Lock} {H : List D.Lock} {bo : Option Int} {cb : List II}
    {m : Mem} {pc : W} {σ σ' : World D} {ρ ρ' : Env D Γ} {a s p q : Nat} {X : Int} {e tgt : W}
    (ha : L.lk Lk = a) (hsd : frei Γ reserved = s) (hs18 : s + 18 ≤ Ks) (hW : WIn L fp Ks K)
    (hlo0 : lo = (functionFrame P f).internalResult) (hlo2 : lo ≤ s) (hpr : ∀ j ∈ pr, j < s)
    (hp : PreS L m pc fp K s (locksCodeT L a s cb ex.1 ex.2) ρ reserved)
    (hu : Umf L A C dv m fp Ks K H) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ)
    (hH : HeldIn H Λ bo) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang Lk)
    (hb : ∀ c, bo = some c → c ≤ D.rang Lk)
    (hAt : At (locksCodeT L a s cb ex.1 ex.2) p (gibT L a s)) (he : e = pc + BitVec.ofNat 64 (16 * p))
    (hq : q = p + 16) (hj : (locksCodeT L a s cb ex.1 ex.2)[q]? = some (ci 18 X 0 0)) (hX : lit32 X = true)
    (htgt : pc + BitVec.ofNat 64 (16 * q) + BitVec.ofInt 64 X = tgt)
    (hbody : ∀ m1, PreS L m1 (pc + BitVec.ofNat 64 (16 * 35)) fp K s cb ρ reserved →
      Umf L A C dv m1 fp (Ks - 1) K (Lk :: H) → Kopf L f m1 fp K rp cfp ρ0 P σ0 → WeltAt m1 L (σ.nimmt Lk) →
      HeldIn (Lk :: H) (Res.held Lk :: Λ) bo →
      Reach L fp lo K pr ⟨pc + BitVec.ofNat 64 (16 * 35), fp⟩ m1 e σ' ρ' reserved) :
    Reach L fp lo K pr ⟨pc, fp⟩ m tgt (σ'.gibt Lk) ρ' reserved := by
  subst he htgt hq
  obtain ⟨m1, n, f1, E0, s1, h0n, h0u, h0w, hL1, hp1, hu1, hk1, hWa1⟩ :=
    locksT_take ha hsd hs18 hW hlo0 hlo2 hp hu hk hWa hH hr hb
  obtain ⟨m2, s2, a2, en2, hw2, kp2⟩ := hbody m1 hp1 hu1 hk1 hWa1 hH.nimmt
  obtain ⟨m3, s3, a3, k3⟩ := locksT_give ha hW hu.sync hs18 hlo2 E0 hp.far h0n h0u h0w hL1 hAt a2
  have hfa := E0.far
  have ha31 := E0.top
  have hla := hu.sync.lay Lk
  rw [ha] at hla
  have hks := hW.ks
  have htopW := hW.top
  have hord := hW.ord
  have hfl : fp.toNat + 8 * (s + 18) ≤ L.lo := by omega
  have en3 : EnvAt L m3 fp ρ' reserved := k3.envAt en2 (Nat.le_of_eq hsd) hfa ha31
  have hw3 : WeltAt m3 L (σ'.gibt Lk) := k3.weltAt hw2 hW.lay hfl (by omega)
  have kp3 : Keeps fp pr m m3 := fun j hj => by
    have := hpr j hj
    rw [k3.rd_low (by omega) hfa ha31, kp2 j hj, hL1.ag.rd_low (by omega) hfa ha31]
  have s4 := code_jmp (fp := fp) (codeAt_agreeWIn hW a3 hp.code hp.far) hj hX
  exact ⟨m3, s1.trans (s2.trans (s3.trans s4)), a3, en3, hw3, kp3⟩

/-- **A stop in the body** stops the whole. -/
theorem locksT_stop {reserved : Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {L : Lay D} {P : Programm D}
    {f : D.Fn} {fp : W} {K Ks lo : Nat} {rp cfp : W} {σ0 : World D} {ρ0 : Env D (D.params f)}
    {ex : Int × Int} {Γ : Ctx} {Λ : List (Res D)} {Lk : D.Lock} {H : List D.Lock} {bo : Option Int} {cb : List II}
    {m : Mem} {pc : W} {σ : World D} {ρ : Env D Γ} {a s c : Nat}
    (ha : L.lk Lk = a) (hsd : frei Γ reserved = s) (hs18 : s + 18 ≤ Ks) (hW : WIn L fp Ks K)
    (hlo0 : lo = (functionFrame P f).internalResult) (hlo2 : lo ≤ s)
    (hp : PreS L m pc fp K s (locksCodeT L a s cb ex.1 ex.2) ρ reserved)
    (hu : Umf L A C dv m fp Ks K H) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ)
    (hH : HeldIn H Λ bo) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang Lk)
    (hb : ∀ c, bo = some c → c ≤ D.rang Lk)
    (hbody : ∀ m1, PreS L m1 (pc + BitVec.ofNat 64 (16 * 35)) fp K s cb ρ reserved →
      Umf L A C dv m1 fp (Ks - 1) K (Lk :: H) → Kopf L f m1 fp K rp cfp ρ0 P σ0 → WeltAt m1 L (σ.nimmt Lk) →
      HeldIn (Lk :: H) (Res.held Lk :: Λ) bo → Stops ⟨pc + BitVec.ofNat 64 (16 * 35), fp⟩ m1 c) :
    Stops ⟨pc, fp⟩ m c := by
  obtain ⟨m1, n, f1, E0, s1, -, -, -, -, hp1, hu1, hk1, hWa1⟩ :=
    locksT_take ha hsd hs18 hW hlo0 hlo2 hp hu hk hWa hH hr hb
  exact Stops.prefix s1 (hbody m1 hp1 hu1 hk1 hWa1 hH.nimmt)

/-- **`locks Lk { body }` on the ticket code**: for the body's end, its `leave` (`16 * 17` bytes after its end) and
    its `next` (`16 * 34` bytes after its end) the code reaches the end of the whole, `ex.1` and `ex.2` past it, with
    the body's environment, its world after the give, and an `AgreeW` change; a stop in the body stops the whole.
    The lock `Lk` is free at the start (`HeldIn H Λ bo`, the rank premise `hr`, the floor `hb`); the body runs with
    the ticket state against `Lk :: H` and the tie for `.held Lk :: Λ`. -/
theorem locks_okT {reserved : Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {L : Lay D} {P : Programm D}
    {f : D.Fn} {fp : W} {K Ks lo : Nat} {rp cfp : W} {σ0 : World D} {ρ0 : Env D (D.params f)} {pr : List Nat}
    {ex : Int × Int} {Γ : Ctx} {Λ : List (Res D)} {Lk : D.Lock} {H : List D.Lock} {bo : Option Int} {cb : List II}
    {m : Mem} {pc : W} {σ : World D} {ρ : Env D Γ}
    (hex1 : lit32 (16 + ex.1 + 16 * 17) = true) (hex2 : lit32 (16 + ex.2) = true)
    (hs18 : frei Γ reserved + 18 ≤ Ks) (hW : WIn L fp Ks K) (hlo0 : lo = (functionFrame P f).internalResult)
    (hlo2 : lo ≤ frei Γ reserved) (hpr : ∀ j ∈ pr, j < frei Γ reserved)
    (hp : PreS L m pc fp K (frei Γ reserved) (locksCodeT L (L.lk Lk) (frei Γ reserved) cb ex.1 ex.2) ρ reserved)
    (hu : Umf L A C dv m fp Ks K H) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ)
    (hH : HeldIn H Λ bo) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang Lk)
    (hb : ∀ c, bo = some c → c ≤ D.rang Lk) :
    (∀ (σ' : World D) (ρ' : Env D Γ),
      (∀ m1, PreS L m1 (pc + BitVec.ofNat 64 (16 * 35)) fp K (frei Γ reserved) cb ρ reserved →
        Umf L A C dv m1 fp (Ks - 1) K (Lk :: H) → Kopf L f m1 fp K rp cfp ρ0 P σ0 → WeltAt m1 L (σ.nimmt Lk) →
        HeldIn (Lk :: H) (Res.held Lk :: Λ) bo →
        Reach L fp lo K pr ⟨pc + BitVec.ofNat 64 (16 * 35), fp⟩ m1
          (pc + BitVec.ofNat 64 (16 * 35) + BitVec.ofNat 64 (16 * cb.length)) σ' ρ' reserved) →
      Reach L fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * (locksCodeT L (L.lk Lk) (frei Γ reserved) cb ex.1 ex.2).length))
        (σ'.gibt Lk) ρ' reserved) ∧
    (∀ (σ' : World D) (ρ' : Env D Γ),
      (∀ m1, PreS L m1 (pc + BitVec.ofNat 64 (16 * 35)) fp K (frei Γ reserved) cb ρ reserved →
        Umf L A C dv m1 fp (Ks - 1) K (Lk :: H) → Kopf L f m1 fp K rp cfp ρ0 P σ0 → WeltAt m1 L (σ.nimmt Lk) →
        HeldIn (Lk :: H) (Res.held Lk :: Λ) bo →
        Reach L fp lo K pr ⟨pc + BitVec.ofNat 64 (16 * 35), fp⟩ m1
          (pc + BitVec.ofNat 64 (16 * 35) + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 (16 * 17))
          σ' ρ' reserved) →
      Reach L fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * (locksCodeT L (L.lk Lk) (frei Γ reserved) cb ex.1 ex.2).length) +
          BitVec.ofInt 64 ex.1) (σ'.gibt Lk) ρ' reserved) ∧
    (∀ (σ' : World D) (ρ' : Env D Γ),
      (∀ m1, PreS L m1 (pc + BitVec.ofNat 64 (16 * 35)) fp K (frei Γ reserved) cb ρ reserved →
        Umf L A C dv m1 fp (Ks - 1) K (Lk :: H) → Kopf L f m1 fp K rp cfp ρ0 P σ0 → WeltAt m1 L (σ.nimmt Lk) →
        HeldIn (Lk :: H) (Res.held Lk :: Λ) bo →
        Reach L fp lo K pr ⟨pc + BitVec.ofNat 64 (16 * 35), fp⟩ m1
          (pc + BitVec.ofNat 64 (16 * 35) + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 (16 * 34))
          σ' ρ' reserved) →
      Reach L fp lo K pr ⟨pc, fp⟩ m
        (pc + BitVec.ofNat 64 (16 * (locksCodeT L (L.lk Lk) (frei Γ reserved) cb ex.1 ex.2).length) +
          BitVec.ofInt 64 ex.2) (σ'.gibt Lk) ρ' reserved) ∧
    (∀ c : Nat,
      (∀ m1, PreS L m1 (pc + BitVec.ofNat 64 (16 * 35)) fp K (frei Γ reserved) cb ρ reserved →
        Umf L A C dv m1 fp (Ks - 1) K (Lk :: H) → Kopf L f m1 fp K rp cfp ρ0 P σ0 → WeltAt m1 L (σ.nimmt Lk) →
        HeldIn (Lk :: H) (Res.held Lk :: Λ) bo → Stops ⟨pc + BitVec.ofNat 64 (16 * 35), fp⟩ m1 c) →
      Stops ⟨pc, fp⟩ m c) := by
  rw [locksCodeT_len]
  obtain ⟨-, -, Atg1, hj1, Atg2, hj2, Atg3, hj3⟩ := locksT_at L (L.lk Lk) (frei Γ reserved) cb ex.1 ex.2
  have e35 : pc + BitVec.ofNat 64 (16 * 35) + BitVec.ofNat 64 (16 * cb.length) =
      pc + BitVec.ofNat 64 (16 * (35 + cb.length)) := pc_jump pc 35 cb.length
  refine ⟨fun σ' ρ' hbody => ?_, fun σ' ρ' hbody => ?_, fun σ' ρ' hbody => ?_, fun c hbody => ?_⟩
  · -- the end: give at 35 + cb, jump over both stubs
    refine locksT_exit rfl rfl hs18 hW hlo0 hlo2 hpr hp hu hk hWa hH hr hb Atg1 e35
      (q := 51 + cb.length) (by omega) hj1 (by rw [gibT_len]; decide) ?_ hbody
    rw [gibT_len, show (16 * (1 + 2 * ((8 + 8 : Nat) + 1)) : Int) = 16 * ((35 : Nat) : Int) by rfl,
      tgt_nat (a := 16 * (51 + cb.length)) (b := 16 * (cb.length + 86)) (by omega)]
  · -- `leave`: give at 52 + cb, on to `ex.1`
    have he : pc + BitVec.ofNat 64 (16 * 35) + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 (16 * 17) =
        pc + BitVec.ofNat 64 (16 * (52 + cb.length)) := by
      rw [e35, show (16 * 17 : Int) = 16 * ((17 : Nat) : Int) by rfl,
        tgt_nat (a := 16 * (35 + cb.length)) (b := 16 * (52 + cb.length)) (by omega)]
    refine locksT_exit rfl rfl hs18 hW hlo0 hlo2 hpr hp hu hk hWa hH hr hb Atg2 he
      (q := 68 + cb.length) (by omega) hj2 (by rw [gibT_len]; exact hex1) ?_ hbody
    rw [gibT_len, show (16 + ex.1 + 16 * ((8 + 8 : Nat) + 1) : Int) = ex.1 + 16 * ((18 : Nat) : Int) by
      push_cast; omega, tgt_eq (a := 16 * (68 + cb.length)) (b := 16 * (cb.length + 86)) (by omega)]
  · -- `next`: give at 69 + cb, on to `ex.2`
    have he : pc + BitVec.ofNat 64 (16 * 35) + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 (16 * 34) =
        pc + BitVec.ofNat 64 (16 * (69 + cb.length)) := by
      rw [e35, show (16 * 34 : Int) = 16 * ((34 : Nat) : Int) by rfl,
        tgt_nat (a := 16 * (35 + cb.length)) (b := 16 * (69 + cb.length)) (by omega)]
    refine locksT_exit rfl rfl hs18 hW hlo0 hlo2 hpr hp hu hk hWa hH hr hb Atg3 he
      (q := 85 + cb.length) (by omega) hj3 hex2 ?_ hbody
    rw [show (16 + ex.2 : Int) = ex.2 + 16 * ((1 : Nat) : Int) by push_cast; omega,
      tgt_eq (a := 16 * (85 + cb.length)) (b := 16 * (cb.length + 86)) (by omega)]
  · exact locksT_stop rfl rfl hs18 hW hlo0 hlo2 hp hu hk hWa hH hr hb hbody

end Gabbro.Stage0.Senke
