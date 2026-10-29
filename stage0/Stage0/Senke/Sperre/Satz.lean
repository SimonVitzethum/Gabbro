/-
  File:      stage0/Stage0/Senke/Sperre/Satz.lean
  Subject:   `ir_sim` for `locks Lk { body }` (`locksCode`): G runs the body on `σ.nimmt Lk` and gives the lock back on
             its way out (`mapWelt (·.gibt Lk)`); the code takes the lock (`nimm_paar`), runs the body, and on each way
             out -- its end, `leave`, `next` -- gives it (`gib_paar`) before the jump. The lock words end as they
             began, so the whole is a statement's change (`AgreeW`); the body has no `ret` (`retFreiB_istZ`), and a
             stop in it stops the whole.
-/
import Stage0.Senke.Sperre.Paar
import Stage0.Senke.Sperre.OhneRet
import Stage0.Senke.Anweisung.Simulation

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem locksCode_len (L : Lay D) (a s : Nat) (cb : List II) (x y : Int) :
    (locksCode L a s cb x y).length = cb.length + 138 := by
  simp only [locksCode, List.length_append, nimmC_len, gibC_len, List.length_singleton]; omega

theorem At.of_eq {code xs ys zs : List II} {p : Nat} (h : code = xs ++ ys ++ zs) (hp : p = xs.length) :
    At code p ys := by subst h hp; exact At.mid xs ys zs

theorem locks_at (L : Lay D) (a s : Nat) (cb : List II) (x y : Int) :
    At (locksCode L a s cb x y) 0 (nimmC L a s) ∧
    At (locksCode L a s cb x y) 48 cb ∧
    At (locksCode L a s cb x y) (48 + cb.length) (gibC L a s) ∧
    (locksCode L a s cb x y)[77 + cb.length]? = some (ci 18 (16 * (1 + 2 * ((gibC L a s).length + 1))) 0 0) ∧
    At (locksCode L a s cb x y) (78 + cb.length) (gibC L a s) ∧
    (locksCode L a s cb x y)[107 + cb.length]? = some (ci 18 (16 + x + 16 * ((gibC L a s).length + 1)) 0 0) ∧
    At (locksCode L a s cb x y) (108 + cb.length) (gibC L a s) ∧
    (locksCode L a s cb x y)[137 + cb.length]? = some (ci 18 (16 + y) 0 0) := by
  have hn := nimmC_len L a s
  have hg := gibC_len L a s
  refine ⟨At.of_eq (xs := []) (by simp only [locksCode, List.append_assoc, List.nil_append]; rfl) rfl, At.of_eq (xs := nimmC L a s) (by simp only [locksCode, List.append_assoc, List.nil_append]; rfl)
      (by omega), At.of_eq (xs := nimmC L a s ++ cb) (by simp only [locksCode, List.append_assoc, List.nil_append]; rfl) (by simp; omega),
    At.one (At.of_eq (xs := nimmC L a s ++ cb ++ gibC L a s) (by simp only [locksCode, List.append_assoc, List.nil_append]; rfl) (by simp; omega)),
    At.of_eq (xs := nimmC L a s ++ cb ++ gibC L a s ++ [_]) (by simp only [locksCode, List.append_assoc, List.nil_append]; rfl) (by simp; omega),
    At.one (At.of_eq (xs := nimmC L a s ++ cb ++ gibC L a s ++ [_] ++ gibC L a s) (by simp only [locksCode, List.append_assoc, List.nil_append]; rfl)
      (by simp; omega)),
    At.of_eq (xs := nimmC L a s ++ cb ++ gibC L a s ++ [_] ++ gibC L a s ++ [_]) (by simp only [locksCode, List.append_assoc, List.nil_append]; rfl)
      (by simp; omega),
    At.one (At.of_eq (xs := nimmC L a s ++ cb ++ gibC L a s ++ [_] ++ gibC L a s ++ [_] ++ gibC L a s)
      (by simp only [locksCode, List.append_assoc, List.nil_append]; rfl) (by simp; omega))⟩

theorem At.codeAt {m : Mem} {pc : W} {code xs : List II} {p : Nat} (hc : CodeAt m pc code) (h : At code p xs) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * p)) xs := fun k hk => by
  have e := h k hk
  rw [List.getElem?_eq_getElem hk] at e
  obtain ⟨hl, hx⟩ := List.getElem?_eq_some_iff.mp e
  have := hc (p + k) hl
  rw [hx, show pc + BitVec.ofNat 64 (16 * (p + k)) = pc + BitVec.ofNat 64 (16 * p) + BitVec.ofNat 64 (16 * k) by
    rw [pc_jump]] at this
  exact this

theorem At.codeFar {pc fp : W} {code xs : List II} {p K : Nat} (hf : CodeFar pc code.length fp K)
    (hl : p + xs.length ≤ code.length) : CodeFar (pc + BitVec.ofNat 64 (16 * p)) xs.length fp K := by
  obtain ⟨h1, h2, h3⟩ := hf
  have := pc.isLt
  have hx : (pc + BitVec.ofNat 64 (16 * p)).toNat = pc.toNat + 16 * p := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨by rw [hx]; omega, h2, by rw [hx]; omega⟩

theorem code_jmp {m : Mem} {pc fp : W} {code : List II} {i : Nat} {X : Int} (hc : CodeAt m pc code)
    (hi : code[i]? = some (ci 18 X 0 0)) (hX : lit32 X = true) :
    Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 X, fp⟩ m := by
  obtain ⟨hl, hx⟩ := List.getElem?_eq_some_iff.mp hi
  have hI := hc i hl
  rw [hx] at hI
  simp only [ci] at hI
  refine Star.one (run_step (t := ⟨_, fp⟩) hI (by decide) ?_)
  simp only [op]
  refine f1_run hI ?_
  rw [sx_lit hX]
  exact .next

theorem tgt_nat {p : W} {a b n : Nat} (h : a + 16 * n = b) :
    p + BitVec.ofNat 64 a + BitVec.ofInt 64 (16 * (n : Int)) = p + BitVec.ofNat 64 b := by
  have := tgt_eq (p := p) (x := 0) h
  simpa using this

/-- **`locks Lk { body }`**: what G answers for the statement, the code does. -/
theorem locks_ok {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {L : Lay D} {P : Programm D} {f : D.Fn} {fp : W} {K Ks lo : Nat}
    {rp cfp : W} {σ0 : World D} {ρ0 : Env D (D.params f)} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {Lk : D.Lock}
    {body : Block D (vertragVon D f) l Γ (.held Lk :: Λ) (.held Lk :: Λ)} {cb : List II}
    (hrf : retFreiB body = true) (hex1 : lit32 (16 + ex.1 + 16 * 30) = true) (hex2 : lit32 (16 + ex.2) = true)
    (hs18 : frei Γ + 18 ≤ Ks) (hW : WIn L fp Ks K) (hlo0 : lo = FB + (D.params f).length) (hlo2 : lo ≤ frei Γ)
    (hpr : ∀ j ∈ pr, j < frei Γ) {m : Mem} {pc : W} {σ : World D} {ρ : Env D Γ}
    (hbody : ∀ m' σ', PreS L m' (pc + BitVec.ofNat 64 (16 * 48)) fp K (frei Γ) cb ρ → Umf L A C dv m' fp (Ks - 1) K →
      Kopf L f m' fp K rp cfp ρ0 → WeltAt m' L σ' →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc + BitVec.ofNat 64 (16 * 48), fp⟩ m'
        (pc + BitVec.ofNat 64 (16 * 48) + BitVec.ofNat 64 (16 * cb.length))
        (pc + BitVec.ofNat 64 (16 * 48) + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 (16 * 30))
        (pc + BitVec.ofNat 64 (16 * 48) + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 (16 * 60))
        (execBlock O passes R body σ' ρ))
    (hp : PreS L m pc fp K (frei Γ) (locksCode L (L.lk Lk) (frei Γ) cb ex.1 ex.2) ρ)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (locksCode L (L.lk Lk) (frei Γ) cb ex.1 ex.2).length))
      (pc + BitVec.ofNat 64 (16 * (locksCode L (L.lk Lk) (frei Γ) cb ex.1 ex.2).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (locksCode L (L.lk Lk) (frei Γ) cb ex.1 ex.2).length) + BitVec.ofInt 64 ex.2)
      ((execBlock O passes R body (σ.nimmt Lk) ρ).mapWelt (·.gibt Lk)) := by
  generalize ha : L.lk Lk = a at hp
  generalize hsd : frei Γ = s at hp hs18 hlo2 hpr hbody
  have hy := hu.sync
  have hme := hy.me
  have hla := hy.lay Lk
  rw [ha] at hla
  have hsye := hy.sye
  have htopW := hW.top
  have hord := hW.ord
  have hks := hW.ks
  have hK31 := hp.small
  have hFB3 : FB = 3 := rfl
  have hfa : fp.toNat + 8 * (s + 18) ≤ a := by omega
  have hfh : fp.toNat + 8 * (s + 18) ≤ L.hi := by omega
  have hfl : fp.toNat + 8 * (s + 18) ≤ L.lo := by omega
  have ha31 : a + 24 < 2 ^ 31 := by omega
  rw [locksCode_len]
  obtain ⟨At0, Atb, Atg1, hj1, Atg2, hj2, Atg3, hj3⟩ := locks_at L a s cb ex.1 ex.2
  have hlen := locksCode_len L a s cb ex.1 ex.2
  have hw0 : all m.wr (BitVec.ofNat 64 a) 8 = true := by simpa [ha] using hy.wr Lk 0 (by omega)
  have hw1 : all m.wr (BitVec.ofNat 64 (a + 8)) 8 = true := by simpa [ha] using hy.wr Lk 1 (by omega)
  have hw2 : all m.wr (BitVec.ofNat 64 (a + 16)) 8 = true := by simpa [ha] using hy.wr Lk 2 (by omega)
  have hcf := hp.far
  have E0 : LE m pc fp s a (locksCode L a s cb ex.1 ex.2) :=
    ⟨frameOK_sub hp.frame (by omega), by omega, hfa, ha31, hw0, hw1, hw2, hp.code, codeFar_sub2 hcf (by omega)⟩
  obtain ⟨o, c, ho, hc, hwt, hst⟩ := hy.zust Lk
  rw [ha] at ho hc hwt
  obtain ⟨f0, hL0⟩ := ls_init E0 ho hc hwt
  obtain ⟨m1, f1, c1, s1, hL1, hc1, hc1a, hc1b⟩ := nimm_paar E0 hL0 (p := 0) At0 hme hst (by omega) (by omega)
  have s1' : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 48), fp⟩ m1 := star_cast s1 (by simp) rfl
  -- the body's start
  have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * 48)) fp K s cb ρ :=
    ⟨by omega, hp.small, ⟨hp.frame.lt, fun i hi => by rw [hL1.ag.rd]; exact hp.frame.rd i hi,
      fun i hi => by rw [hL1.ag.wr]; exact hp.frame.wr i hi⟩,
     At.codeAt (hL1.ag.codeAt hfa ha31 hp.code hcf) Atb, At.codeFar hcf (by rw [hlen]; omega),
     hL1.ag.envAt hp.env (by omega) hfa ha31, trivial, wstab_true _ _⟩
  have sync1 : SyncOK m1 L fp (Ks - 1) := by
    have hy' := hy.mono (Nat.sub_le Ks 1)
    refine ⟨hy'.sb31, hy'.st, hy'.st31, hy'.lo, hy'.room, hy'.band, hy'.lay, hy'.sye, hy'.dis,
      fun Lk' k hk => by rw [hL1.ag.wr]; exact hy.wr Lk' k hk, fun Lk' => ?_⟩
    by_cases hq : Lk' = Lk
    · rw [hq]
      exact ⟨meW L fp, c1, by rw [ha]; exact hL1.o, by rw [ha]; exact hL1.c, by rw [ha]; exact hL1.w,
        Or.inr ⟨rfl, hc1a, hc1b⟩⟩
    · rw [← ha] at hL1
      exact hL1.ag.lockOK hy hq (Nat.sub_le Ks 1) hfh
  have hu1 : Umf L A C dv m1 fp (Ks - 1) K :=
    ⟨hL1.ag.pcode hu.code hfa ha31, by rw [hL1.ag.rd_low (i := 2) (by omega) hfa ha31]; exact hu.depth, hu.big,
     sync1, hu.hiK⟩
  have hk1 : Kopf L f m1 fp K rp cfp ρ0 := AgreeK.kopf hk hL1.ag (by omega) hfa ha31
  have hWa1 : WeltAt m1 L (σ.nimmt Lk) := hL1.ag.weltAt hWa hW.lay hfl (by omega)
  have ih := hbody m1 (σ.nimmt Lk) hp1 hu1 hk1 hWa1
  -- the give, on every way out
  have give : ∀ p q, At (locksCode L a s cb ex.1 ex.2) p (gibC L a s) → q = p + 29 → ∀ m2, AgreeW L fp lo K m1 m2 →
      ∃ m3, Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m2 ⟨pc + BitVec.ofNat 64 (16 * q), fp⟩ m3 ∧
        AgreeW L fp lo K m m3 ∧ AgreeK fp s a m2 m3 := by
    intro p q hAt hq m2 a2
    subst hq
    have keep2 : ∀ y, a ≤ y → y ≤ a + 16 → m2.rd64 (BitVec.ofNat 64 y) = m1.rd64 (BitVec.ofNat 64 y) :=
      fun y h1 h2 => rd64_keep a2.rd fun j hj => a2.b _
        (fun ⟨_, h3⟩ => by rw [lk_byte (by omega) hj] at h3; omega)
        (fun ⟨_, h3⟩ => by rw [lk_byte (by omega) hj] at h3; omega)
    have E2 : LE m2 pc fp s a (locksCode L a s cb ex.1 ex.2) :=
      ⟨⟨E0.frame.lt, fun i hi => by rw [a2.rd, hL1.ag.rd]; exact E0.frame.rd i hi,
        fun i hi => by rw [a2.wr, hL1.ag.wr]; exact E0.frame.wr i hi⟩, E0.small, hfa, ha31,
       by rw [a2.wr, hL1.ag.wr]; exact hw0, by rw [a2.wr, hL1.ag.wr]; exact hw1, by rw [a2.wr, hL1.ag.wr]; exact hw2,
       codeAt_agreeWIn hW a2 (hL1.ag.codeAt hfa ha31 hp.code hcf) hcf, E0.cfar⟩
    obtain ⟨f2, hL2⟩ := ls_init E2 (by rw [keep2 _ (Nat.le_refl _) (by omega)]; exact hL1.o)
      (by rw [keep2 _ (by omega) (by omega)]; exact hL1.c) (by rw [keep2 _ (by omega) (by omega)]; exact hL1.w)
    obtain ⟨m3, f3, s3, hL3⟩ := gib_paar E2 hL2 hAt hme hst hc1
    refine ⟨m3, s3, ⟨by rw [hL3.ag.rd, a2.rd, hL1.ag.rd], by rw [hL3.ag.wr, a2.wr, hL1.ag.wr], fun x hx hxw => ?_⟩,
      hL3.ag⟩
    by_cases hxl : InLk a x
    · exact lk_bytes ha31 ho hc hwt hL3.o hL3.c hL3.w x hxl
    · have hxs : ¬ inSlots fp s (s + 18) x := fun ⟨h1, h2⟩ => hx ⟨by omega, by omega⟩
      rw [hL3.ag.b x hxs hxl, a2.b x hx hxw, hL1.ag.b x hxs hxl]
  -- what holds after the give
  have after : ∀ m2 m3 (σ' : World D) (ρ' : Env D Γ), AgreeK fp s a m2 m3 → EnvAt L m2 fp ρ' → WeltAt m2 L σ' → Keeps fp pr m1 m2 →
      EnvAt L m3 fp ρ' ∧ WeltAt m3 L (σ'.gibt Lk) ∧ Keeps fp pr m m3 := fun m2 m3 σ' ρ' k3 en hw kp =>
    ⟨k3.envAt en (Nat.le_of_eq hsd) hfa ha31, k3.weltAt hw hW.lay hfl (by omega),
     fun j hj => by
      have := hpr j hj
      rw [k3.rd_low (by omega) hfa ha31, kp j hj, hL1.ag.rd_low (by omega) hfa ha31]⟩
  have hcode3 : ∀ m3, AgreeW L fp lo K m m3 → CodeAt m3 pc (locksCode L a s cb ex.1 ex.2) :=
    fun m3 a3 => codeAt_agreeWIn hW a3 hp.code hcf
  have e48 : pc + BitVec.ofNat 64 (16 * 48) + BitVec.ofNat 64 (16 * cb.length) =
      pc + BitVec.ofNat 64 (16 * (48 + cb.length)) := pc_jump pc 48 cb.length
  have hZ := retFreiB_istZ (O := O) (passes := passes) (R := R) body hrf (σ.nimmt Lk) ρ
  generalize execBlock O passes R body (σ.nimmt Lk) ρ = out at ih hZ ⊢
  cases out with
  | ok σ' ρ' =>
    obtain ⟨m2, s2, a2, en2, hw2, kp2⟩ := ih
    obtain ⟨m3, s3, a3, k3⟩ := give (48 + cb.length) (77 + cb.length) Atg1 (by omega) m2 a2
    obtain ⟨en3, hw3, kp3⟩ := after m2 m3 σ' ρ' k3 en2 hw2 kp2
    have s4 := code_jmp (fp := fp) (hcode3 m3 a3) hj1 (by rw [gibC_len]; decide)
    refine ⟨m3, s1'.trans ((star_cast s2 rfl (by rw [e48])).trans (s3.trans (star_cast s4 rfl ?_))), a3, en3, hw3,
      kp3⟩
    rw [gibC_len, show (16 * (1 + 2 * ((7 + 7 + 4 + 3 + 8 : Nat) + 1)) : Int) = 16 * ((61 : Nat) : Int) by rfl,
      tgt_nat (a := 16 * (77 + cb.length)) (b := 16 * (cb.length + 138)) (by omega)]
  | leave hl σ' ρ' =>
    obtain ⟨m2, s2, a2, en2, hw2, kp2⟩ := ih
    obtain ⟨m3, s3, a3, k3⟩ := give (78 + cb.length) (107 + cb.length) Atg2 (by omega) m2 a2
    obtain ⟨en3, hw3, kp3⟩ := after m2 m3 σ' ρ' k3 en2 hw2 kp2
    have s4 := code_jmp (fp := fp) (hcode3 m3 a3) hj2 (by rw [gibC_len]; exact hex1)
    refine ⟨m3, s1'.trans ((star_cast s2 rfl ?_).trans (s3.trans (star_cast s4 rfl ?_))), a3, en3, hw3, kp3⟩
    · rw [e48, show (16 * 30 : Int) = 16 * ((30 : Nat) : Int) by rfl,
        tgt_nat (a := 16 * (48 + cb.length)) (b := 16 * (78 + cb.length)) (by omega)]
    · rw [gibC_len, show (16 + ex.1 + 16 * ((7 + 7 + 4 + 3 + 8 : Nat) + 1) : Int) = ex.1 + 16 * ((31 : Nat) : Int) by
        push_cast; omega, tgt_eq (a := 16 * (107 + cb.length)) (b := 16 * (cb.length + 138)) (by omega)]
  | next hn σ' ρ' =>
    obtain ⟨m2, s2, a2, en2, hw2, kp2⟩ := ih
    obtain ⟨m3, s3, a3, k3⟩ := give (108 + cb.length) (137 + cb.length) Atg3 (by omega) m2 a2
    obtain ⟨en3, hw3, kp3⟩ := after m2 m3 σ' ρ' k3 en2 hw2 kp2
    have s4 := code_jmp (fp := fp) (hcode3 m3 a3) hj3 hex2
    refine ⟨m3, s1'.trans ((star_cast s2 rfl ?_).trans (s3.trans (star_cast s4 rfl ?_))), a3, en3, hw3, kp3⟩
    · rw [e48, show (16 * 60 : Int) = 16 * ((60 : Nat) : Int) by rfl,
        tgt_nat (a := 16 * (48 + cb.length)) (b := 16 * (108 + cb.length)) (by omega)]
    · rw [show (16 + ex.2 : Int) = ex.2 + 16 * ((1 : Nat) : Int) by push_cast; omega,
        tgt_eq (a := 16 * (137 + cb.length)) (b := 16 * (cb.length + 138)) (by omega)]
  | zurueck σ' v => simp [istZ] at hZ
  | why σ' r => exact ih.elim
  | logik e => exact Stops.prefix s1' ih
  | hardware e => exact Stops.prefix s1' ih

end Gabbro.Stage0.Senke
