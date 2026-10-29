/-
  File:      stage0/Stage0/Senke/Anweisung/PufferTor.lean
  Subject:   **A gate with a buffer** (`torPuf_ok`): the arguments, the byte field packed into the frame from slot `B`,
             its address into the pointer's register, zeros, the number, the kernel (`TorOK.puf`), and -- for a
             writable buffer -- the bytes back into the field. Afterwards the memory holds the oracle's world and slot
             `s` the kernel's word.
-/
import Stage0.Senke.Anweisung.PufferLauf

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- A slot at or above `K` keeps its word under a change of the slots `lo .. K-1`. -/
theorem agree_rd_high {m m' : Runner.Mem} {fp : Runner.W} {lo K i R : Nat} (ha : Agree fp lo K m m')
    (hr : fp.toNat + 8 * R ≤ 2 ^ 64) (hi : K ≤ i) (hiR : i < R) :
    m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i)) := by
  have hs := slot_toNat (i := i) hr hiR
  simp only [Runner.Mem.rd64, ha.rd]
  rw [le_congr (fun j hj => ha.b _ fun ⟨h1, h2⟩ => by
    have := fp.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs] at h2
    omega)]

/-- The kernel's change of the buffer's bytes lies in the frame's slots from `B`. -/
theorem kern_agree_puf {m m' : Runner.Mem} {fp : Runner.W} {B Wn Ks : Nat} (hr : fp.toNat + 8 * Ks ≤ 2 ^ 64)
    (hB : B + Wn ≤ Ks) (hrd : m'.rd = m.rd) (hwr : m'.wr = m.wr)
    (hb : ∀ y : Runner.W, ¬ ((slot fp (BitVec.ofNat 64 B)).toNat ≤ y.toNat ∧
      y.toNat < (slot fp (BitVec.ofNat 64 B)).toNat + 8 * Wn) → m'.b y = m.b y) : Agree fp B Ks m m' := by
  refine ⟨hrd, hwr, fun x hx => hb x fun ⟨h1, h2⟩ => hx ⟨?_, ?_⟩⟩
  · rw [slot_toNat hr (by omega)] at h1; omega
  · rw [slot_toNat (K := Ks) hr (by omega)] at h2; omega

set_option maxHeartbeats 1600000 in
theorem torPuf_ok {L : Lay D} {O : Orakel D} [TorOK L O] {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {s : Nat} {b : TorB} (hb : L.tor a = some b)
    (hg : torGut b (D.aparams a).length = true) {j nt : Nat} {rw : Bool} {t : D.Tab} {f : D.Feld t}
    (hpp : ptrParam (D.aparams a) = some (j, nt, rw)) (htn : D.tabNr nt = some t) (hbf : L.byte t = some f)
    (hτ : D.typ t f = .int 0 255) (hc0 : 0 ≤ D.count t) {ca : List II} {ta : Nat}
    (hca : lowR L args (s + 1) = some (ca, ta)) {c B Wn : Nat} (hc : c = (D.count t).toNat)
    (hB : B = max ta (s + 7)) (hWn : Wn = pufW c) {P U : List II}
    (hP : P = packI L t f c B (B + Wn) (B + Wn + 1) Wn) (hU : U = if rw then unpackK L t f B (B + Wn + 1) c else [])
    {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (hKs : B + Wn + 3 ≤ Ks) (hW : WIn L fp Ks K)
    (hp : PreS m pc fp K s (((((ca ++ P) ++ [ci 17 ((s + 1 + j : Nat) : Int) (B : Int) 0]) ++
      zeroC (s + 1 + (D.aparams a).length) (6 - (D.aparams a).length)) ++ [ci 1 s b.nr 0, ci 23 s s 0]) ++ U) ρ)
    (hWa : WeltAt m L σ) :
    ∃ m' w, Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length) + 2 +
        U.length)), fp⟩ m' ∧ AgreeW L fp s K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 s)) = some w ∧
      WeltAt m' L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1 ∧
      (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).2 = rohW b (D.agruende a) w := by
  have hks := hW.ks
  have hlo := hW.lo
  have hord := hW.ord
  have hl := hW.lay
  have hd := hW.dis
  have hl3 := hl.2.2
  have hsmall := hp.small
  have hFs : FrameOK m fp Ks := frameOK_sub hp.frame hks
  have hroom := hFs.room
  have hroomK := hp.frame.room
  obtain ⟨hjn, hjt⟩ := ptrParam_spec hpp
  have hg' := hg
  simp only [torGut, Bool.and_eq_true, decide_eq_true_eq] at hg'
  obtain ⟨⟨hn6, _⟩, hnr⟩ := hg'
  have hB7 : s + 7 ≤ B := by omega
  have hBta : ta ≤ B := by omega
  have hfar := codeFar_sub2 hp.far hks
  simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil, zeroC_len] at hfar
  -- the arguments
  have hpU := hp.up (d' := s + 1) (by omega)
  have hq : PreS m pc fp K (s + 1) ca ρ := hpU.left.left.left.left.left
  have hpw := PreS.welt hq hks hWa hl (by omega)
  obtain ⟨m1, s1, a1, hA1⟩ := lowR_ok σ σ (fun _ h => h) args (s + 1) ca ta hca (by omega) (by omega) m pc ρ hpw
  have hW1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1.mono (Nat.zero_le _))
  -- the cells' words
  let ws : Nat → Runner.W := fun k => wAt m (L.elem t f k)
  have hcell : ∀ k, k < c → (L.elem t f k : Int) < 2 ^ 31 ∧ L.lo ≤ L.elem t f k ∧ L.elem t f k + 8 ≤ L.hi := fun k hk => by
    have := hl.1 t f k (by omega); exact ⟨by omega, this.1, this.2⟩
  have hwsm : ∀ k, k < c → m.rd64 (BitVec.ofNat 64 (L.elem t f k)) = some (ws k) := fun k hk => by
    obtain ⟨w, hw, _⟩ := hWa.1 t f k (by omega)
    show _ = some (wAt m (L.elem t f k))
    rw [wAt_of hw]; exact hw
  let Wc : Runner.Mem → Prop := fun m' => ∀ k, k < c → m'.rd64 (BitVec.ofNat 64 (L.elem t f k)) = some (ws k)
  have hWcs : WStab Wc fp Ks := fun m' m'' h a k hk => by
    have := hcell k hk
    rw [rd64_agree_out a (by omega) (.inr (by omega))]; exact h k hk
  have hWc1 : Wc m1 := hWcs m m1 hwsm (a1.mono (Nat.zero_le _))
  -- the packing
  have a1K := Agree.widen a1 hks
  have hnP := (hpU.left.left.left.left).next' a1K (by have := hp.ctx; omega) (by omega) (by omega)
  have hpP : Pre m1 (pc + BitVec.ofNat 64 (16 * ca.length)) fp Ks (B + Wn + 1) P ρ Wc :=
    ⟨by have := hp.ctx; omega, by omega, frameOK_sub hnP.frame hks, hnP.code, codeFar_sub2 hnP.far hks, hnP.env,
     hWc1, hWcs⟩
  rw [hP] at hpP
  obtain ⟨m2, s2, a2, hbuf⟩ := packI_ok (by omega) (by have := hp.ctx; omega)
    (fun k hk => by have := hcell k (by omega); omega) (fun k hk m' h => h k (by omega)) Wn (Nat.le_refl _) m1 _ hpP
  rw [← hP] at s2
  have hWc2 : Wc m2 := hWcs m1 m2 hWc1 (a2.mono (Nat.zero_le _))
  have a12 : Agree fp (s + 1) Ks m m2 := a1.trans (a2.mono (by omega))
  -- the buffer's address into the pointer's register
  have hnL := (hpU.left.left.left).next' (Agree.widen a12 hks) (by have := hp.ctx; omega) (by omega) (by omega)
  have s3 := lea_step (d := s + 1 + j) (a := B) hnL.code (frameOK_sub hnL.frame hks) (by omega) (by omega) (by omega)
  let m3 := write m2 (slot fp (BitVec.ofNat 64 (s + 1 + j))) 8 (slot fp (BitVec.ofNat 64 B)).toNat
  have a3 : Agree fp (s + 1 + j) Ks m2 m3 := agree_write hroom (Nat.le_refl _) (by omega) _
  have a13 : Agree fp (s + 1) Ks m m3 := a12.trans (a3.mono (by omega))
  -- zeros, the number
  have hnZ := (hpU.left.left).next' (Agree.widen a13 hks) (by have := hp.ctx; omega) (by omega) (by omega)
  simp only [List.length_append, List.length_singleton] at hnZ
  obtain ⟨m4, s4, a4, hz⟩ := zero_ok (K := s + 7) (by omega) _ _ m3 _ hnZ.code
    (by have := codeFar_sub2 (Ks := s + 7) hnZ.far (by omega); simpa [zeroC_len] using this)
    (frameOK_sub (frameOK_sub hnZ.frame hks) (by omega)) (by omega)
  have a4s : Agree fp (s + 1 + (D.aparams a).length) Ks m3 m4 := Agree.widen a4 (by omega)
  have hnN := hpU.left.next' (Agree.widen (a13.trans (a4s.mono (by omega))) hks) (by have := hp.ctx; omega) (Nat.le_refl _)
    (by omega)
  simp only [List.length_append, List.length_singleton, zeroC_len] at hnN
  have hcN : CodeAt m4 _ [ci 1 s b.nr 0] := codeAt_left (a := [ci 1 s b.nr 0]) (b := [ci 23 s s 0]) hnN.code
  have s5 := const_step (k := (b.nr : Int)) hcN (frameOK_sub hnN.frame hks) (by omega) (by omega) hnr
  let m5 := write m4 (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofInt 64 (b.nr : Int)).toNat
  have a5 : Agree fp s Ks m4 m5 := agree_write hroom (Nat.le_refl _) (by omega) _
  have a15 : Agree fp s Ks m m5 := (a13.mono (Nat.le_succ s)).trans ((a4s.mono (by omega)).trans a5)
  have hF5 : FrameOK m5 fp Ks := hFs.agree a15
  -- the request
  have hcS : CodeAt m5 (pc + BitVec.ofNat 64 (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length))) +
      BitVec.ofNat 64 (16 * 1)) [ci 23 s s 0] :=
    (codeAt_right (a := [ci 1 s b.nr 0]) (b := [ci 23 s s 0]) hnN.code).agree a5
      (codeFar_sub2 (codeFar_right (n := 1) (k := 1) hnN.far) hks)
  have h0 : m5.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofNat 64 b.nr) := by
    rw [← BitVec.ofInt_natCast]; exact rd64_write_same ((frameOK_sub hnN.frame hks).rd s (by omega))
  let fq : Nat → Runner.W := fun i => rdW m5 fp (s + 1 + i)
  let q : Runner.Req := ⟨BitVec.ofNat 64 b.nr, fq 0, fq 1, fq 2, fq 3, fq 4, fq 5⟩
  have hr : ∀ i, i < 6 → m5.rd64 (slot fp (BitVec.ofNat 64 (s + 1 + i))) = some (reqArg q i) := fun i hi => by
    rw [reqArg_mk _ fq i hi]; exact rd64_rdW hF5 (by omega)
  -- a slot of the arguments, from `m3` on: kept by the zeros above it and the number below it
  have h35 : ∀ i, i < (D.aparams a).length → rdW m5 fp (s + 1 + i) = rdW m3 fp (s + 1 + i) := fun i hi => by
    simp only [rdW, m5]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega)),
      agree_rd_low a4 (by omega) (by omega) (by omega)]
  have hpa : reqArg q j = slot fp (BitVec.ofNat 64 B) := by
    rw [reqArg_mk _ fq j (by omega)]
    show rdW m5 fp (s + 1 + j) = _
    rw [h35 j hjn]
    exact rdW_of (rd64_write_same (by rw [a12.rd]; exact hFs.rd _ (by omega)))
  have hArgs : ArgsW (reqArg q) (evalArgs σ args σ ρ) := by
    refine argsW_ptr _ (fun i hi => ?_) hA1
    by_cases hij : i = j
    · subst hij; exact .inr ⟨nt, rw, hjt⟩
    · refine .inl ?_
      rw [reqArg_mk _ fq i (by omega)]
      show rdW m1 fp (s + 1 + i) = rdW m5 fp (s + 1 + i)
      rw [h35 i hi]
      simp only [rdW, m3]
      rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega)),
        agree_rd_low a2 hroom (by omega) (by omega)]
  have hZero : ∀ i, (D.aparams a).length ≤ i → i < 6 → reqArg q i = 0 := fun i h1 h2 => by
    rw [reqArg_mk _ fq i h2]
    show rdW m5 fp (s + 1 + i) = 0
    simp only [rdW, m5]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]
    have := hz (i - (D.aparams a).length) (by omega)
    rw [show s + 1 + (D.aparams a).length + (i - (D.aparams a).length) = s + 1 + i by omega] at this
    rw [this]; rfl
  have hW5 : WeltAt m5 L σ := weltAt_stab hl (by omega) m m5 hWa (a15.mono (Nat.zero_le _))
  have hWc5 : Wc m5 := hWcs m m5 hwsm (a15.mono (Nat.zero_le _))
  have hBuf : ∀ i, i < pufW (D.count t).toNat → m5.rd64 (reqArg q j + BitVec.ofNat 64 (8 * i)) =
      some (packV (fun k => wAt m5 (L.elem t f k)) (D.count t).toNat i 8) := fun i hi => by
    rw [hpa, slot_succ, ← hc]
    rw [← hc, ← hWn] at hi
    simp only [m5]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega)),
      agree_rd_high a4 hroom (by omega) (by omega)]
    simp only [m3]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega)), hbuf i hi,
      packV_congr (ws' := fun k => wAt m5 (L.elem t f k)) (fun k hk => by rw [wAt_of (hWc5 k hk)]) 8]
  obtain ⟨w, x, m6, hk, hrd6, hwr6, hb6, hOhne, hCol, hroh⟩ := TorOK.puf (O := O) a b hb hg j nt rw t f hpp htn hbf
    hτ (σ.fragt (.inl a)) (evalArgs σ args σ ρ) q m5 rfl hArgs hZero hW5 hBuf
  have s6 := sys_step hcS hF5 (by omega) (by omega) h0 hr hk hwr6
  -- after the call: slot `s`, the world, the buffer
  let m7 := write m6 (slot fp (BitVec.ofNat 64 s)) 8 w.toNat
  rw [hpa, ← hc, ← hWn] at hb6
  have a56 : Agree fp B Ks m5 m6 := kern_agree_puf hroom (by omega) hrd6 hwr6 hb6
  have a67 : Agree fp s Ks m6 m7 := agree_write hroom (Nat.le_refl _) (by omega) _
  have a17 : Agree fp s K m m7 :=
    ((Agree.widen a15 hks).trans ((Agree.widen a56 hks).mono (by omega))).trans (Agree.widen a67 hks)
  have hF7 : FrameOK m7 fp K := hp.frame.agree a17
  have hs7 : m7.rd64 (slot fp (BitVec.ofNat 64 s)) = some w := rd64_write_same (by rw [hrd6]; exact hF5.rd s (by omega))
  have hworld7 : ∀ a : Nat, a + 8 ≤ 2 ^ 64 → fp.toNat + 8 * Ks ≤ a →
      m7.rd64 (BitVec.ofNat 64 a) = m5.rd64 (BitVec.ofNat 64 a) := fun a h1 h2 => by
    simp only [m7]
    rw [rd64_write_slot hroom (by omega) h2 h1]
    exact rd64_agree_out a56 h1 (.inr h2)
  have hbyte : ∀ k, k < c → byteOf m7 (slot fp (BitVec.ofNat 64 B)) k = byteOf m6 (slot fp (BitVec.ofNat 64 B)) k :=
    fun k hk => by
      have : k / 8 < Wn := by rw [hWn]; simp only [pufW]; omega
      simp only [byteOf, slot_succ, m7]
      rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]
  have p16 : ∀ x y : Nat, pc + BitVec.ofNat 64 x + BitVec.ofNat 64 y = pc + BitVec.ofNat 64 (x + y) :=
    fun x y => addr_norm pc x y
  have e1 : ∀ x y z : Nat, x + y = z → pc + BitVec.ofNat 64 x + BitVec.ofNat 64 y = pc + BitVec.ofNat 64 z :=
    fun x y z h => by rw [p16, h]
  have t2 : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ca.length + P.length)), fp⟩ m2 :=
    s1.trans (star_cast s2 rfl (by rw [e1 _ _ (16 * (ca.length + P.length)) (by omega)]))
  have t3 : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ca.length + P.length + 1)), fp⟩ m3 :=
    t2.trans (star_cast s3 (by rw [List.length_append]) (by
      rw [List.length_append, List.length_singleton, e1 _ _ (16 * (ca.length + P.length + 1)) (by omega)]))
  have t4 : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length))), fp⟩
      m4 := t3.trans (star_cast s4 rfl (by
        rw [e1 _ _ (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length))) (by omega)]))
  have t5 : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length) + 1)),
      fp⟩ m5 := t4.trans (star_cast s5 rfl (by
        rw [show (16 : Runner.W) = BitVec.ofNat 64 16 from rfl,
          e1 _ _ (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length) + 1)) (by omega)]))
  have s16 : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length) + 2)),
      fp⟩ m7 := t5.trans (star_cast s6
        (by rw [e1 _ _ (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length) + 1)) (by omega)]) (by
        rw [List.length_singleton, e1 _ _ (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length) + 1)) (by omega),
          e1 _ _ (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length) + 2)) (by omega)]))
  cases rw with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hU
    subst hU
    refine ⟨m7, w, by simpa using s16, agreeW_of a17, hs7, ?_, by rw [hroh]⟩
    refine weltAt_puf hl hd (by omega) hOhne (fun k hk => ?_) (fun a h1 h2 _ => hworld7 a h1 h2)
      (hW5.2.2.keep (by rw [a67.wr, hwr6]))
    have hk' : k < c := by omega
    refine ⟨ws k, by rw [hworld7 _ (by have := hcell k hk'; omega) (by have := hcell k hk'; omega)]; exact hWc5 k hk', ?_⟩
    have := hCol k hk
    simp only [Bool.false_eq_true, ↓reduceIte, wAt_of (hWc5 k hk')] at this
    exact this
  | true =>
    simp only [↓reduceIte] at hU
    have hn7 := hp.next' a17 hp.ctx (Nat.le_refl _) (by omega)
    simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil, zeroC_len] at hn7
    have hfU : CodeFar (pc + BitVec.ofNat 64 (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length) + 2)))
        U.length fp K := by
      have := hn7.far; rwa [show ca.length + P.length + 1 + (6 - (D.aparams a).length) + (1 + 1) =
        ca.length + P.length + 1 + (6 - (D.aparams a).length) + 2 by omega] at this
    have hpre7 : PreS m7 (pc + BitVec.ofNat 64 (16 * (ca.length + P.length + 1 + (6 - (D.aparams a).length) + 2)))
        fp Ks (B + Wn + 1) U ρ :=
      ⟨by have := hp.ctx; omega, by omega, frameOK_sub hF7 hks,
       by have := hn7.code; rwa [show ca.length + P.length + 1 + (6 - (D.aparams a).length) + (1 + 1) =
        ca.length + P.length + 1 + (6 - (D.aparams a).length) + 2 by omega] at this,
       codeFar_sub2 hfU hks, hn7.env, trivial, wstab_true _ _⟩
    rw [hU] at hpre7 hfU
    have hW7 : WeltWr m7 L := hW5.2.2.keep (by rw [a67.wr, hwr6])
    obtain ⟨m8, s8, a8, hc8, ho8⟩ := unpackK_ok hl hd (by omega) (by omega) hord c (by omega)
      (fun k hk => by have : k / 8 < Wn := (by rw [hWn]; simp only [pufW]; omega); omega) m7 _ hpre7 hW7
      (fun k hk => by
        obtain ⟨w', hw', _⟩ := hW5.1 t f k hk
        rw [a67.rd, hrd6]; exact rd64_some_all hw')
    rw [← hU] at s8
    refine ⟨m8, w, s16.trans s8 |> fun h => star_cast h rfl ?_, (agreeW_of a17).trans (AgreeW.widen (a8.mono (by omega)) hks), ?_, ?_, by rw [hroh]⟩
    · simp only [T.mk.injEq, and_true, p16]
      exact congrArg (fun x => pc + BitVec.ofNat 64 x) (by omega)
    · rw [agreeW_rd_low a8 (by omega) hroom (by omega) (by omega)]; exact hs7
    · refine weltAt_puf hl hd (by omega) hOhne (fun k hk => ?_)
        (fun a h1 h2 h3 => by rw [ho8 a h1 h2 (fun k hk => h3 k (by omega)), hworld7 a h1 h2])
        (hW5.2.2.keep (by rw [a8.wr, a67.wr, hwr6]))
      have hk' : k < c := by omega
      refine ⟨_, hc8 k hk', ?_⟩
      have := hCol k hk
      simp only [↓reduceIte] at this
      rw [hbyte k hk']
      rw [hpa] at this
      exact this

end Gabbro.Stage0.Senke
