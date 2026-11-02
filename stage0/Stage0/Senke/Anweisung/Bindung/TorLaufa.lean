/-
  File:      stage0/Stage0/Senke/Anweisung/TorLauf.lean
  Subject:   **The call of a gate** (`torC_ok`): the code of `torC` builds the request -- the arguments' words in the
             first argument registers, zero in the others, the number -- and the kernel answers it (`TorOK`): the
             memory then holds the oracle's world, slot `s` the kernel's word, which is the oracle's raw answer; no slot
             below `s` changed.
-/
module
public import Stage0.Senke.Anweisung.Bindung.Pruefung
public import Stage0.Senke.Anweisung.Puffer.Tor
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem torCode_len (nr s n : Nat) (ca : List II) :
    (torCode nr s n ca).length = ca.length + (6 - n) + 2 := by
  simp only [torCode, List.length_append, zeroC_len, List.length_cons, List.length_nil]

theorem torC_ok {reserved : Nat} {L : Lay D} {O : Orakel D} [TorOK L O] {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {s : Nat} {c : List II} {top : Nat} {fp pc : Runner.W} {K Ks : Nat}
    {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : torC L a args s reserved = some (c, top)) (hKs : top ≤ Ks) (hW : WIn L fp Ks K)
    (hp : PreS L m pc fp K s c ρ reserved) (hWa : WeltAt m L σ) :
    ∃ b, L.tor a = some b ∧ ∃ m' w, Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧ AgreeW L fp s K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 s)) = some w ∧
      WeltAt m' L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1 ∧
      (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).2 = rohW b (D.agruende a) w := by
  have hks := hW.ks
  simp only [torC] at h
  split at h
  · next b hb =>
    split at h
    · next hc =>
      obtain ⟨hg, _⟩ := hc
      split at h
      · next hpn =>
        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
        obtain ⟨⟨ca, ta⟩, hca, hc⟩ := h
        simp only [Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have hg' := hg
        simp only [torGut, Bool.and_eq_true, decide_eq_true_eq] at hg'
        obtain ⟨⟨hn6, _⟩, hnr⟩ := hg'
        refine ⟨b, hb, ?_⟩
        have hsmall := hp.small
        have hFs : FrameOK m fp Ks := frameOK_sub hp.frame hks
        have hroom := hFs.room
        have hroomK := hp.frame.room
        have hlo := hW.lo
        have hfar := codeFar_sub2 hp.far hks
        rw [torCode_len] at hfar
        -- the arguments
        have hp0 : PreS L m pc fp K s ((ca ++ zeroC (s + 1 + (D.aparams a).length) (6 - (D.aparams a).length)) ++
            [ci 1 s b.nr 0, ci 23 s s 0]) ρ reserved := hp
        have hq : PreS L m pc fp K (s + 1) ca ρ reserved := (hp0.up (d' := s + 1) (by omega)).left.left
        have hpw := PreS.welt hq hks hWa hW.lay (by omega)
        obtain ⟨m1, s1, a1, hA⟩ := lowR_ok σ σ (fun _ h => h) hW.lay args (s + 1) ca ta hca (by omega) (by omega) m pc ρ hpw
        have hF1 := hFs.agree a1
        have hfz : CodeFar (pc + BitVec.ofNat 64 (16 * ca.length))
            (6 - (D.aparams a).length) fp Ks :=
          codeFar_right (n := ca.length) (k := 6 - (D.aparams a).length)
            (codeFar_left (k := 2) hfar)
        -- zeros into the unused registers
        have hcz : CodeAt m1 (pc + BitVec.ofNat 64 (16 * ca.length))
            (zeroC (s + 1 + (D.aparams a).length) (6 - (D.aparams a).length)) :=
          (codeAt_right hp0.left.code).agree a1 (by rw [zeroC_len]; exact hfz)
        obtain ⟨m2, s2, a2, hz⟩ := zero_ok (K := Ks) (by omega) _ _ m1 _ hcz (by simpa only [zeroC_len] using hfz) hF1 (by omega)
        have hF2 := hF1.agree a2
        -- the number into slot `s`
        have hc34 : CodeAt m (pc + BitVec.ofNat 64 (16 * (ca.length + (6 - (D.aparams a).length))))
            ([ci 1 s b.nr 0] ++ [ci 23 s s 0]) := by
          have h1 := codeAt_right (a := ca ++ zeroC (s + 1 + (D.aparams a).length) (6 - (D.aparams a).length))
            (b := [ci 1 s b.nr 0] ++ [ci 23 s s 0]) hp0.code
          rwa [List.length_append, zeroC_len] at h1
        have hf34 : CodeFar (pc + BitVec.ofNat 64 (16 * (ca.length + (6 - (D.aparams a).length)))) 2 fp Ks :=
          codeFar_right (n := ca.length + (6 - (D.aparams a).length)) (k := 2) hfar
        have hc3 : CodeAt m2 (pc + BitVec.ofNat 64 (16 * (ca.length + (6 - (D.aparams a).length)))) [ci 1 s b.nr 0] :=
          (codeAt_left hc34).agree (a1.trans (a2.mono (by omega))) (codeFar_left (k := 1) hf34)
        have s3 := const_step (k := (b.nr : Int)) hc3 hF2 (by omega) (by omega) hnr
        let m3 := write m2 (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofInt 64 (b.nr : Int)).toNat
        have a3 : Agree fp s Ks m2 m3 := agree_write hroom (Nat.le_refl _) (by omega) _
        have hF3 := hF2.agree a3
        -- the request
        have hc4 : CodeAt m3 (pc + BitVec.ofNat 64 (16 * (ca.length + (6 - (D.aparams a).length))) + 16)
            [ci 23 s s 0] := by
          have h1 := (codeAt_right hc34).agree ((a1.mono (Nat.le_succ s)).trans ((a2.mono (by omega)).trans a3))
            (codeFar_right (n := 1) (k := 1) hf34)
          simpa using h1
        have h0 : m3.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofNat 64 b.nr) := by
          rw [← BitVec.ofInt_natCast]; exact rd64_write_same (hF2.rd s (by omega))
        let f : Nat → Runner.W := fun i => rdW m3 fp (s + 1 + i)
        let q : Runner.Req := ⟨BitVec.ofNat 64 b.nr, f 0, f 1, f 2, f 3, f 4, f 5⟩
        have hr : ∀ i, i < 6 → m3.rd64 (slot fp (BitVec.ofNat 64 (s + 1 + i))) = some (reqArg q i) := fun i hi => by
          rw [reqArg_mk _ f i hi]; exact rd64_rdW hF3 (by omega)
        have h32 : ∀ i, 0 < i → i < 7 → rdW m3 fp (s + i) = rdW m2 fp (s + i) := fun i h1 h2 => by
          simp only [rdW, m3]
          rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]
        have hArgs : ArgsW L (reqArg q) (evalArgs σ args σ ρ) := by
          refine argsW_congr _ (fun j hj => ?_) hA
          rw [reqArg_mk _ f j (by omega)]
          simp only [f, show s + 1 + j = s + (1 + j) by omega, h32 (1 + j) (by omega) (by omega)]
          simp only [rdW, agree_rd_low a2 hroom (show s + (1 + j) < s + 1 + (D.aparams a).length by omega) (by omega)]
        have hZero : ∀ i, (D.aparams a).length ≤ i → i < 6 → reqArg q i = 0 := fun i h1 h2 => by
          rw [reqArg_mk _ f i h2]
          simp only [f, show s + 1 + i = s + (1 + i) by omega, h32 (1 + i) (by omega) (by omega)]
          have := hz (i - (D.aparams a).length) (by omega)
          rw [show s + 1 + (D.aparams a).length + (i - (D.aparams a).length) = s + (1 + i) by omega] at this
          exact rdW_of this
        have hWa3 : WeltAt m3 L σ := weltAt_stab hW.lay hlo m m3 hWa
          ((a1.mono (Nat.zero_le _)).trans ((a2.mono (Nat.zero_le _)).trans (a3.mono (Nat.zero_le _))))
        obtain ⟨w, x, m4, hk, hKW, hW4, hroh⟩ :=
          TorOK.ans (O := O) a b hb hg hpn (σ.fragt (.inl a)) (evalArgs σ args σ ρ) q m3 rfl hArgs hZero hWa3
        have s4 := sys_step hc4 hF3 (by omega) (by omega) h0 hr hk hKW.2.1
        let m5 := write m4 (slot fp (BitVec.ofNat 64 s)) 8 w.toNat
        have a5 : Agree fp s Ks m4 m5 := agree_write hroom (Nat.le_refl _) (by omega) _
        refine ⟨m5, w, ?_, ?_, ?_, ?_, ?_⟩
        · have s2' := star_cast s2 rfl (by rw [pc_add])
          refine s1.trans (s2'.trans (s3.trans (star_cast s4 rfl ?_)))
          simp only [T.mk.injEq, and_true, List.length_singleton, torCode_len]
          rw [show (16 : Runner.W) = BitVec.ofNat 64 16 from rfl, addr_norm, addr_norm]; congr 2
        · exact (agreeW_of (((Agree.widen a1 hks).mono (by omega)).trans (((Agree.widen a2 hks).mono (by omega)).trans
            (Agree.widen a3 hks)))).trans ((kernW_agreeW hKW).trans (agreeW_of (Agree.widen a5 hks)))
        · exact rd64_write_same (by rw [hKW.1]; exact hF3.rd s (by omega))
        · exact weltAt_stab hW.lay hlo m4 m5 hW4 (a5.mono (Nat.zero_le _))
        · exact hroh
      · next j nt rw hpp =>
        split at h
        · next t htn =>
          split at h
          · next f hbf =>
            split at h
            · next hcond =>
              obtain ⟨hτ, _, hc0, _, hcount⟩ := hcond
              simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
              obtain ⟨⟨ca, ta⟩, hca, hc⟩ := h
              simp only [Prod.mk.injEq] at hc
              obtain ⟨rfl, rfl⟩ := hc
              refine ⟨b, hb, ?_⟩
              obtain ⟨m', w, st, ag, hw, hW', hroh⟩ := torPuf_ok (O := O) hb hg hpp htn hbf hτ hc0 hcount hca rfl rfl rfl rfl rfl
                hKs hW hp hWa
              refine ⟨m', w, star_cast st rfl ?_, ag, hw, hW', hroh⟩
              simp only [T.mk.injEq, and_true, torCode, List.length_append, List.length_singleton, List.length_cons,
                List.length_nil, zeroC_len]
            · cases h
          · cases h
        · cases h
    · cases h
  · cases h


end Gabbro.Stage0.Senke
