/-
  File:      stage0/Stage0/Senke/Anweisung/TorLauf.lean
  Subject:   **The call of a gate** (`torC_ok`): the code of `torC` builds the request -- the arguments' words in the
             first argument registers, zero in the others, the number -- and the kernel answers it (`TorOK`): the
             memory then holds the oracle's world, slot `s` the kernel's word, which is the oracle's raw answer; no slot
             below `s` changed.
-/
module
public import Stage0.Senke.Anweisung.Bindung.TorLaufa
public import Stage0.Senke.Anweisung.Bindung.Pruefung
public import Stage0.Senke.Anweisung.Puffer.Tor
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-- The call of a gate without a reason channel: the raw answer is the kernel's word read signed. -/
theorem torC0_ok {reserved : Nat} {L : Lay D} {O : Orakel D} [TorOK L O] {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {s : Nat} {c : List II} {top : Nat} {fp pc : Runner.W} {K Ks : Nat}
    {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : torC0 L a args s reserved = some (c, top)) (hKs : top ≤ Ks) (hW : WIn L fp Ks K)
    (hp : PreS L m pc fp K s c ρ reserved) (hWa : WeltAt m L σ) :
    ∃ m' w, Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧ AgreeW L fp s K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 s)) = some w ∧
      WeltAt m' L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1 ∧
      (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).2 = w.toInt := by
  simp only [torC0] at h
  split at h
  · next h0 =>
    obtain ⟨b, _, m', w, s1, a1, hw, hW', hroh⟩ := torC_ok (O := O) h hKs hW hp hWa
    exact ⟨m', w, s1, a1, hw, hW', by rw [hroh]; simp only [rohW, h0, ↓reduceIte]⟩
  · cases h

theorem torC_top1 {L : Lay D} {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {s : Nat}
    {reserved : Nat} {c : List II} {t : Nat} (h : torC L a args s reserved = some (c, t)) : s + 7 ≤ t := by
  simp only [torC] at h
  split at h
  · split at h
    · split at h
      · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, _, _, rfl⟩ := h
        omega
      · split at h
        · split at h
          · split at h
            · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, _, _, rfl⟩ := h
              omega
            · cases h
          · cases h
        · cases h
    · cases h
  · cases h

theorem torC_top {L : Lay D} {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {s : Nat}
    {reserved : Nat} {c : List II} {t : Nat} (h : torC0 L a args s reserved = some (c, t)) : s + 7 ≤ t := by
  simp only [torC0] at h
  split at h
  · exact torC_top1 h
  · cases h

/-! ## G's side: the raw answer decoded -/

theorem axiomAntwort_eq (O : Orakel D) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    axiomAntwort O a σ ρ = ((O.wirkt a (σ.fragt (.inl a)) ρ).1,
      einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ.fragt (.inl a)) ρ).2) := by rfl

/-- A gate without an answer: every raw word decodes. -/
theorem einpassenErg_none {z : Int → Option D.Fn} {e : Option Ty} (he : e = none) (r : Int) :
    ∃ u, einpassenErg z e r = some u := by
  subst he; exact ⟨(), rfl⟩

/-- An integer answer: inside its range the kernel's word is the value's word; outside, no answer. -/
theorem einpassen_int {z : Int → Option D.Fn} {e : Option Ty} {τ : Ty} (he : e = some τ) {lo hi : Int}
    (hτ : τ = .int lo hi) (w : Runner.W) :
    (lo ≤ w.toInt ∧ w.toInt ≤ hi → ∃ v, einpassenErg z e w.toInt = some v ∧ Enc L τ (ergWert he v) w) ∧
    (¬ (lo ≤ w.toInt ∧ w.toInt ≤ hi) → einpassenErg z e w.toInt = none) := by
  subst he hτ
  refine ⟨fun h => ⟨⟨w.toInt, h.1, h.2⟩, ?_, ?_⟩, fun h => ?_⟩
  · simp [einpassenErg, einpassen, h]; try rfl
  · show w = BitVec.ofInt 64 w.toInt
    exact (BitVec.ofInt_toInt).symm
  · simp [einpassenErg, einpassen, h]; try rfl

/-- No raw integer answers a never gate. -/
theorem einpassen_never {z : Int → Option D.Fn} {e : Option Ty}
    (he : e = some .never) (n : Int) : einpassenErg z e n = none := by
  subst he
  rfl

/-- Boolean answers always fit, with zero false and every other raw integer true. -/
theorem einpassen_bool {z : Int → Option D.Fn} {e : Option Ty}
    (he : e = some .bool) (n : Int) :
    ∃ v, einpassenErg z e n = some v ∧ ergWert he v = decide (n ≠ 0) := by
  subst he
  exact ⟨decide (n ≠ 0), rfl, rfl⟩

/-- **A gate bound in a block** (`bindAxiom`): the call, then the test of its answer. Inside the range the value is in
    slot `frei Γ` and the oracle's world in memory; outside it, G has no answer and the code stops with 110. -/
theorem torBind_ok {reserved : Nat} {L : Lay D} {O : Orakel D} [TorOK L O] {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {τ : Ty} (he : D.aerg a = some τ) {ct ck cr : List II} {tt : Nat}
    {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (ht : torC0 L a args (frei Γ reserved) reserved = some (ct, tt)) (hck : chkC (D.aerg a) (frei Γ reserved) = some ck)
    (htt : tt ≤ Ks) (htk : frei Γ reserved + 10 ≤ Ks) (hW : WIn L fp Ks K) (hp : PreS L m pc fp K (frei Γ reserved) (ct ++ ck ++ cr) ρ reserved)
    (hWa : WeltAt m L σ) :
    (∃ v m2, axiomAntwort O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some v) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ct ++ ck).length), fp⟩ m2 ∧ AgreeW L fp (frei Γ reserved) K m m2 ∧
      ValueAt L m2 fp (frei Γ reserved) τ (ergWert he v) ∧
      WeltAt m2 L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) ∨
    (axiomAntwort O a σ (evalArgs σ args σ ρ) = ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, none) ∧
      Stops ⟨pc, fp⟩ m 110) := by
  have hks := hW.ks
  have h7 := torC_top ht
  have hck' := hck
  rw [he] at hck'
  have width := chkC_width hck'
  cases τ with
  | int lo hi =>
    have hp' : PreS L m pc fp K (frei Γ reserved) (ct ++ (ck ++ cr)) ρ reserved := (List.append_assoc ct ck cr) ▸ hp
    obtain ⟨m1, w, s1, a1, hw1, hW1, hroh⟩ := torC0_ok (O := O) ht htt hW hp'.left hWa
    have hn := hp'.nextW hW a1 (by have := hp.ctx; omega) (Nat.le_refl _) (by omega)
    have hpk : PreS L m1 (pc + BitVec.ofNat 64 (16 * ct.length)) fp Ks (frei Γ reserved + 1) ck ρ reserved :=
      ⟨by have := hp.ctx; omega, by have := hp.small; omega, frameOK_sub hn.frame hks, hn.left.code,
        codeFar_sub2 hn.left.far hks, hn.env, trivial, wstab_true _ _⟩
    obtain ⟨hin, hout⟩ := chkC_ok hck' hpk htk hw1
    obtain ⟨g1, g2⟩ := einpassen_int (z := O.zeiger) he rfl w
    rw [axiomAntwort_eq, hroh]
    by_cases hr : lo ≤ w.toInt ∧ w.toInt ≤ hi
    · obtain ⟨v, hv, hen⟩ := g1 hr
      obtain ⟨m2, s2, a2⟩ := hin hr
      have hroom := (frameOK_sub hp.frame hks).room
      refine .inl ⟨v, m2, by rw [hv], ?_, a1.trans (agreeW_of (Agree.widen (a2.mono (Nat.le_succ _)) hks)), ?_, ?_⟩
      · exact s1.trans (by rw [List.length_append, ← pc_add]; exact s2)
      · refine ValueAt.of_enc width ?_ hen
        rw [agree_rd_low a2 hroom (by omega) (by omega)]; exact hw1
      · exact weltAt_stab hW.lay (by have := hW.lo; omega) m1 m2 hW1 (a2.mono (Nat.zero_le _))
    · exact .inr ⟨by rw [g2 hr], Stops.prefix s1 (hout hr)⟩
  | bool =>
    have hp' : PreS L m pc fp K (frei Γ reserved) (ct ++ (ck ++ cr)) ρ reserved := (List.append_assoc ct ck cr) ▸ hp
    obtain ⟨m1, w, s1, a1, hw1, hW1, hroh⟩ := torC0_ok (O := O) ht htt hW hp'.left hWa
    have hn := hp'.nextW hW a1 (by have := hp.ctx; omega) (Nat.le_refl _) (by omega)
    simp only [chkC, Option.some.injEq] at hck'
    subst ck
    have hpk : PreS L m1 _ fp Ks (frei Γ reserved) ([ci 1 (frei Γ reserved + 1) 0 0, ci 14 (frei Γ reserved) (frei Γ reserved) (frei Γ reserved + 1)] ++ [ci 1 (frei Γ reserved + 1) 0 0, ci 14 (frei Γ reserved) (frei Γ reserved) (frei Γ reserved + 1)]) ρ reserved :=
      ⟨hp.ctx, by have := hp.small; omega, frameOK_sub hn.frame hks, hn.left.code,
       codeFar_sub2 hn.left.far hks, hn.env, trivial, wstab_true _ _⟩
    obtain ⟨m2, s2, a2, w2, hw2, he2⟩ := boolC_ok hpk (by omega) hw1
    obtain ⟨v, hv, hev⟩ := einpassen_bool (z := O.zeiger) he w.toInt
    refine .inl ⟨v, m2, ?_, ?_, a1.trans (agreeW_of (Agree.widen a2 hks)), ?_, ?_⟩
    · rw [axiomAntwort_eq, hroh, hv]
    · exact s1.trans (by rw [List.length_append, ← pc_add]; exact s2)
    · apply ValueAt.of_enc width hw2
      simpa only [hev] using he2
    · exact weltAt_stab hW.lay (by have := hW.lo; omega) m1 m2 hW1 (a2.mono (Nat.zero_le _))
  | never =>
    have hp' : PreS L m pc fp K (frei Γ reserved) (ct ++ (ck ++ cr)) ρ reserved := (List.append_assoc ct ck cr) ▸ hp
    obtain ⟨m1, w, s1, a1, hw1, hW1, hroh⟩ := torC0_ok (O := O) ht htt hW hp'.left hWa
    have hn := hp'.nextW hW a1 (by have := hp.ctx; omega) (Nat.le_refl _) (by omega)
    simp only [chkC, Option.some.injEq] at hck'
    subst ck
    refine .inr ⟨by rw [axiomAntwort_eq, einpassen_never he], Stops.prefix s1 ?_⟩
    exact stop_ok hn.left.code hn.left.far hn.frame (by omega) hp.small (by decide)
  | _ => simp [chkC] at hck'

end Gabbro.Stage0.Senke
