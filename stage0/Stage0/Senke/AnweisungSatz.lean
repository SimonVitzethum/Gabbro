/-
  File:      stage0/Stage0/Senke/AnweisungSatz.lean
  Subject:   `ir_sim` for statements and blocks: where machine G ends a block normally (`ok`), the lowered code
             runs to its end and leaves the new environment in the frame.
-/
import Stage0.Senke.Umgebung
import Stage0.Senke.Anweisung

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration} {V : Vertrag D}

/-- `mov j s`: slot `j` gets the word of slot `s`. -/
theorem mov_to {m : Runner.Mem} {pc fp : Runner.W} {K j s : Nat} {w : Runner.W}
    (hc : CodeAt m pc [ci 2 j s 0]) (hF : FrameOK m fp K) (hj : j < K) (hs : s < K) (hK : K < 2 ^ 31)
    (hv : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w) :
    Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * [ci 2 j s 0].length), fp⟩
      (write m (slot fp (BitVec.ofNat 64 j)) 8 w.toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  refine star_ins hc (by simp [ci]) ?_
  simp only [ci, op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  refine run_rd64 hv ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  exact run_wr64 (wr64_some (hF.wr j hj))

theorem star_cast {t t' u u' : T} {m m' : Runner.Mem} (h : Star t m t' m') (h1 : t = u) (h2 : t' = u') :
    Star u m u' m' := by subst h1; subst h2; exact h

theorem addr_norm (pc : Runner.W) (a b : Nat) :
    pc + BitVec.ofNat 64 a + BitVec.ofNat 64 b = pc + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem pc_add1 (pc : Runner.W) (a b : List II) :
    pc + BitVec.ofNat 64 (16 * (a ++ b).length) = pc + BitVec.ofNat 64 (16 * a.length) +
      BitVec.ofNat 64 (16 * b.length) := by
  rw [pc_add, List.length_append]

mutual
theorem lowS_ok {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {fp : Runner.W} {K : Nat} :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (s : Stmt D V l Γ Λ Λ') → (c : List II) → (top : Nat) →
    lowS s = some (c, top) → top ≤ K → 16 * c.length < 2 ^ 31 →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ σ' : World D) (ρ ρ' : Env D Γ),
    execStmt O passes R s σ ρ = .ok σ' ρ' → Pre m pc fp K Γ.length c ρ →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧ Agree fp 0 K m m' ∧ EnvAt m' fp ρ'
  | _, Γ, Λ, _, .assignVar x e, c, top, h, hK, _, m, pc, σ, σ', ρ, ρ', hx, hp => by
    simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [execStmt, Ausgang.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    have htop := lowE_top e _ _ _ he
    obtain ⟨m1, s1, a1, w, hw, hen⟩ := lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) e _ ce te he hK m pc ρ hp.left
    have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
    have hxs := vslot_lt x
    have hsm := hp.small
    have s2 := mov_to hp1.code hp1.frame (j := vslot x) (by omega) (by omega) hsm hw
    refine ⟨_, s1.trans (by rw [pc_add1]; exact s2), (a1.mono (Nat.zero_le _)).trans
      (agree_write hp1.frame.room (Nat.zero_le _) (by omega) _), ?_⟩
    have hF1 := hp1.frame
    refine envAt_set hp1.env (rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))) hen ?_
    intro τ' y hy
    have := vslot_lt y
    exact rd64_write_far (slot_far hF1.room (by omega) (by omega) (vslot_ne hy).symm)
  | _, Γ, Λ, _, .ite cnd t e, c, top, h, hK, hs, m, pc, σ, σ', ρ, ρ', hx, hp => by
    simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cc, tc⟩, hcc, ⟨ct, tt⟩, hct, ⟨ce, te⟩, hce, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append, List.length_singleton] at hs
    have hsm := hp.small
    have htop := lowE_top cnd Γ.length cc tc hcc
    let σ1 := σ.lese Λ cnd.orte
    have hq : Pre m pc fp K Γ.length (cc ++ ([ci 19 Γ.length (16 * (ct.length + 2)) 0] ++ (ct ++
        ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce)))) ρ := by simpa [List.append_assoc] using hp
    obtain ⟨m1, s1, a1, w, hw, hen⟩ := lowE_ok (fp := fp) (K := K) σ1 σ1 cnd Γ.length cc tc hcc (by omega) m pc ρ
      hq.left
    have h1 := hq.next a1 (Nat.le_refl _) (by omega)
    have hF1 := h1.frame
    have hbrz := h1.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hbrz
    have h2 := h1.next (a := [ci 19 Γ.length (16 * (ct.length + 2)) 0]) (Agree.refl _ _ _ _) (Nat.le_refl _)
      (by omega)
    have hd0 : sx (II.f (Γ.length : Int)) = BitVec.ofNat 64 Γ.length := sx_nat (by omega)
    simp only [execStmt] at hx
    split at hx
    · next hb =>
      -- the condition holds: brz falls through, the `then` block, jmp to the end
      have hw1 : w = 1 := by
        simp only [Enc] at hen
        rw [hen, if_pos hb]
      have sb := star_ins (fp := fp) (m' := m1) (codeAt_left h1.code) (by simp [ci])
        (by simp only [ci]; exact run_brz_ne (t := ⟨_, fp⟩) hbrz (by rw [hd0]; exact hw) (by rw [hw1]; decide))
      obtain ⟨m2, s2, a2, e2⟩ := lowB_ok t ct tt hct (by omega) (by omega) m1 _ σ1 σ' ρ ρ' hx h2.left
      have hf3 := codeFar_right (n := ct.length) (k := ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length)
        (by simpa using h2.far)
      have hc3 := (codeAt_right h2.code).agree a2 hf3
      have hjmp := hc3 0 (by simp)
      simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hjmp
      have sj := Star.one (run_step (t := ⟨_, fp⟩) hjmp (by decide) (run_jmp (t := ⟨_, fp⟩) hjmp))
      have hl : sx (II.f (16 * ((ce.length : Int) + 1))) = BitVec.ofNat 64 (16 * (ce.length + 1)) := by
        have := sx_nat (d := 16 * (ce.length + 1)) (by omega); simpa using this
      rw [hl] at sj
      refine ⟨m2, ((s1.trans sb).trans s2).trans (star_cast sj rfl ?_), ((a1.mono (Nat.zero_le _)).trans a2), e2⟩
      simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, List.length_cons,
        List.length_nil, addr_norm]
      congr 2
      omega
    · next hb =>
      -- the condition fails: brz jumps to the `else` block
      have hw0 : w = 0 := by
        simp only [Enc] at hen
        rw [hen, if_neg hb]
      have hl : sx (II.f (16 * ((ct.length : Int) + 2))) = BitVec.ofNat 64 (16 * (ct.length + 2)) := by
        have := sx_nat (d := 16 * (ct.length + 2)) (by omega); simpa using this
      have sb := Star.one (run_step (t := ⟨_, fp⟩) hbrz (by decide)
        (run_brz_zero (t := ⟨_, fp⟩) hbrz (by rw [hd0, ← hw0]; exact hw)))
      rw [hl] at sb
      have h4 := ((h2.next (a := ct) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)).next
        (a := [ci 18 (16 * (ce.length + 1)) 0 0]) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega))
      obtain ⟨m2, s2, a2, e2⟩ := lowB_ok e ce te hce (by omega) (by omega) m1 _ σ1 σ' ρ ρ' hx h4
      refine ⟨m2, (s1.trans sb).trans (star_cast s2 ?_ ?_), ((a1.mono (Nat.zero_le _)).trans a2), e2⟩
      · simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, List.length_cons,
          List.length_nil, addr_norm]
        congr 2
        omega
      · simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, List.length_cons,
          List.length_nil, addr_norm]
        congr 2
        omega
  | _, _, _, _, .assignSlot .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .assignThru .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .assignGlob .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .putBytes .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .shift .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .onOption .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .onTag .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .onWhy .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .call .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .callInd .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .locks .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .breaking .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .traverse .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .retry .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .forever .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .axiomCall .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .regWrite .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .transition .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .publish .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .advances .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .retires .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .ret .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .retWhy .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .leave .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .next .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .assignSlotRef .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h

theorem lowB_ok {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {fp : Runner.W} {K : Nat} :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (b : Block D V l Γ Λ Λ') → (c : List II) → (top : Nat) →
    lowB b = some (c, top) → top ≤ K → 16 * c.length < 2 ^ 31 →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ σ' : World D) (ρ ρ' : Env D Γ),
    execBlock O passes R b σ ρ = .ok σ' ρ' → Pre m pc fp K Γ.length c ρ →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧ Agree fp 0 K m m' ∧ EnvAt m' fp ρ'
  | _, Γ, _, _, .nil, c, top, h, _, _, m, pc, σ, σ', ρ, ρ', hx, hp => by
    simp only [lowB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execBlock, Ausgang.ok.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, hp.env⟩
  | _, Γ, _, _, .cons s rest, c, top, h, hK, hs, m, pc, σ, σ', ρ, ρ', hx, hp => by
    simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cs, ts⟩, hs1, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    simp only [execBlock] at hx
    cases hst : execStmt O passes R s σ ρ with
    | ok σ1 ρ1 =>
      rw [hst] at hx
      obtain ⟨m1, s1, a1, e1⟩ := lowS_ok s cs ts hs1 (by omega) (by omega) m pc σ σ1 ρ ρ1 hst hp.left
      have hf := codeFar_right (n := cs.length) (k := cr.length) (by simpa using hp.far)
      have hp1 : Pre m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K Γ.length cr ρ1 :=
        ⟨hp.ctx, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf, e1⟩
      obtain ⟨m2, s2, a2, e2⟩ := lowB_ok rest cr tr hr (by omega) (by omega) m1 _ σ1 σ' ρ1 ρ' hx hp1
      exact ⟨m2, s1.trans (by rw [pc_add1]; exact s2), a1.trans a2, e2⟩
    | zurueck | why | leave | next | logik | hardware => rw [hst] at hx; cases hx
  | _, Γ, Λ, _, .bind e rest, c, top, h, hK, hs, m, pc, σ, σ', ρ, ρ', hx, hp => by
    simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    simp only [execBlock] at hx
    cases hb : execBlock O passes R rest (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) with
    | ok σ2 ρ2 =>
      rw [hb] at hx
      simp only [Ausgang.schrumpf, Ausgang.ok.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      have htop := lowE_top e _ _ _ he
      obtain ⟨m1, s1, a1, w, hw, hen⟩ :=
        lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) e _ ce te he (by omega) m pc ρ hp.left
      have hf := codeFar_right (n := ce.length) (k := cr.length) (by simpa using hp.far)
      have hp1 : Pre m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (Γ.length + 1) cr
          (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) :=
        ⟨by simp, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf,
         envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) hw hen⟩
      obtain ⟨m2, s2, a2, e2⟩ := lowB_ok rest cr tr hr (by omega) (by omega) m1 _ _ σ2 _ ρ2 hb hp1
      exact ⟨m2, s1.trans (by rw [pc_add1]; exact s2), (a1.mono (Nat.zero_le _)).trans a2, envAt_tail e2⟩
    | zurueck | why | leave | next | logik | hardware =>
      rw [hb] at hx; simp [Ausgang.schrumpf] at hx
  | _, _, _, _, .bindCall .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .bindCallInd .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .bindCallElse .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .bindAxiom .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .bindAxiomElse .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .regRead .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .regReadElse .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .awaits .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .exchange .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .narrow .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .check .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .float .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatLit .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatOf .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatNarrow .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
end

end Gabbro.Stage0.Senke
