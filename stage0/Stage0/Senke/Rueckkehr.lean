/-
  File:      stage0/Stage0/Senke/Rueckkehr.lean
  Subject:   `ret`: the result into slot `lo`, `ensures` over it and the parameters, then back to the caller with the
             result in slot 2 or `exit_group(102)` (`RetZ`, `ret_ok`); the callee's header and parameters (`Kopf`).
-/
import Stage0.Senke.Aufruf

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration}

/-- What the code from `t` does when G returns `v` in the world `σ'` from the body of `f`: `ensures` fails, the
    stop 102; else back to the caller with the result in slot 2, nothing below changed. -/
def RetZ (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (K : Nat)
    (rp cfp : Runner.W) (t : T) (m : Runner.Mem) (σ' : World D) (v : ErgVal D (D.erg f)) : Prop :=
  if wahr? (eval σ0 (P.ensures f) (σ'.lese (vertragVon D f).ende (P.ensures f).orte) (ergEnv (D.erg f) v ρ0)) = false
  then Stops t m 102
  else ∃ m', Star t m ⟨rp, cfp⟩ m' ∧ Agree fp 2 K m m' ∧
    ∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 2)) = some w ∧ EncErg (D.erg f) v w

theorem RetZ.prefix {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W} {K : Nat}
    {rp cfp : Runner.W} {t0 t : T} {m0 m : Runner.Mem} {σ' : World D} {v : ErgVal D (D.erg f)}
    (h : Star t0 m0 t m) (ha : Agree fp 2 K m0 m) (hs : RetZ P f σ0 ρ0 fp K rp cfp t m σ' v) :
    RetZ P f σ0 ρ0 fp K rp cfp t0 m0 σ' v := by
  simp only [RetZ] at hs ⊢
  split
  · next hf => rw [if_pos hf] at hs; exact Stops.prefix h hs
  · next hf =>
    rw [if_neg hf] at hs
    obtain ⟨m', s, a, w, hw, he⟩ := hs
    exact ⟨m', h.trans s, ha.trans a, w, hw, he⟩

/-- The callee's header and parameters, below `lo`. -/
structure Kopf (f : D.Fn) (m : Runner.Mem) (fp : Runner.W) (K : Nat) (rp cfp : Runner.W)
    (ρ0 : Env D (D.params f)) : Prop where
  r0 : m.rd64 (slot fp (BitVec.ofNat 64 0)) = some rp
  r1 : m.rd64 (slot fp (BitVec.ofNat 64 1)) = some cfp
  env : EnvAt m fp ρ0
  big : FB + (D.params f).length ≤ K

theorem Kopf.agree {f : D.Fn} {m m' : Runner.Mem} {fp : Runner.W} {K lo : Nat} {rp cfp : Runner.W}
    {ρ0 : Env D (D.params f)} (h : Kopf f m fp K rp cfp ρ0) (ha : Agree fp lo K m m') (hF : FrameOK m fp K)
    (hl : FB + (D.params f).length ≤ lo) : Kopf f m' fp K rp cfp ρ0 := by
  have hb := h.big
  have hFB3 : FB = 3 := rfl
  have ha' := ha.mono hl
  refine ⟨?_, ?_, envAt_agree h.env ha' hF (Nat.le_refl _) hb, hb⟩
  · rw [agree_rd_low ha' hF.room (by omega) hb]; exact h.r0
  · rw [agree_rd_low ha' hF.room (by omega) hb]; exact h.r1

theorem envAt_ergEnv {m : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} :
    {e : Option Ty} → {v : ErgVal D e} → {w : Runner.W} → EnvAt m fp ρ →
    m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some w → EncErg e v w → EnvAt m fp (ergEnv e v ρ)
  | none, _, _, h, _, _ => h
  | some _, _, _, h, hw, he => envAt_cons h hw he

theorem frei_ergCtx (Γ : Ctx) : (e : Option Ty) → frei (ErgCtx Γ e) ≤ frei Γ + 1
  | none => by simp [ErgCtx]
  | some _ => by simp [ErgCtx, frei]; omega

theorem lowErg_top {Λ : List (Res D)} {Γ : Ctx} : {e : Option Ty} → (x : ErgExpr D Γ Λ e) → (d : Nat) →
    (c : List II) → (top : Nat) → lowErg x d = some (c, top) → d < top
  | _, .empty, d, c, top, h => by simp only [lowErg, Option.some.injEq, Prod.mk.injEq] at h; omega
  | _, .val e, d, c, top, h => lowE_top e d c top h

theorem lowErg_ok {Λ : List (Res D)} {fp : Runner.W} {K : Nat} (σ₀ σ : World D) {Γ : Ctx} :
    {e : Option Ty} → (x : ErgExpr D Γ Λ e) → (d : Nat) → (c : List II) → (top : Nat) →
    lowErg x d = some (c, top) → top ≤ K → ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ),
    Pre m pc fp K d c ρ → Ok m pc fp K d c (EncErg e (evalErg σ₀ x σ ρ))
  | _, .empty, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowErg, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, ?_⟩
    exact ⟨_, by simp only [Runner.Mem.rd64, hp.frame.rd d (by omega), ↓reduceIte]; rfl, trivial⟩
  | _, .val e, d, c, top, h, hK, m, pc, ρ, hp => lowE_ok σ₀ σ e d c top h hK m pc ρ hp

theorem codeFar_tail {pc fp : Runner.W} {K : Nat} {a b : List II} (h : CodeFar pc (a ++ b).length fp K) :
    CodeFar (pc + BitVec.ofNat 64 (16 * a.length)) b.length fp K :=
  codeFar_right (by rw [List.length_append] at h; exact h)

theorem slot_zero (fp : Runner.W) : slot fp (BitVec.ofNat 64 0) = fp := by simp [slot]

theorem slot_one (fp : Runner.W) : slot fp (BitVec.ofNat 64 1) = fp + 8 := by simp [slot]

/-- `ret e`: the result, `ensures`, back or the stop (`retC`). -/
theorem ret_ok {P : Programm D} {f : D.Fn} {fp : Runner.W} {K lo : Nat} {rp cfp : Runner.W} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE (P.ensures f) (lo + 1) = some (cens, tens))
    {Γ : Ctx} {Λ : List (Res D)} (e : ErgExpr D Γ Λ (vertragVon D f).erg) {ce : List II} {te : Nat}
    (he : lowErg e (frei Γ) = some (ce, te)) (hK : max te (max tens (retTop lo)) ≤ K)
    (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ)
    (hp : Pre m pc fp K (frei Γ) (ce ++ retC lo (frei Γ) cens) ρ) (hlo : lo ≤ frei Γ)
    (hk : Kopf f m fp K rp cfp ρ0) :
    RetZ P f σ0 ρ0 fp K rp cfp ⟨pc, fp⟩ m (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
    have hFB3 : FB = 3 := rfl
    have htop := lowErg_top e _ _ _ he
    have hsm := hp.small
    have hroom := hp.frame.room
    simp only [retTop] at hK
    -- the result into slot `frei Γ`, then into slot `lo`
    obtain ⟨m1, s1, a1, w, hw, hen⟩ := lowErg_ok (fp := fp) (K := K) (σ.lese Λ e.orte) (σ.lese Λ e.orte) e _ ce te
      he (by omega) m pc ρ hp.left
    have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
    have hq : Pre m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (frei Γ)
        ([ci 2 lo (frei Γ) 0] ++ (cens ++ ([ci 19 ((lo + 1 : Nat) : Int) 48 0] ++
          ([ci 2 2 lo 0] ++ ([ci 21 0 0 0] ++ stopC 102 (lo + 1)))))) ρ := by
      simpa [retC, List.append_assoc] using hp1
    have hF1 := hq.frame
    have s2 := mov_to (codeAt_left hq.code) hF1 (j := lo) (s := frei Γ) (by omega) (by omega) hsm hw
    let m2 := write m1 (slot fp (BitVec.ofNat 64 lo)) 8 w.toNat
    have a2 : Agree fp lo K m1 m2 := agree_write hroom (Nat.le_refl _) (by omega) _
    have hF2 := hF1.agree a2
    have hf2 := codeFar_tail (a := [ci 2 lo (frei Γ) 0]) hq.far
    have hc2 := (codeAt_right hq.code).agree a2 hf2
    have hk2 := hk.agree ((a1.mono hlo).trans a2) hp.frame (by omega)
    -- `ensures` over the result and the parameters, into slot `lo + 1`
    have hpe : Pre m2 _ fp K (lo + 1) cens (ergEnv (D.erg f) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ0) :=
      ⟨Nat.le_trans (frei_ergCtx _ _) (by simp only [frei]; omega), hsm, hF2, codeAt_left hc2,
       codeFar_left (by rw [← List.length_append]; exact hf2),
       envAt_ergEnv hk2.env (by
         show m2.rd64 (slot fp (BitVec.ofNat 64 (FB + (D.params f).length))) = some w
         rw [← hlo0]; exact rd_same hF1 (by omega) w) hen⟩
    obtain ⟨m3, s3, a3, b, hb, hbe⟩ := lowE_ok (fp := fp) (K := K) σ0
      ((σ.lese Λ e.orte).lese (vertragVon D f).ende (P.ensures f).orte) (P.ensures f) (lo + 1) cens tens hens
      (by omega) m2 _ _ hpe
    have hF3 := hF2.agree a3
    have hf3 := codeFar_tail (a := cens) hf2
    have hc3 := (codeAt_right hc2).agree a3 hf3
    have hbrz := hc3 0 (by simp)
    simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hbrz
    have hd1 : sx (II.f ((lo + 1 : Nat) : Int)) = BitVec.ofNat 64 (lo + 1) := sx_nat (by omega)
    simp only [Enc] at hbe
    simp only [RetZ]
    split
    · next hfalse =>
      -- `ensures` fails: brz to the stop
      have hb0 : b = 0 := by
        split at hbe
        · next ht => exact (Bool.false_ne_true (hfalse.symm.trans ht)).elim
        · exact hbe
      have hl : sx (II.f 48) = BitVec.ofNat 64 48 := sx_nat (d := 48) (by omega)
      have sb := Star.one (run_step (t := ⟨_, fp⟩) hbrz (by decide)
        (run_brz_zero (t := ⟨_, fp⟩) hbrz (by rw [hd1, ← hb0]; exact hb)))
      rw [hl] at sb
      have hcS : CodeAt m3 (_ + BitVec.ofNat 64 48) (stopC 102 (lo + 1)) :=
        codeAt_right (a := [ci 19 ((lo + 1 : Nat) : Int) 48 0, ci 2 2 lo 0, ci 21 0 0 0]) hc3
      have hfS : CodeFar (_ + BitVec.ofNat 64 48) 3 fp K :=
        codeFar_tail (a := [ci 19 ((lo + 1 : Nat) : Int) 48 0, ci 2 2 lo 0, ci 21 0 0 0]) hf3
      exact Stops.prefix (s1.trans (s2.trans (s3.trans sb))) (stop_ok hcS hfS hF3 (by omega) hsm (by decide))
    · next htrue =>
      -- `ensures` holds: the result into slot 2, `ret`
      have hb1 : b = 1 := by
        split at hbe
        · exact hbe
        · next hn => simp only [Bool.not_eq_true] at hn; exact absurd hn htrue
      have rb := run_brz_ne (t := ⟨_, fp⟩) hbrz (by rw [hd1]; exact hb) (by rw [hb1]; decide)
      have sb := star_ins (fp := fp) (m' := m3) (codeAt_left (a := [ci 19 ((lo + 1 : Nat) : Int) 48 0]) hc3)
        (by simp [ci]) (by simp only [ci]; exact rb)
      have hc4 := codeAt_right (a := [ci 19 ((lo + 1 : Nat) : Int) 48 0]) hc3
      have hw3 : m3.rd64 (slot fp (BitVec.ofNat 64 lo)) = some w := by
        rw [agree_rd_low a3 hF2.room (by omega) (by omega)]; exact rd_same hF1 (by omega) w
      have s5 := mov_to (codeAt_left (a := [ci 2 2 lo 0]) hc4) hF3 (j := 2) (s := lo) (by omega) (by omega) hsm hw3
      let m4 := write m3 (slot fp (BitVec.ofNat 64 2)) 8 w.toNat
      have a4 : Agree fp 2 K m3 m4 := agree_write hF3.room (Nat.le_refl _) (by omega) _
      have hf4 := codeFar_tail (a := [ci 2 2 lo 0]) (codeFar_tail (a := [ci 19 ((lo + 1 : Nat) : Int) 48 0]) hf3)
      have hc5 := (codeAt_right (a := [ci 2 2 lo 0]) hc4).agree a4 hf4
      have hret := hc5 0 (by simp)
      simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hret
      have hk3 := hk2.agree a3 hF2 (by omega)
      have h0 : m4.rd64 fp = some rp := by
        rw [← slot_zero fp, rd_other hF3.room (by omega) (by omega) (by omega)]; exact hk3.r0
      have h1 : m4.rd64 (fp + 8) = some cfp := by
        rw [← slot_one fp, rd_other hF3.room (by omega) (by omega) (by omega)]; exact hk3.r1
      have sr := Star.one (run_step (t := ⟨_, fp⟩) hret (by decide) (run_ret (t := ⟨_, fp⟩) h0 h1))
      refine ⟨m4, s1.trans (s2.trans (s3.trans (sb.trans (s5.trans sr)))),
        (a1.mono (by omega)).trans ((a2.mono (by omega)).trans ((a3.mono (by omega)).trans a4)), w,
        rd_same hF3 (by omega) w, hen⟩

end Gabbro.Stage0.Senke
