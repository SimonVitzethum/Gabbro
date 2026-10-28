/-
  File:      stage0/Stage0/Senke/FunktionSatz.lean
  Subject:   `ir_sim` for a function body (`lowEnd`): where G's body returns, the code checks `ensures` and either
             stops with `exit_group(102)` or goes back to the caller with the result in slot 2; where G ends in a
             logic outcome, the code stops with its code (`Ret`).

  The body runs in the callee's frame with `lo = FB + np`: it writes no slot below, so the header (return `pc`,
  caller `fp`, depth) and the parameters stay as the call left them (`Kopf`).
-/
import Stage0.Senke.AnweisungSatz

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration}

/-- What the body's code from `t` does for G's outcome of the body of `f`. -/
def Ret (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (K : Nat)
    (rp cfp : Runner.W) (t : T) (m : Runner.Mem) {l : Bool} {Γ : Ctx} : EndAusgang (vertragVon D f) l Γ → Prop
  | .zurueck σ' v =>
    if wahr? (eval σ0 (P.ensures f) (σ'.lese (vertragVon D f).ende (P.ensures f).orte) (ergEnv (D.erg f) v ρ0)) = false
    then Stops t m 102
    else ∃ m', Star t m ⟨rp, cfp⟩ m' ∧ Agree fp 2 K m m' ∧
      ∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 2)) = some w ∧ EncErg (D.erg f) v w
  | .logik e => Stops t m (logikCode e)
  | _ => False

section
variable {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W} {K : Nat}
  {rp cfp : Runner.W} {l : Bool} {Γ : Ctx}

theorem Ret.prefix {o : EndAusgang (vertragVon D f) l Γ} {t0 t : T} {m0 m : Runner.Mem}
    (h : Star t0 m0 t m) (ha : Agree fp 2 K m0 m) (hs : Ret P f σ0 ρ0 fp K rp cfp t m o) :
    Ret P f σ0 ρ0 fp K rp cfp t0 m0 o := by
  cases o with
  | zurueck σ' v =>
    simp only [Ret] at hs ⊢
    split
    · next hf => rw [if_pos hf] at hs; exact Stops.prefix h hs
    · next hf =>
      rw [if_neg hf] at hs
      obtain ⟨m', s, a, w, hw, he⟩ := hs
      exact ⟨m', h.trans s, ha.trans a, w, hw, he⟩
  | logik e => exact Stops.prefix h hs
  | why | leave | next | hardware => exact hs

theorem Ret.cast {o : EndAusgang (vertragVon D f) l Γ} {t t' : T} {m : Runner.Mem}
    (hs : Ret P f σ0 ρ0 fp K rp cfp t m o) (h : t = t') : Ret P f σ0 ρ0 fp K rp cfp t' m o := by
  subst h; exact hs

theorem Ret.schrumpf {τ : Ty} {o : EndAusgang (vertragVon D f) l (τ :: Γ)} {t : T} {m : Runner.Mem}
    (hs : Ret P f σ0 ρ0 fp K rp cfp t m o) : Ret P f σ0 ρ0 fp K rp cfp t m o.schrumpf := by
  cases o with
  | zurueck | logik | why | leave | next | hardware => exact hs

end

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
  | none, _, _, _, _, h => h.elim
  | some _, _, _, h, hw, he => envAt_cons h hw he

theorem frei_ergCtx (Γ : Ctx) : (e : Option Ty) → frei (ErgCtx Γ e) ≤ frei Γ + 1
  | none => by simp [ErgCtx]
  | some _ => by simp [ErgCtx, frei]; omega

theorem lowErg_top {Λ : List (Res D)} {Γ : Ctx} : {e : Option Ty} → (x : ErgExpr D Γ Λ e) → (d : Nat) →
    (c : List II) → (top : Nat) → lowErg x d = some (c, top) → d < top
  | _, .empty, _, _, _, h => by simp [lowErg] at h
  | _, .val e, d, c, top, h => lowE_top e d c top h

theorem lowErg_ok {Λ : List (Res D)} {fp : Runner.W} {K : Nat} (σ₀ σ : World D) {Γ : Ctx} :
    {e : Option Ty} → (x : ErgExpr D Γ Λ e) → (d : Nat) → (c : List II) → (top : Nat) →
    lowErg x d = some (c, top) → top ≤ K → ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ),
    Pre m pc fp K d c ρ → Ok m pc fp K d c (EncErg e (evalErg σ₀ x σ ρ))
  | _, .empty, _, _, _, h, _, _, _, _, _ => by simp [lowErg] at h
  | _, .val e, d, c, top, h, hK, m, pc, ρ, hp => lowE_ok σ₀ σ e d c top h hK m pc ρ hp

theorem codeFar_tail {pc fp : Runner.W} {K : Nat} {a b : List II} (h : CodeFar pc (a ++ b).length fp K) :
    CodeFar (pc + BitVec.ofNat 64 (16 * a.length)) b.length fp K :=
  codeFar_right (by rw [List.length_append] at h; exact h)

theorem slot_zero (fp : Runner.W) : slot fp (BitVec.ofNat 64 0) = fp := by simp [slot]

theorem slot_one (fp : Runner.W) : slot fp (BitVec.ofNat 64 1) = fp + 8 := by simp [slot]

theorem lowEnd_ok {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE (P.ensures f) (lo + 1) = some (cens, tens)) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → (b : Endblock D (vertragVon D f) l Γ Λ) → (c : List II) →
    (top : Nat) → lowEnd A lo (cens, tens) b = some (c, top) → top + cap ≤ K → 16 * c.length < 2 ^ 31 →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), Pre m pc fp K (frei Γ) c ρ →
    lo ≤ frei Γ → Umf A C dv m fp K → Kopf f m fp K rp cfp ρ0 →
    Ret P f σ0 ρ0 fp K rp cfp ⟨pc, fp⟩ m (execEnd O passes R b σ ρ)
  | _, Γ, Λ, .ret e _, c, top, h, hK, _, m, pc, σ, ρ, hp, hlo, _, hk => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
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
    simp only [execEnd, Ret]
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
  | _, Γ, _, .cons s rest, c, top, h, hK, hs, m, pc, σ, ρ, hp, hlo, hu, hk => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cs, ts⟩, hs1, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hFB3 : FB = 3 := rfl
    have ih := lowS_ok (O := O) (passes := passes) hS hA s cs ts hs1 (by omega) (by omega) m pc σ ρ hp.left
      (by omega) hlo hu
    simp only [execEnd]
    generalize execStmt O passes R s σ ρ = o at ih ⊢
    cases o with
    | ok σ1 ρ1 =>
      obtain ⟨m1, s1, a1, e1⟩ := ih
      have hf := codeFar_right (n := cs.length) (k := cr.length) (by simpa using hp.far)
      have hp1 : Pre m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K (frei Γ) cr ρ1 :=
        ⟨hp.ctx, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf, e1⟩
      have ih2 := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens rest cr tr hr (by omega) (by omega) m1 _ σ1 ρ1 hp1 hlo
        (hu.agree a1 hp.frame (by omega)) (hk.agree a1 hp.frame (by omega))
      exact Ret.prefix s1 (a1.mono (by omega)) ih2
    | logik e => exact ih
    | zurueck | why | leave | next | hardware => exact (ih : False).elim
  | _, Γ, Λ, .bind e rest, c, top, h, hK, hs, m, pc, σ, ρ, hp, hlo, hu, hk => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hFB3 : FB = 3 := rfl
    simp only [execEnd]
    have htop := lowE_top e _ _ _ he
    obtain ⟨m1, s1, a1, w, hw, hen⟩ :=
      lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) e _ ce te he (by omega) m pc ρ hp.left
    have hf := codeFar_right (n := ce.length) (k := cr.length) (by simpa using hp.far)
    have hp1 : Pre m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (frei Γ + 1) cr
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) :=
      ⟨by simp only [frei, List.length_cons]; omega, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf,
       envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) hw hen⟩
    have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens rest cr tr hr (by omega) (by omega) m1 _ (σ.lese Λ e.orte) _ hp1
      (by simp only [frei, List.length_cons] at hlo ⊢; omega) (hu.agree a1 hp.frame (by omega))
      (hk.agree a1 hp.frame (by omega))
    exact Ret.prefix s1 (a1.mono (by omega)) (Ret.schrumpf ih)
  | _, Γ, Λ, .bindCall g args he _ _ rest, c, top, h, hK, hs, m, pc, σ, ρ, hp, hlo, hu, hk => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, hca, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hFB3 : FB = 3 := rfl
    have hct : frei Γ + FB + (D.params g).length + 1 ≤ callTop g (frei Γ) ta := by simp only [callTop]; omega
    have hc := callC_ok hS (hA g) args (σ.lese Λ args.orte) (σ.lese Λ args.orte) hca (by omega) hp.left.left hu
    simp only [execEnd]
    generalize R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = o at hc ⊢
    cases o with
    | ok σ' v =>
      obtain ⟨m1, s1, a1, w, hw, hew⟩ := hc
      have hp1 := hp.left.next a1 (Nat.le_refl _) (by omega)
      have s2 := mov_to hp1.code hp1.frame (j := frei Γ) (s := frei Γ + 2) (by omega) (by omega) hp.small hw
      rw [← pc_add1] at s2
      let m2 := write m1 (slot fp (BitVec.ofNat 64 (frei Γ))) 8 w.toNat
      have a2 : Agree fp (frei Γ) K m1 m2 := agree_write hp1.frame.room (Nat.le_refl _) (by omega) _
      have hq := hp.next (a1.trans a2) (d' := frei Γ + 1) (by omega) (by omega)
      have hp2 : Pre m2 _ fp K (frei Γ + 1) cr (Env.cons (ergWert he v) ρ) :=
        ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
         envAt_cons hq.env (rd_same hp1.frame (by omega) w) (encErg_wert he hew)⟩
      have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens rest cr tr hr (by omega) (by omega) m2 _ σ' _ hp2
        (by simp only [frei, List.length_cons] at hlo ⊢; omega)
        (hu.agree (a1.trans a2) hp.frame (by omega)) (hk.agree (a1.trans a2) hp.frame (by omega))
      exact Ret.prefix (s1.trans s2) ((a1.trans a2).mono (by omega)) (Ret.schrumpf ih)
    | logik e => exact hc
    | why _ _ => exact hc.elim
    | hardware _ => exact hc.elim
  | _, Γ, Λ, .ite cnd t e, c, top, h, hK, hs, m, pc, σ, ρ, hp, hlo, hu, hk => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cc, tc⟩, hcc, ⟨ct, tt⟩, hct, ⟨ce, te⟩, hce, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append, List.length_singleton] at hs
    have hFB3 : FB = 3 := rfl
    have hsm := hp.small
    have htop := lowE_top cnd (frei Γ) cc tc hcc
    have hq : Pre m pc fp K (frei Γ) (cc ++ ([ci 19 (frei Γ) (16 * (ct.length + 1)) 0] ++ (ct ++ ce))) ρ := by
      simpa [List.append_assoc] using hp
    obtain ⟨m1, s1, a1, w, hw, hen⟩ := lowE_ok (fp := fp) (K := K) (σ.lese Λ cnd.orte) (σ.lese Λ cnd.orte) cnd
      (frei Γ) cc tc hcc (by omega) m pc ρ hq.left
    have h1 := hq.next a1 (Nat.le_refl _) (by omega)
    have hu1 := hu.agree a1 hp.frame (by omega)
    have hk1 := hk.agree a1 hp.frame (by omega)
    have hbrz := h1.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hbrz
    have h2 := h1.next (a := [ci 19 (frei Γ) (16 * (ct.length + 1)) 0]) (Agree.refl _ _ _ _) (Nat.le_refl _)
      (by omega)
    have hd0 : sx (II.f (frei Γ : Int)) = BitVec.ofNat 64 (frei Γ) := sx_nat (by omega)
    simp only [execEnd]
    split
    · next hb =>
      have hw1 : w = 1 := by
        simp only [Enc] at hen
        rw [hen, if_pos hb]
      have sb := star_ins (fp := fp) (m' := m1) (codeAt_left h1.code) (by simp [ci])
        (by simp only [ci]; exact run_brz_ne (t := ⟨_, fp⟩) hbrz (by rw [hd0]; exact hw) (by rw [hw1]; decide))
      have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens t ct tt hct (by omega) (by omega) m1 _ (σ.lese Λ cnd.orte) ρ h2.left hlo
        hu1 hk1
      exact Ret.prefix (s1.trans sb) (a1.mono (by omega)) ih
    · next hb =>
      have hw0 : w = 0 := by
        simp only [Enc] at hen
        rw [hen, if_neg hb]
      have hl : sx (II.f (16 * ((ct.length : Int) + 1))) = BitVec.ofNat 64 (16 * (ct.length + 1)) := by
        have := sx_nat (d := 16 * (ct.length + 1)) (by omega); simpa using this
      have sb := Star.one (run_step (t := ⟨_, fp⟩) hbrz (by decide)
        (run_brz_zero (t := ⟨_, fp⟩) hbrz (by rw [hd0, ← hw0]; exact hw)))
      rw [hl] at sb
      have h4 := h2.next (a := ct) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
      have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens e ce te hce (by omega) (by omega) m1 _ (σ.lese Λ cnd.orte) ρ h4 hlo hu1 hk1
      refine Ret.prefix (s1.trans sb) (a1.mono (by omega)) (Ret.cast ih ?_)
      simp only [T.mk.injEq, and_true, List.length_singleton, addr_norm]
      congr 2
      omega
  | _, _, _, .retWhy .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .leave .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .next .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .bindCallElse .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .bindAxiom .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .bindAxiomElse .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .regRead .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .regReadElse .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .awaits .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .bindCallInd .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .narrow .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .exchange .., _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h

end Gabbro.Stage0.Senke
