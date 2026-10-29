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
def Ret (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (K : Nat)
    (rp cfp : Runner.W) (t : T) (m : Runner.Mem) {l : Bool} {Γ : Ctx} : EndAusgang (vertragVon D f) l Γ → Prop
  | .zurueck σ' v => RetZ L P f σ0 ρ0 fp K rp cfp t m σ' v
  | .logik e => Stops t m (logikCode e)
  | _ => False

section
variable {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W} {K : Nat}
  {rp cfp : Runner.W} {l : Bool} {Γ : Ctx}

theorem Ret.prefix {o : EndAusgang (vertragVon D f) l Γ} {t0 t : T} {m0 m : Runner.Mem}
    (h : Star t0 m0 t m) (ha : Agree fp 2 K m0 m) (hs : Ret L P f σ0 ρ0 fp K rp cfp t m o) :
    Ret L P f σ0 ρ0 fp K rp cfp t0 m0 o := by
  cases o with
  | zurueck σ' v => exact RetZ.prefix h ha hs
  | logik e => exact Stops.prefix h hs
  | why | leave | next | hardware => exact hs

theorem Ret.cast {o : EndAusgang (vertragVon D f) l Γ} {t t' : T} {m : Runner.Mem}
    (hs : Ret L P f σ0 ρ0 fp K rp cfp t m o) (h : t = t') : Ret L P f σ0 ρ0 fp K rp cfp t' m o := by
  subst h; exact hs

theorem Ret.schrumpf {τ : Ty} {o : EndAusgang (vertragVon D f) l (τ :: Γ)} {t : T} {m : Runner.Mem}
    (hs : Ret L P f σ0 ρ0 fp K rp cfp t m o) : Ret L P f σ0 ρ0 fp K rp cfp t m o.schrumpf := by
  cases o with
  | zurueck | logik | why | leave | next | hardware => exact hs

end

theorem lowEnd_ok {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens)) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → (b : Endblock D (vertragVon D f) l Γ Λ) → (c : List II) →
    (top : Nat) → lowEnd A L lo (cens, tens) b = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS m pc fp K (frei Γ) c ρ →
    lo ≤ frei Γ → Umf A C dv m fp K → Kopf f m fp K rp cfp ρ0 → WeltAt m L σ →
    Ret L P f σ0 ρ0 fp K rp cfp ⟨pc, fp⟩ m (execEnd O passes R b σ ρ)
  | _, Γ, Λ, .ret e _, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, hlo, _, hk, hWa => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [execEnd, Ret]
    exact ret_ok hlo0 hens e he (by omega) m pc σ ρ hp hlo hk hW hWa
  | _, Γ, _, .cons s rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cs, ts⟩, hs1, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hFB3 : FB = 3 := rfl
    have ih := lowS_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens s cs ts hs1 (by omega) (by omega) hW m pc
      σ ρ hp.left (by omega) hlo hu hk hWa
    simp only [execEnd]
    generalize execStmt O passes R s σ ρ = o at ih ⊢
    cases o with
    | ok σ1 ρ1 =>
      obtain ⟨m1, s1, a1, e1, hw1⟩ := ih
      have hf := codeFar_right (n := cs.length) (k := cr.length) (by simpa using hp.far)
      have hp1 : PreS m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K (frei Γ) cr ρ1 :=
        ⟨hp.ctx, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf, e1, trivial, wstab_true _ _⟩
      have ih2 := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens rest cr tr hr (by omega) (by omega) hW m1 _ σ1 ρ1 hp1 hlo
        (hu.agree a1 hp.frame (by omega)) (hk.agree a1 hp.frame (by omega)) hw1
      exact Ret.prefix s1 (a1.mono (by omega)) ih2
    | zurueck σ' v => exact ih
    | logik e => exact ih
    | why | leave | next | hardware => exact (ih : False).elim
  | _, Γ, Λ, .bind e rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hFB3 : FB = 3 := rfl
    simp only [execEnd]
    have htop := lowE_top e _ _ _ he
    have hks := hW.ks
    have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, s1, a1s, w, hw, hen⟩ :=
      lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) e _ ce te he (by omega) m pc ρ hpw
    have a1 := Agree.widen a1s hks
    have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
    have hf := codeFar_right (n := ce.length) (k := cr.length) (by simpa using hp.far)
    have hp1 : PreS m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (frei Γ + 1) cr
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) :=
      ⟨by simp only [frei, List.length_cons]; omega, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf,
       envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) hw hen, trivial, wstab_true _ _⟩
    have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens rest cr tr hr (by omega) (by omega) hW m1 _ (σ.lese Λ e.orte) _ hp1
      (by simp only [frei, List.length_cons] at hlo ⊢; omega) (hu.agree a1 hp.frame (by omega))
      (hk.agree a1 hp.frame (by omega)) hWa1
    exact Ret.prefix s1 (a1.mono (by omega)) (Ret.schrumpf ih)
  | _, Γ, Λ, .bindCall g args he _ _ rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, hca, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hFB3 : FB = 3 := rfl
    have hct : frei Γ + FB + (D.params g).length + 1 ≤ callTop g (frei Γ) ta := by simp only [callTop]; omega
    have hc := callC_ok hS (hA g) args (σ.lese Λ args.orte) (σ.lese Λ args.orte) hca (by omega) hp.left.left hu hW hWa
    simp only [execEnd]
    generalize R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = o at hc ⊢
    cases o with
    | ok σ' v =>
      obtain ⟨m1, s1, a1, ⟨w, hw, hew⟩, hw1⟩ := hc
      have hks := hW.ks
      have hp1 := hp.left.next a1 (Nat.le_refl _) (by omega)
      have s2 := mov_to hp1.code hp1.frame (j := frei Γ) (s := frei Γ + 2) (by omega) (by omega) hp.small hw
      rw [← pc_add1] at s2
      let m2 := write m1 (slot fp (BitVec.ofNat 64 (frei Γ))) 8 w.toNat
      have a2s : Agree fp (frei Γ) Ks m1 m2 := agree_write (frameOK_sub hp1.frame hks).room (Nat.le_refl _) (by omega) _
      have a2 : Agree fp (frei Γ) K m1 m2 := Agree.widen a2s hks
      have hw2 : WeltAt m2 L σ' :=
        weltAt_stab hW.lay (by have := hW.lo; omega) m1 m2 hw1 (a2s.mono (Nat.zero_le _))
      have hq := hp.next (a1.trans a2) (d' := frei Γ + 1) (by omega) (by omega)
      have hp2 : PreS m2 _ fp K (frei Γ + 1) cr (Env.cons (ergWert he v) ρ) :=
        ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
         envAt_cons hq.env (rd_same hp1.frame (by omega) w) (encErg_wert he hew), trivial, wstab_true _ _⟩
      have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens rest cr tr hr (by omega) (by omega) hW m2 _ σ' _ hp2
        (by simp only [frei, List.length_cons] at hlo ⊢; omega)
        (hu.agree (a1.trans a2) hp.frame (by omega)) (hk.agree (a1.trans a2) hp.frame (by omega)) hw2
      exact Ret.prefix (s1.trans s2) ((a1.trans a2).mono (by omega)) (Ret.schrumpf ih)
    | logik e => exact hc
    | why _ _ => exact hc.elim
    | hardware _ => exact hc.elim
  | _, Γ, Λ, .ite cnd t e, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cc, tc⟩, hcc, ⟨ct, tt⟩, hct, ⟨ce, te⟩, hce, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append, List.length_singleton] at hs
    have hFB3 : FB = 3 := rfl
    have hsm := hp.small
    have htop := lowE_top cnd (frei Γ) cc tc hcc
    have hq : PreS m pc fp K (frei Γ) (cc ++ ([ci 19 (frei Γ) (16 * (ct.length + 1)) 0] ++ (ct ++ ce))) ρ := by
      simpa [List.append_assoc] using hp
    have hks := hW.ks
    have hpw := PreS.welt hq.left hks hWa hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, s1, a1s, w, hw, hen⟩ := lowE_ok (fp := fp) (K := Ks) (σ.lese Λ cnd.orte) (σ.lese Λ cnd.orte) cnd
      (frei Γ) cc tc hcc (by omega) m pc ρ hpw
    have a1 := Agree.widen a1s hks
    have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
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
      have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens t ct tt hct (by omega) (by omega) hW m1 _ (σ.lese Λ cnd.orte) ρ h2.left hlo
        hu1 hk1 hWa1
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
      have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens e ce te hce (by omega) (by omega) hW m1 _ (σ.lese Λ cnd.orte) ρ h4 hlo hu1 hk1 hWa1
      refine Ret.prefix (s1.trans sb) (a1.mono (by omega)) (Ret.cast ih ?_)
      simp only [T.mk.injEq, and_true, List.length_singleton, addr_norm]
      congr 2
      omega
  | _, _, _, .retWhy .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .leave .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .next .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .bindCallElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .bindAxiom .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .bindAxiomElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .regRead .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .regReadElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .awaits .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .bindCallInd .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .narrow .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .exchange .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h

end Gabbro.Stage0.Senke
