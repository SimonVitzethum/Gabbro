/-
  File:      stage0/Stage0/Senke/FunktionSatz.lean
  Subject:   `ir_sim` for a function body (`lowEnd`): where G's body returns, the code checks `ensures` and either
             stops with `exit_group(102)` or goes back to the caller with the result in slot 2; where G ends in a
             logic outcome, the code stops with its code (`Ret`).

  The body runs in the callee's frame with `lo = FB + np`: it writes no slot below, so the header (return `pc`,
  caller `fp`, depth) and the parameters stay as the call left them (`Kopf`).
-/
import Stage0.Senke.Anweisung.Satz
import Stage0.Senke.Anweisung.Atomar
import Stage0.Senke.Anweisung.FehlerLauf

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-- What the body's code from `t` does for G's outcome of an end block: `zurueck` returns (`RetZ`), `logik` stops
    with its code, `leave` and `next` reach the loop's targets `eL` and `eN`. -/
def Ret (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (lo K : Nat)
    (pr : List Nat) (rp cfp : Runner.W) (t : T) (m : Runner.Mem) (eL eN : Runner.W) {l : Bool} {Γ : Ctx} :
    EndAusgang (vertragVon D f) l Γ → Prop
  | .zurueck σ' v => RetZ L P f σ0 ρ0 fp K rp cfp t m σ' v
  | .logik e => Stops t m (logikCode e)
  | .hardware h => Stops t m (hwCode h)
  | .leave _ σ' ρ' => Reach L fp lo K pr t m eL σ' ρ'
  | .next _ σ' ρ' => Reach L fp lo K pr t m eN σ' ρ'
  | _ => False

section
variable {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W} {lo K : Nat}
  {pr : List Nat} {rp cfp : Runner.W} {l : Bool} {Γ : Ctx}

theorem Ret.prefix {o : EndAusgang (vertragVon D f) l Γ} {t0 t : T} {m0 m : Runner.Mem} {eL eN : Runner.W}
    (hl : 2 ≤ lo) (h : Star t0 m0 t m) (ha : AgreeW L fp lo K m0 m) (hk : Keeps fp pr m0 m) (hs : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o) :
    Ret L P f σ0 ρ0 fp lo K pr rp cfp t0 m0 eL eN o := by
  cases o with
  | zurueck σ' v => exact RetZ.prefix h (ha.mono hl) hs
  | logik e => exact Stops.prefix h hs
  | hardware e => exact Stops.prefix h hs
  | leave _ σ' ρ' => exact Reach.prefix h ha hk hs
  | next _ σ' ρ' => exact Reach.prefix h ha hk hs
  | why => exact hs

theorem Ret.cast {o : EndAusgang (vertragVon D f) l Γ} {t t' : T} {m : Runner.Mem} {eL eN eL' eN' : Runner.W}
    (hs : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o) (h : t = t') (h3 : eL = eL') (h4 : eN = eN') :
    Ret L P f σ0 ρ0 fp lo K pr rp cfp t' m eL' eN' o := by
  subst h h3 h4; exact hs

theorem Ret.schrumpf {τ : Ty} {o : EndAusgang (vertragVon D f) l (τ :: Γ)} {t : T} {m : Runner.Mem} {eL eN : Runner.W}
    (hs : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o) : Ret L P f σ0 ρ0 fp lo K pr rp cfp t m eL eN o.schrumpf := by
  cases o with
  | leave _ σ ρ => obtain ⟨m', s, a, en, hw, kp⟩ := hs; exact ⟨m', s, a, envAt_tail en, hw, kp⟩
  | next _ σ ρ => obtain ⟨m', s, a, en, hw, kp⟩ := hs; exact ⟨m', s, a, envAt_tail en, hw, kp⟩
  | zurueck | logik | why | hardware => exact hs

end

theorem lowEnd_ok {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → (b : Endblock D (vertragVon D f) l Γ Λ) → (c : List II) →
    (top : Nat) → lowEnd A L lo (cens, tens) pr ex b = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS L m pc fp K (frei Γ) c ρ →
    lo ≤ frei Γ → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ) →
    Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R b σ ρ)
  | _, Γ, Λ, .ret e _, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, hlo, _, hk, hWa, hpr => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [execEnd, Ret]
    exact ret_ok hlo0 hens e he (by omega) m pc σ ρ hp hlo hk hW hWa
  | _, Γ, _, .cons s rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs1, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hFB3 : FB = 3 := rfl
    have ih := lowS_ok (O := O) (passes := passes) (σ0 := σ0) (ex := exPlus ex cr.length) hS hA hlo0 hens s cs ts
      hs1 (by omega) (by omega) hW m pc σ ρ hp.left (by omega) hlo hu hk hWa hpr
    have hL : pc + BitVec.ofNat 64 (16 * cs.length) + BitVec.ofInt 64 (exPlus ex cr.length).1 =
        pc + BitVec.ofNat 64 (16 * (cs ++ cr).length) + BitVec.ofInt 64 ex.1 := by
      simp only [exPlus, List.length_append]; exact tgt_eq (by omega)
    have hN : pc + BitVec.ofNat 64 (16 * cs.length) + BitVec.ofInt 64 (exPlus ex cr.length).2 =
        pc + BitVec.ofNat 64 (16 * (cs ++ cr).length) + BitVec.ofInt 64 ex.2 := by
      simp only [exPlus, List.length_append]; exact tgt_eq (by omega)
    simp only [execEnd]
    generalize execStmt O passes R s σ ρ = o at ih ⊢
    cases o with
    | ok σ1 ρ1 =>
      obtain ⟨m1, s1, a1, e1, hw1, k1⟩ := ih
      have hf := codeFar_right (n := cs.length) (k := cr.length) (by simpa using hp.far)
      have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K (frei Γ) cr ρ1 :=
        ⟨hp.ctx, hp.small, frameOK_agreeW hp.frame a1, codeAt_agreeWIn hW a1 (codeAt_right hp.code) hf, hf, e1, trivial,
          wstab_true _ _⟩
      have ih2 := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) (ex := ex) hS hA hlo0 hens rest cr tr hr
        (by omega) (by omega) hW m1 _ σ1 ρ1 hp1 hlo (hu.agreeW hW a1 (by omega)) (hk.agreeW hW a1 (by omega)) hw1 hpr
      rw [pc_add1]
      exact Ret.prefix (by omega) s1 a1 k1 ih2
    | zurueck σ' v => exact ih
    | logik e => exact ih
    | leave _ σ' ρ' => exact (show Reach L fp lo K pr _ m _ σ' ρ' from hL ▸ ih)
    | next _ σ' ρ' => exact (show Reach L fp lo K pr _ m _ σ' ρ' from hN ▸ ih)
    | hardware e => exact ih
    | why => exact (ih : False).elim
  | _, Γ, Λ, .bind e rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
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
      lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) e _ ce te he (by omega) m pc ρ hpw
    have a1 := Agree.widen a1s hks
    have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
    have hf := codeFar_right (n := ce.length) (k := cr.length) (by simpa using hp.far)
    have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (frei Γ + 1) cr
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) :=
      ⟨by simp only [frei, List.length_cons]; omega, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf,
       envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) hw hen, trivial, wstab_true _ _⟩
    have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (ex := ex) rest cr tr hr (by omega) (by omega) hW m1 _ (σ.lese Λ e.orte) _ hp1
      (by simp only [frei, List.length_cons] at hlo ⊢; omega) (hu.agree a1 hp.frame (by omega))
      (hk.agree a1 hp.frame (by omega)) hWa1 (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
    rw [pc_add1]
    exact Ret.prefix (by omega) s1 (a1.mono (by omega)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Ret.schrumpf ih)
  | _, Γ, Λ, .bindCall g args he _ _ rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
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
      have hp1 := hp.left.nextW hW a1 (by have := hp.ctx; omega) (Nat.le_refl _) (by omega)
      have s2 := mov_to hp1.code hp1.frame (j := frei Γ) (s := frei Γ + 2) (by omega) (by omega) hp.small hw
      rw [← pc_add1] at s2
      let m2 := write m1 (slot fp (BitVec.ofNat 64 (frei Γ))) 8 w.toNat
      have a2s : Agree fp (frei Γ) Ks m1 m2 := agree_write (frameOK_sub hp1.frame hks).room (Nat.le_refl _) (by omega) _
      have a2 : Agree fp (frei Γ) K m1 m2 := Agree.widen a2s hks
      have hw2 : WeltAt m2 L σ' :=
        weltAt_stab hW.lay (by have := hW.lo; omega) m1 m2 hw1 (a2s.mono (Nat.zero_le _))
      have hq := hp.nextW hW (a1.trans (agreeW_of a2)) (d' := frei Γ + 1) (by have := hp.ctx; omega) (by omega)
        (by omega)
      have hp2 : PreS L m2 _ fp K (frei Γ + 1) cr (Env.cons (ergWert he v) ρ) :=
        ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
         envAt_cons hq.env (rd_same hp1.frame (by omega) w) (encErg_wert he hew), trivial, wstab_true _ _⟩
      have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (ex := ex) rest cr tr hr (by omega) (by omega) hW m2 _ σ' _ hp2
        (by simp only [frei, List.length_cons] at hlo ⊢; omega)
        (hu.agreeW hW (a1.trans (agreeW_of a2)) (by omega)) (hk.agreeW hW (a1.trans (agreeW_of a2)) (by omega)) hw2
        (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
      rw [pc_add1 pc (callC A g (frei Γ) ca ++ [ci 2 (frei Γ) (frei Γ + 2) 0]) cr]
      exact Ret.prefix (by omega) (s1.trans s2) ((a1.trans (agreeW_of a2)).mono (by omega))
        (keeps_of_agreeW hW (a1.trans (agreeW_of a2)) hpr (by have := hW.ks; omega)) (Ret.schrumpf ih)
    | logik e => exact hc
    | why _ _ => exact hc.elim
    | hardware e => exact hc
  | _, Γ, Λ, .ite cnd t e, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, hce, ⟨ct, tt⟩, hct, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append, List.length_singleton] at hs
    have hFB3 : FB = 3 := rfl
    have hsm := hp.small
    have htop := lowE_top cnd (frei Γ) cc tc hcc
    have hq : PreS L m pc fp K (frei Γ) (cc ++ ([ci 19 (frei Γ) (16 * (ct.length + 1)) 0] ++ (ct ++ ce))) ρ := by
      simpa [List.append_assoc] using hp
    have hks := hW.ks
    have hpw := PreS.welt hq.left hks hWa hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, s1, a1s, w, hw, hen⟩ := lowE_ok (fp := fp) (K := Ks) (σ.lese Λ cnd.orte) (σ.lese Λ cnd.orte) (fun _ h => h) cnd
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
      have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) (ex := exPlus ex ce.length) hS hA hlo0 hens t ct
        tt hct (by omega) (by omega) hW m1 _ (σ.lese Λ cnd.orte) ρ h2.left hlo hu1 hk1 hWa1 hpr
      refine Ret.prefix (by omega) (s1.trans sb) (a1.mono (by omega)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Ret.cast ih rfl ?_ ?_)
      · simp only [exPlus, List.length_append, List.length_singleton, addr_norm]
        exact tgt_eq (by omega)
      · simp only [exPlus, List.length_append, List.length_singleton, addr_norm]
        exact tgt_eq (by omega)
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
      have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) (ex := ex) hS hA hlo0 hens e ce te hce (by omega)
        (by omega) hW m1 _ (σ.lese Λ cnd.orte) ρ h4 hlo hu1 hk1 hWa1 hpr
      refine Ret.prefix (by omega) (s1.trans sb) (a1.mono (by omega)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Ret.cast ih ?_ ?_ ?_)
      · simp only [T.mk.injEq, and_true, List.length_singleton, addr_norm]
        congr 2
        omega
      · simp only [List.length_append, List.length_singleton, addr_norm]
        exact tgt_eq0 (by omega)
      · simp only [List.length_append, List.length_singleton, addr_norm]
        exact tgt_eq0 (by omega)
  | _, _, _, .retWhy .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .leave .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .next .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .bindCallElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, Γ, Λ, .bindAxiom a args he _ _ _ _ rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ct, tt⟩, ht, ck, hck, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hks := hW.ks
    have hFB3 : FB = 3 := rfl
    simp only [execEnd]
    rcases torBind_ok (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ) he ht hck (by omega) (by omega) hW hp hWa with
      ⟨v, m2, w, hAA, s12, a12, hw2, hen, hW2⟩ | ⟨hAA, hst⟩
    · rw [hAA]
      have hq := hp.nextW hW a12 (d' := frei Γ + 1) (by have := hp.ctx; omega) (by omega) (by omega)
      have hp2 : PreS L m2 _ fp K (frei Γ + 1) cr (Env.cons (ergWert he v) ρ) :=
        ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
         envAt_cons hq.env hw2 hen, trivial, wstab_true _ _⟩
      have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (ex := ex) rest cr tr hr (by omega)
        (by omega) hW m2 _ _ _ hp2
        (by simp only [frei, List.length_cons] at hlo ⊢; omega)
        (hu.agreeW hW a12 (by omega)) (hk.agreeW hW a12 (by omega)) hW2
        (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
      rw [pc_add1 pc (ct ++ ck) cr]
      exact Ret.prefix (by omega) s12 (a12.mono (by omega)) (keeps_of_agreeW hW a12 hpr (by omega))
        (Ret.schrumpf ih)
    · rw [hAA]
      exact hst
  | _, Γ, Λ, .bindAxiomElse a args he _ _ _ _ _ err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa,
      hpr => by
    simp only [lowEnd] at h
    split at h
    · next b lo' hi' hb hτ =>
      split at h
      · next hc =>
        obtain ⟨hf, hlo', hn⟩ := hc
        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
        obtain ⟨⟨ct, tt⟩, ht, ck, hck, ⟨ce, te⟩, hce, ⟨cr, tr⟩, hr, hc⟩ := h
        split at hc
        · next hJ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          simp only [List.length_append, fehlC_len] at hs
          have hFB3 : FB = 3 := rfl
          have hks := hW.ks
          have h7 := torC_top1 ht
          simp only [execEnd]
          rcases torElse_ok (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ) he hτ hb hf hlo' hn ht hck hJ (by omega)
            (by omega) hW hp hWa with ⟨v, m2, w, hAA, s12, a12, hw2, hen, hW2⟩ | ⟨r, m2, hAA, s12, a12, hw2, hW2⟩ |
            ⟨hAA, hst⟩
          · rw [hAA]
            have hp2 : PreS L m pc fp K (frei Γ) ((ct ++ fehlC (frei Γ) b.fehler ((16 * (ck.length + cr.length) : Nat) : Int)
                ++ ck) ++ (cr ++ ce)) ρ := by simpa only [List.append_assoc] using hp
            have hq := hp2.nextW hW a12 (d' := frei Γ + 1) (by have := hp.ctx; omega) (by omega) (by omega)
            simp only [List.length_append, fehlC_len] at hq
            have hp3 : PreS L m2 _ fp K (frei Γ + 1) cr (Env.cons (ergWert he v) ρ) :=
              ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.left.code, hq.left.far,
               envAt_cons hq.env hw2 hen, trivial, wstab_true _ _⟩
            have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (ex := exPlus ex ce.length)
              rest cr tr hr (by omega) (by omega) hW m2 _ _ _ hp3
              (by simp only [frei, List.length_cons] at hlo ⊢; omega)
              (hu.agreeW hW a12 (by omega)) (hk.agreeW hW a12 (by omega)) hW2
              (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
            refine Ret.prefix (by omega) s12 (a12.mono (by omega)) (keeps_of_agreeW hW a12 hpr (by omega))
              (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_)
            · simp only [exPlus, List.length_append, fehlC_len, addr_norm]
              exact tgt_eq (by omega)
            · simp only [exPlus, List.length_append, fehlC_len, addr_norm]
              exact tgt_eq (by omega)
          · rw [hAA]
            have hp2 : PreS L m pc fp K (frei Γ) ((ct ++ fehlC (frei Γ) b.fehler ((16 * (ck.length + cr.length) : Nat) : Int)
                ++ ck ++ cr) ++ ce) ρ := by simpa only [List.append_assoc] using hp
            have hq := hp2.nextW hW a12 (d' := frei Γ + 1) (by have := hp.ctx; omega) (by omega) (by omega)
            simp only [List.length_append, fehlC_len] at hq
            have hp3 : PreS L m2 _ fp K (frei Γ + 1) ce (Env.cons (τ := .why (D.agruende a)) r ρ) :=
              ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
               envAt_cons hq.env hw2 rfl, trivial, wstab_true _ _⟩
            have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (ex := ex)
              err ce te hce (by omega) (by omega) hW m2 _ _ _ hp3
              (by simp only [frei, List.length_cons] at hlo ⊢; omega)
              (hu.agreeW hW a12 (by omega)) (hk.agreeW hW a12 (by omega)) hW2
              (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
            refine Ret.prefix (by omega) s12 (a12.mono (by omega)) (keeps_of_agreeW hW a12 hpr (by omega))
              (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_)
            · simp only [List.length_append, fehlC_len, addr_norm]
              exact tgt_eq0 (by omega)
            · simp only [List.length_append, fehlC_len, addr_norm]
              exact tgt_eq0 (by omega)
          · rw [hAA]
            exact hst
        · cases hc
      · cases h
    · cases h
  | _, _, _, .regRead .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .regReadElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, Γ, Λ, .awaits g _ _ _ _ rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    simp only [lowEnd] at h
    split at h
    · next hl =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨cr, tr⟩, hr, hc⟩ := h
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [List.length_append] at hs
      have hFB3 : FB = 3 := rfl
      have hks := hW.ks
      obtain ⟨m1, s1, A, hp1, hW1⟩ := awaits_head hl (by omega) hW hp hWa
      simp only [execEnd, SichtOK.sicht, ↓reduceIte]
      have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (ex := ex) rest cr tr hr (by omega)
        (by omega) hW m1 _ ((σ.fragt (.inr (.inr g))).lese Λ [.inr g]) _ hp1
        (by simp only [frei, List.length_cons] at hlo ⊢; omega) (hu.agreeW hW (A.mono hlo) (by omega))
        (hk.agreeW hW (A.mono hlo) (by omega)) hW1 (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
      rw [pc_add1]
      exact Ret.prefix (by omega) s1 (A.mono hlo) (keeps_of_agreeW hW A hpr (by omega)) (Ret.schrumpf ih)
    · cases h
  | _, _, _, .bindCallInd .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .narrow .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, Γ, Λ, .exchange g neu _ _ rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    simp only [lowEnd] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure] at h
      obtain ⟨⟨cn, tn⟩, hn, ⟨cr, tr⟩, hr, h⟩ := h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlen := exC_len (frei Γ) (L.ga g) cn
        simp only [List.length_append, hlen] at hs
        have hFB3 : FB = 3 := rfl
        have hks := hW.ks
        obtain ⟨m3, s3, A, hp3, hW3⟩ := exch_head (Λ := Λ) hn (by omega) (by omega) hW hp hWa
        simp only [execEnd]
        have ih := lowEnd_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (ex := ex) rest cr tr hr (by omega)
          (by omega) hW m3 _ _ _ hp3
          (by simp only [frei, List.length_cons] at hlo ⊢; omega) (hu.agreeW hW (A.mono hlo) (by omega))
          (hk.agreeW hW (A.mono hlo) (by omega)) hW3 (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
        rw [pc_add1]
        exact Ret.prefix (by omega) s3 (A.mono hlo) (keeps_of_agreeW hW A hpr (by omega)) (Ret.schrumpf ih)
      · cases h
    · cases h

end Gabbro.Stage0.Senke
