/-
  File:      stage0/Stage0/Senke/AnweisungSatz.lean
  Subject:   `ir_sim` for statements and blocks, calls included: where machine G ends a block normally (`ok`), the
             lowered code runs to its end and leaves the new environment in the frame, changing no slot below
             `lo`; where G ends in a logic outcome, the code stops with its `exit_group` code. G answers nothing
             else for a lowered block (`Sim`).
-/
import Stage0.Senke.Rueckkehr

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration} {V : Vertrag D}

/-- What the code from `t` to `e` does for G's outcome `o` in the body of `f`: `ok` runs to `e`, `zurueck` returns
    (`RetZ`), `logik` stops with its code. -/
def Sim (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (rp cfp : Runner.W) {l : Bool}
    {Γ : Ctx} (fp : Runner.W) (lo K : Nat) (t : T) (m : Runner.Mem) (e : Runner.W) :
    Ausgang (vertragVon D f) l Γ → Prop
  | .ok _ ρ' => ∃ m', Star t m ⟨e, fp⟩ m' ∧ Agree fp lo K m m' ∧ EnvAt m' fp ρ'
  | .zurueck σ' v => RetZ P f σ0 ρ0 fp K rp cfp t m σ' v
  | .logik c => Stops t m (logikCode c)
  | _ => False

section
variable {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp : Runner.W} {l : Bool}
  {Γ : Ctx} {fp : Runner.W} {lo K : Nat}

theorem Sim.prefix {o : Ausgang (vertragVon D f) l Γ} {t0 t : T} {m0 m : Runner.Mem} {e : Runner.W} (hl : FB ≤ lo)
    (h : Star t0 m0 t m) (ha : Agree fp lo K m0 m) (hs : Sim P f σ0 ρ0 rp cfp fp lo K t m e o) :
    Sim P f σ0 ρ0 rp cfp fp lo K t0 m0 e o := by
  cases o with
  | ok σ ρ => obtain ⟨m', s, a, en⟩ := hs; exact ⟨m', h.trans s, ha.trans a, en⟩
  | zurueck σ' v =>
    have hFB3 : FB = 3 := rfl
    exact RetZ.prefix h (ha.mono (by omega)) hs
  | logik c => exact Stops.prefix h hs
  | why | leave | next | hardware => exact hs

theorem Sim.cont {o : Ausgang (vertragVon D f) l Γ} {t : T} {m : Runner.Mem} {e1 e2 : Runner.W}
    (hs : Sim P f σ0 ρ0 rp cfp fp lo K t m e1 o)
    (hj : ∀ m', Agree fp lo K m m' → Star ⟨e1, fp⟩ m' ⟨e2, fp⟩ m') : Sim P f σ0 ρ0 rp cfp fp lo K t m e2 o := by
  cases o with
  | ok σ ρ => obtain ⟨m', s, a, en⟩ := hs; exact ⟨m', s.trans (hj m' a), a, en⟩
  | logik c => exact hs
  | zurueck | why | leave | next | hardware => exact hs

theorem Sim.cast {o : Ausgang (vertragVon D f) l Γ} {t t' : T} {m : Runner.Mem} {e e' : Runner.W}
    (hs : Sim P f σ0 ρ0 rp cfp fp lo K t m e o) (h1 : t = t') (h2 : e = e') :
    Sim P f σ0 ρ0 rp cfp fp lo K t' m e' o := by subst h1; subst h2; exact hs

theorem Sim.schrumpf {τ : Ty} {o : Ausgang (vertragVon D f) l (τ :: Γ)} {t : T} {m : Runner.Mem} {e : Runner.W}
    (hs : Sim P f σ0 ρ0 rp cfp fp lo K t m e o) : Sim P f σ0 ρ0 rp cfp fp lo K t m e o.schrumpf := by
  cases o with
  | ok σ ρ => obtain ⟨m', s, a, en⟩ := hs; exact ⟨m', s, a, envAt_tail en⟩
  | logik c => exact hs
  | zurueck | why | leave | next | hardware => exact hs

end

theorem encErg_wert {e : Option Ty} {τ : Ty} (he : e = some τ) {v : ErgVal D e} {w : Runner.W}
    (h : EncErg e v w) : Enc τ (ergWert he v) w := by
  subst he; exact h

mutual
theorem lowS_ok {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE (P.ensures f) (lo + 1) = some (cens, tens)) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (s : Stmt D (vertragVon D f) l Γ Λ Λ') → (c : List II) → (top : Nat) →
    lowS A lo (cens, tens) s = some (c, top) → top + cap ≤ K → 16 * c.length < 2 ^ 31 →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS m pc fp K (frei Γ) c ρ →
    FB ≤ lo → lo ≤ frei Γ → Umf A C dv m fp K → Kopf f m fp K rp cfp ρ0 →
    Sim P f σ0 ρ0 rp cfp fp lo K ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (execStmt O passes R s σ ρ)
  | _, Γ, Λ, _, .assignVar x e, c, top, h, hK, _, m, pc, σ, ρ, hp, _, hlo2, _, _ => by
    simp only [lowS] at h
    split at h
    · next hlx =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ce, te⟩, he, hc⟩ := h
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [execStmt, Sim]
      have htop := lowE_top e _ _ _ he
      obtain ⟨m1, s1, a1, w, hw, hen⟩ := lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) e _ ce te he (by omega)
        m pc ρ hp.left
      have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
      have hxs := vslot_lt x
      have hsm := hp.small
      have s2 := mov_to hp1.code hp1.frame (j := vslot x) (by omega) (by omega) hsm hw
      refine ⟨_, s1.trans (by rw [pc_add1]; exact s2), (a1.mono hlo2).trans
        (agree_write hp1.frame.room hlx (by omega) _), ?_⟩
      have hF1 := hp1.frame
      refine envAt_set hp1.env (rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))) hen ?_
      intro τ' y hy
      have := vslot_lt y
      exact rd64_write_far (slot_far hF1.room (by omega) (by omega) (vslot_ne hy).symm)
    · simp at h
  | _, Γ, Λ, _, .ite cnd t e, c, top, h, hK, hs, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk => by
    simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cc, tc⟩, hcc, ⟨ct, tt⟩, hct, ⟨ce, te⟩, hce, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append, List.length_singleton] at hs
    have hsm := hp.small
    have htop := lowE_top cnd (frei Γ) cc tc hcc
    have hq : PreS m pc fp K (frei Γ) (cc ++ ([ci 19 (frei Γ) (16 * (ct.length + 2)) 0] ++ (ct ++
        ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce)))) ρ := by simpa [List.append_assoc] using hp
    obtain ⟨m1, s1, a1, w, hw, hen⟩ := lowE_ok (fp := fp) (K := K) (σ.lese Λ cnd.orte) (σ.lese Λ cnd.orte) cnd
      (frei Γ) cc tc hcc (by omega) m pc ρ hq.left
    have h1 := hq.next a1 (Nat.le_refl _) (by omega)
    have hu1 := hu.agree (a1.mono hlo2) hp.frame hlo
    have hk1 := hk.agree (a1.mono hlo2) hp.frame (by omega)
    have hF1 := h1.frame
    have hbrz := h1.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hbrz
    have h2 := h1.next (a := [ci 19 (frei Γ) (16 * (ct.length + 2)) 0]) (Agree.refl _ _ _ _) (Nat.le_refl _)
      (by omega)
    have hd0 : sx (II.f (frei Γ : Int)) = BitVec.ofNat 64 (frei Γ) := sx_nat (by omega)
    simp only [execStmt]
    split
    · next hb =>
      -- the condition holds: brz falls through, the `then` block, jmp to the end
      have hw1 : w = 1 := by
        simp only [Enc] at hen
        rw [hen, if_pos hb]
      have sb := star_ins (fp := fp) (m' := m1) (codeAt_left h1.code) (by simp [ci])
        (by simp only [ci]; exact run_brz_ne (t := ⟨_, fp⟩) hbrz (by rw [hd0]; exact hw) (by rw [hw1]; decide))
      have ih := lowB_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens t ct tt hct (by omega) (by omega) m1 _ (σ.lese Λ cnd.orte) ρ h2.left hlo hlo2 hu1 hk1
      have hf3 := codeFar_right (n := ct.length) (k := ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length)
        (by simpa using h2.far)
      refine Sim.prefix hlo (s1.trans sb) (a1.mono hlo2) (Sim.cont ih fun m2 a2 => ?_)
      have hc3 := (codeAt_right h2.code).agree a2 hf3
      have hjmp := hc3 0 (by simp)
      simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hjmp
      have sj := Star.one (run_step (t := ⟨_, fp⟩) hjmp (by decide) (run_jmp (t := ⟨_, fp⟩) hjmp))
      have hl : sx (II.f (16 * ((ce.length : Int) + 1))) = BitVec.ofNat 64 (16 * (ce.length + 1)) := by
        have := sx_nat (d := 16 * (ce.length + 1)) (by omega); simpa using this
      rw [hl] at sj
      refine star_cast sj rfl ?_
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
      have ih := lowB_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens e ce te hce (by omega) (by omega) m1 _ (σ.lese Λ cnd.orte) ρ h4 hlo hlo2 hu1 hk1
      refine Sim.prefix hlo (s1.trans sb) (a1.mono hlo2) (Sim.cast ih ?_ ?_)
      · simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, List.length_cons,
          List.length_nil, addr_norm]
        congr 2
        omega
      · simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil, addr_norm]
        congr 2
        omega
  | _, Γ, Λ, _, .call f args _ _, c, top, h, hK, _, m, pc, σ, ρ, hp, _, hlo2, hu, hk => by
    simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, hca, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hct : frei Γ + FB + (D.params f).length + 1 ≤ callTop f (frei Γ) ta := by simp only [callTop]; omega
    have hc := callC_ok hS (hA f) args (σ.lese Λ args.orte) (σ.lese Λ args.orte) hca (by omega) hp hu
    simp only [execStmt]
    generalize R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = o at hc ⊢
    cases o with
    | ok σ' v =>
      obtain ⟨m1, s1, a1, _⟩ := hc
      exact ⟨m1, s1, a1.mono hlo2, envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)⟩
    | logik e => exact hc
    | why _ _ => exact hc.elim
    | hardware _ => exact hc.elim
  | _, Γ, Λ, _, .ret e _, c, top, h, hK, _, m, pc, σ, ρ, hp, _, hlo2, _, hk => by
    simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [execStmt, Sim]
    exact ret_ok hlo0 hens e he (by omega) m pc σ ρ hp hlo2 hk
  | _, _, _, _, .assignSlot .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .assignThru .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .assignGlob .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .putBytes .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .shift .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .onOption .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .onTag .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .onWhy .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .callInd .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .locks .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .breaking .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .traverse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .retry .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .forever .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .axiomCall .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .regWrite .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .transition .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .publish .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .advances .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .retires .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .retWhy .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .leave .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .next .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .assignSlotRef .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h

theorem lowB_ok {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE (P.ensures f) (lo + 1) = some (cens, tens)) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (b : Block D (vertragVon D f) l Γ Λ Λ') → (c : List II) → (top : Nat) →
    lowB A lo (cens, tens) b = some (c, top) → top + cap ≤ K → 16 * c.length < 2 ^ 31 →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS m pc fp K (frei Γ) c ρ →
    FB ≤ lo → lo ≤ frei Γ → Umf A C dv m fp K → Kopf f m fp K rp cfp ρ0 →
    Sim P f σ0 ρ0 rp cfp fp lo K ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (execBlock O passes R b σ ρ)
  | _, Γ, _, _, .nil, c, top, h, _, _, m, pc, σ, ρ, hp, _, _, _, _ => by
    simp only [lowB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execBlock, Sim]
    exact ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, hp.env⟩
  | _, Γ, _, _, .cons s rest, c, top, h, hK, hs, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk => by
    simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cs, ts⟩, hs1, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have ih := lowS_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens s cs ts hs1 (by omega) (by omega) m pc σ ρ hp.left hlo hlo2 hu hk
    simp only [execBlock]
    generalize execStmt O passes R s σ ρ = o at ih ⊢
    cases o with
    | ok σ1 ρ1 =>
      obtain ⟨m1, s1, a1, e1⟩ := ih
      have hf := codeFar_right (n := cs.length) (k := cr.length) (by simpa using hp.far)
      have hp1 : PreS m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K (frei Γ) cr ρ1 :=
        ⟨hp.ctx, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf, e1, trivial, wstab_true _ _⟩
      have ih2 := lowB_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens rest cr tr hr (by omega) (by omega) m1 _ σ1 ρ1 hp1 hlo hlo2
        (hu.agree a1 hp.frame hlo) (hk.agree a1 hp.frame (by omega))
      rw [pc_add1]
      exact Sim.prefix hlo s1 a1 ih2
    | zurueck | why | leave | next | logik | hardware => exact ih
  | _, Γ, Λ, _, .bind e rest, c, top, h, hK, hs, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk => by
    simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    simp only [execBlock]
    have htop := lowE_top e _ _ _ he
    obtain ⟨m1, s1, a1, w, hw, hen⟩ :=
      lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) e _ ce te he (by omega) m pc ρ hp.left
    have hf := codeFar_right (n := ce.length) (k := cr.length) (by simpa using hp.far)
    have hp1 : PreS m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (frei Γ + 1) cr
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) :=
      ⟨by simp only [frei, List.length_cons]; omega, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf,
       envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) hw hen, trivial, wstab_true _ _⟩
    have ih := lowB_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens rest cr tr hr (by omega) (by omega) m1 _ (σ.lese Λ e.orte) _ hp1 hlo
      (by simp only [frei, List.length_cons] at hlo2 ⊢; omega) (hu.agree (a1.mono hlo2) hp.frame hlo)
      (hk.agree (a1.mono hlo2) hp.frame (by omega))
    rw [pc_add1]
    exact Sim.prefix hlo s1 (a1.mono hlo2) (Sim.schrumpf ih)
  | _, Γ, Λ, _, .bindCall f args he _ _ rest, c, top, h, hK, hs, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk => by
    simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, hca, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hFB3 : FB = 3 := rfl
    have hct : frei Γ + FB + (D.params f).length + 1 ≤ callTop f (frei Γ) ta := by simp only [callTop]; omega
    have hc := callC_ok hS (hA f) args (σ.lese Λ args.orte) (σ.lese Λ args.orte) hca (by omega) hp.left.left hu
    simp only [execBlock]
    generalize R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = o at hc ⊢
    cases o with
    | ok σ' v =>
      obtain ⟨m1, s1, a1, w, hw, hew⟩ := hc
      have hp1 := hp.left.next a1 (Nat.le_refl _) (by omega)
      have s2 := mov_to hp1.code hp1.frame (j := frei Γ) (s := frei Γ + 2) (by omega) (by omega) hp.small hw
      rw [← pc_add1] at s2
      let m2 := write m1 (slot fp (BitVec.ofNat 64 (frei Γ))) 8 w.toNat
      have a2 : Agree fp (frei Γ) K m1 m2 := agree_write hp1.frame.room (Nat.le_refl _) (by omega) _
      have hq := hp.next (a1.trans a2) (d' := frei Γ + 1) (by omega) (by omega)
      have hp2 : PreS m2 _ fp K (frei Γ + 1) cr (Env.cons (ergWert he v) ρ) :=
        ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
         envAt_cons hq.env (rd_same hp1.frame (by omega) w) (encErg_wert he hew), trivial, wstab_true _ _⟩
      have ih := lowB_ok (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens rest cr tr hr (by omega) (by omega) m2 _ σ' _ hp2 hlo
        (by simp only [frei, List.length_cons] at hlo2 ⊢; omega)
        (hu.agree ((a1.trans a2).mono hlo2) hp.frame hlo) (hk.agree ((a1.trans a2).mono hlo2) hp.frame (by omega))
      rw [pc_add1 pc (callC A f (frei Γ) ca ++ [ci 2 (frei Γ) (frei Γ + 2) 0]) cr]
      exact Sim.prefix hlo (s1.trans s2) ((a1.trans a2).mono hlo2) (Sim.schrumpf ih)
    | logik e => exact hc
    | why _ _ => exact hc.elim
    | hardware _ => exact hc.elim
  | _, _, _, _, .bindCallInd .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .bindCallElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .bindAxiom .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .bindAxiomElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .regRead .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .regReadElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .awaits .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .exchange .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .narrow .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .check .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .float .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatLit .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatOf .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatNarrow .., _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
end

end Gabbro.Stage0.Senke
