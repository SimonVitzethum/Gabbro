/-
  File:      stage0/Stage0/Senke/Rueckkehr.lean
  Subject:   `ret`: the result into slot `lo`, `ensures` over it and the parameters, then back to the caller with the
             result in slot 2 or `exit_group(102)` (`RetZ`, `ret_ok`); the callee's header and parameters (`Kopf`).
-/
import Stage0.Senke.Aufruf
import Stage0.Senke.Ausdruck.Old.Capture

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable [Kern]

variable {D : Deklaration} {L : Lay D}

/-- What the code from `t` does when G returns `v` in the world `σ'` from the body of `f`, without the world:
    `ensures` fails, the stop 102; else back to the caller with the result in slot 2, nothing below changed. -/
def RetZ0 (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (K : Nat)
    (rp cfp : Runner.W) (t : T) (m : Runner.Mem) (σ' : World D) (v : ErgVal D (D.erg f)) : Prop :=
  if wahr? (eval σ0 (P.ensures f) (σ'.lese (vertragVon D f).ende (P.ensures f).orte) (ergEnv (D.erg f) v ρ0)) = false
  then Stops t m 102
  else ∃ m', Star t m ⟨rp, cfp⟩ m' ∧ Agree fp 2 K m m' ∧
    ResultAt L m' fp (FB + contextWords (D.params f)) (D.erg f) v ∧
      ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
      ReturnFlag m' fp (contextWords (D.params f)) true (returnWords (D.erg f) (D.gruende f))

/-- `RetZ0` and the world `σ'` in memory after the return (`WeltAt`). -/
def RetZ (L : Lay D) (P : Programm D) (f : D.Fn) (σ0 : World D) (ρ0 : Env D (D.params f)) (fp : Runner.W) (K : Nat)
    (rp cfp : Runner.W) (t : T) (m : Runner.Mem) (σ' : World D) (v : ErgVal D (D.erg f)) : Prop :=
  if wahr? (eval σ0 (P.ensures f) (σ'.lese (vertragVon D f).ende (P.ensures f).orte) (ergEnv (D.erg f) v ρ0)) = false
  then Stops t m 102
  else ∃ m', Star t m ⟨rp, cfp⟩ m' ∧ AgreeW L fp 2 K m m' ∧
    (ResultAt L m' fp (FB + contextWords (D.params f)) (D.erg f) v ∧
      ReturnMirror m' fp (FB + contextWords (D.params f)) ∧
      ReturnFlag m' fp (contextWords (D.params f)) true (returnWords (D.erg f) (D.gruende f))) ∧ WeltAt m' L σ'

theorem RetZ.prefix {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {fp : Runner.W}
    {K : Nat} {rp cfp : Runner.W} {t0 t : T} {m0 m : Runner.Mem} {σ' : World D} {v : ErgVal D (D.erg f)}
    (h : Star t0 m0 t m) (ha : AgreeW L fp 2 K m0 m) (hs : RetZ L P f σ0 ρ0 fp K rp cfp t m σ' v) :
    RetZ L P f σ0 ρ0 fp K rp cfp t0 m0 σ' v := by
  simp only [RetZ] at hs ⊢
  split
  · next hf => rw [if_pos hf] at hs; exact Stops.prefix h hs
  · next hf =>
    rw [if_neg hf] at hs
    obtain ⟨m', s, a, hw, hw'⟩ := hs
    exact ⟨m', h.trans s, ha.trans a, hw, hw'⟩

/-- The callee's header and parameters, below `lo`. -/
structure Kopf (L : Lay D) (f : D.Fn) (m : Runner.Mem) (fp : Runner.W) (K : Nat) (rp cfp : Runner.W)
    (ρ0 : Env D (D.params f)) (P : Programm D) (σ0 : World D) : Prop where
  r0 : m.rd64 (slot fp (BitVec.ofNat 64 0)) = some rp
  r1 : m.rd64 (slot fp (BitVec.ofNat 64 1)) = some cfp
  env : EnvAt L m fp ρ0
  big : FB + (contextWords (D.params f)) ≤ K
  entry : SnapAt L (oldCells (P.ensures f)) σ0 m fp

theorem Kopf.agree {P : Programm D} {σ0 : World D} {f : D.Fn} {m m' : Runner.Mem} {fp : Runner.W} {K lo : Nat} {rp cfp : Runner.W}
    {ρ0 : Env D (D.params f)} (h : Kopf L f m fp K rp cfp ρ0 P σ0) (ha : Agree fp lo K m m') (hF : FrameOK m fp K)
    (hl : FB + (contextWords (D.params f)) ≤ lo) : Kopf L f m' fp K rp cfp ρ0 P σ0 := by
  have hb := h.big
  have hFB3 : FB = 4 := rfl
  have ha' := ha.mono hl
  refine ⟨?_, ?_, envAt_agree h.env ha' hF (Nat.le_refl _) hb, hb, h.entry.agree hF ha' (by omega) hb⟩
  · rw [agree_rd_low ha' hF.room (by omega) hb]; exact h.r0
  · rw [agree_rd_low ha' hF.room (by omega) hb]; exact h.r1

/-! ## What a statement keeps, under the frame's `WIn` -/

theorem agreeW_rdW {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {Ks K lo i : Nat} (hW : WIn L fp Ks K)
    (ha : AgreeW L fp lo K m m') (hi : i < lo) (hK : lo ≤ K) :
    m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i)) :=
  agreeW_rd_low ha hW.top (by have := hW.room; omega) hi hK

theorem codeAt_agreeWIn {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {Ks K lo : Nat} (hW : WIn L fp Ks K)
    (ha : AgreeW L fp lo K m m') {pc : Runner.W} {is : List II} (hc : CodeAt m pc is)
    (hf : CodeFar pc is.length fp K) : CodeAt m' pc is :=
  codeAt_agreeW ha hW.top hW.lay.2.2 hW.ord hc hf

theorem envAt_agreeWIn {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {Ks K d reserved : Nat} {Γ : Ctx} {ρ : Env D Γ}
    (hW : WIn L fp Ks K) (h : EnvAt L m fp ρ reserved) (ha : AgreeW L fp d K m m') (hd : frei Γ reserved ≤ d) (hK : d ≤ K) :
    EnvAt L m' fp ρ reserved :=
  envAt_agreeW h ha hW.top (by have := hW.room; omega) hd hK

theorem keeps_of_agreeW {L : Lay D} {fp : Runner.W} {pr : List Nat} {Ks K d : Nat} {m m' : Runner.Mem}
    (hW : WIn L fp Ks K) (ha : AgreeW L fp d K m m') (hp : ∀ j ∈ pr, j < d) (hd : d ≤ K) : Keeps fp pr m m' :=
  fun j hj => agreeW_rdW hW ha (hp j hj) hd

theorem Umf.agreeW {L : Lay D} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {m m' : Runner.Mem}
    {fp : Runner.W} {Ks Ks' K lo : Nat} (hW : WIn L fp Ks' K) (h : Umf L A C dv m fp Ks K) (ha : AgreeW L fp lo K m m')
    (hlo : FB ≤ lo) : Umf L A C dv m' fp Ks K :=
  ⟨pcode_agreeW h.code ha hW.top hW.lay.2.2 hW.ord, by
    have hFB3 : FB = 4 := rfl
    have hb := h.big
    rw [agreeW_rdW hW (ha.mono (Nat.min_le_left lo K)) (by omega) (Nat.min_le_right lo K)]
    exact h.depth, h.big, h.sync.agreeW ha h.hiK, h.hiK⟩

theorem Kopf.agreeW {P : Programm D} {σ0 : World D} {L : Lay D} {f : D.Fn} {m m' : Runner.Mem} {fp : Runner.W} {Ks K lo : Nat} {rp cfp : Runner.W}
    {ρ0 : Env D (D.params f)} (hW : WIn L fp Ks K) (h : Kopf L f m fp K rp cfp ρ0 P σ0) (ha : AgreeW L fp lo K m m')
    (hl : FB + (contextWords (D.params f)) ≤ lo) : Kopf L f m' fp K rp cfp ρ0 P σ0 := by
  have hb := h.big
  have hFB3 : FB = 4 := rfl
  have ha' := ha.mono hl
  refine ⟨?_, ?_, envAt_agreeWIn hW h.env ha' (Nat.le_refl _) hb, hb, ?_⟩
  · rw [agreeW_rdW hW ha' (by omega) hb]; exact h.r0
  · rw [agreeW_rdW hW ha' (by omega) hb]; exact h.r1
  · intro c hc
    obtain ⟨width, value⟩ := h.entry c hc
    exact ⟨width, value.agreeW ha' hW.top (by have := hW.room; omega) (by omega) hb⟩

/-- `Pre.next` after a statement that changed the slots from `lo` on and the world. -/
theorem Pre.nextW {L : Lay D} {m m' : Runner.Mem} {pc fp : Runner.W} {Ks K d d' lo reserved : Nat} {a b : List II}
    {Γ : Ctx} {ρ : Env D Γ} (hW : WIn L fp Ks K) (h : PreS L m pc fp K d (a ++ b) ρ reserved) (ha : AgreeW L fp lo K m m')
    (hlo : frei Γ reserved ≤ lo) (hd : d ≤ d') (hK : lo ≤ K) : PreS L m' (pc + BitVec.ofNat 64 (16 * a.length)) fp K d' b ρ reserved :=
  have hf := codeFar_right (n := a.length) (k := b.length) (by simpa using h.far)
  ⟨Nat.le_trans h.ctx hd, h.small, frameOK_agreeW h.frame ha, codeAt_agreeWIn hW ha (codeAt_right h.code) hf, hf,
   envAt_agreeWIn hW h.env ha hlo hK, trivial, wstab_true _ _⟩

theorem envAt_ergEnv {m : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} :
    {e : Option Ty} → {v : ErgVal D e} → EnvAt L m fp ρ →
    ResultAt L m fp (frei Γ) e v → EnvAt L m fp (ergEnv e v ρ)
  | none, _, h, _ => h
  | some _, _, h, value => envAt_cons h value

theorem frei_ergCtx (Γ : Ctx) : (e : Option Ty) → frei (ErgCtx Γ e) ≤ frei Γ + resultWords e
  | none => by simp [ErgCtx]
  | some _ => by simp [ErgCtx, frei, resultWords, Nat.add_assoc]

theorem lowErg_span {reserved : Nat} {Λ : List (Res D)} {Γ : Ctx} : {e : Option Ty} → (x : ErgExpr D Γ Λ e) → (d : Nat) →
    (c : List II) → (top : Nat) → lowErg L x d reserved = some (c, top) → d + resultWords e ≤ top
  | _, .empty, d, c, top, h => by simp only [lowErg, Option.some.injEq, Prod.mk.injEq] at h; change d + 1 ≤ top; omega
  | _, .val e, d, c, top, h => by
    simp only [lowErg, Option.map_eq_some_iff] at h
    obtain ⟨⟨ce, te⟩, he, out⟩ := h
    cases out
    exact Nat.le_max_right _ _

theorem lowErg_top {reserved : Nat} {Λ : List (Res D)} {Γ : Ctx} {e : Option Ty}
    (x : ErgExpr D Γ Λ e) (d : Nat) (c : List II) (top : Nat)
    (lower : lowErg L x d reserved = some (c, top)) : d < top := by
  have span := lowErg_span x d c top lower
  have positive := resultWords_pos e
  omega

theorem lowErg_ok {reserved : Nat} {Λ : List (Res D)} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop} (σ₀ σ : World D)
    (hWL : ∀ m, W m → WeltAt m L σ) (hLay : LayIn L) {Γ : Ctx} :
    {e : Option Ty} → (x : ErgExpr D Γ Λ e) → (d : Nat) → (c : List II) → (top : Nat) →
    lowErg L x d reserved = some (c, top) → top ≤ K → ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ),
    Pre L m pc fp K d c ρ W reserved → ResultOk L m pc fp K d c e (evalErg σ₀ x σ ρ)
  | _, .empty, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowErg, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨m', run, changed, w, read, equal⟩ := const_ok hp (by decide) (by omega)
    subst w
    refine ⟨m', run, changed, ?_⟩
    intro i hi
    have zero : i = 0 := by simpa using hi
    subst i
    exact read
  | _, .val e, d, c, top, h, hK, m, pc, ρ, hp => by
    simp only [lowErg, Option.map_eq_some_iff] at h
    obtain ⟨⟨ce, te⟩, he, out⟩ := h
    cases out
    exact lowE_ok (reserved := reserved) σ₀ σ hWL hLay e d ce te he
      (Nat.le_trans (Nat.le_max_left _ _) hK) m pc ρ hp

theorem codeFar_tail {pc fp : Runner.W} {K : Nat} {a b : List II} (h : CodeFar pc (a ++ b).length fp K) :
    CodeFar (pc + BitVec.ofNat 64 (16 * a.length)) b.length fp K :=
  codeFar_right (by rw [List.length_append] at h; exact h)

theorem slot_one (fp : Runner.W) : slot fp (BitVec.ofNat 64 1) = fp + 8 := by simp [slot]

/-- `ret e`: the result, `ensures`, back or the stop (`retC`), in a frame of `K` slots. -/
theorem ret_ok0 {P : Programm D} {f : D.Fn} {fp : Runner.W} {K lo reserved : Nat} {rp cfp : Runner.W} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (contextWords (D.params f))) (hens : lowEns L (P.ensures f) (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {Γ : Ctx} {Λ : List (Res D)} (e : ErgExpr D Γ Λ (vertragVon D f).erg) {ce : List II} {te : Nat}
    (he : lowErg L e (frei Γ reserved) reserved = some (ce, te)) (hK : max te (max tens (retTop lo (D.erg f) (D.gruende f))) ≤ K)
    (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) (ce ++ retC lo (frei Γ reserved) cens (D.erg f) (D.gruende f)) ρ reserved) (hlo : lo ≤ frei Γ reserved)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) (hl : LayIn L) (hwl : fp.toNat + 8 * K ≤ L.lo) :
    RetZ0 L P f σ0 ρ0 fp K rp cfp ⟨pc, fp⟩ m (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
    have hnr := resultWords_pos (D.erg f)
    have harea := resultWords_le_returnWords (D.erg f) (D.gruende f)
    have hFB3 : FB = 4 := rfl
    have htop := lowErg_top (reserved := reserved) e _ _ _ he
    have hspan := lowErg_span (reserved := reserved) e _ _ _ he
    have hsm := hp.small
    have hroom := hp.frame.room
    simp only [retTop] at hK
    -- the result into slot `frei Γ reserved`, then into slot `lo`
    have hpw := PreS.welt hp.left (Nat.le_refl K) hWa hl hwl
    obtain ⟨m1, s1, a1, value1⟩ := lowErg_ok (reserved := reserved) (fp := fp) (K := K) (σ.lese Λ e.orte) (σ.lese Λ e.orte)
      (fun _ h => h) hl e _ ce te he (by omega) m pc ρ hpw
    have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1.mono (Nat.zero_le _))
    have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
    have hq : PreS L m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (frei Γ reserved)
        (copyWords (resultWords (D.erg f)) lo (frei Γ reserved) ++ (cens ++ ([ci 19 ((lo + returnWords (D.erg f) (D.gruende f) : Nat) : Int) 48 0] ++
          ([ci 2 2 lo 0] ++ ([ci 21 0 0 0] ++ stopC 102 (lo + returnWords (D.erg f) (D.gruende f))))))) ρ reserved := by
      simpa [retC, List.append_assoc] using hp1
    have hF1 := hq.frame
    obtain ⟨m2, s2, a2exact, value2⟩ := copyResult_run (L := L) hF1 hsm
      (by omega) (by simpa only [resultWords_vertragVon] using Nat.le_trans hspan (by omega : te ≤ K))
      (Or.inl hlo) (codeAt_left hq.code)
      (by simpa only [copyWords_length] using hq.left.far) value1
    have a2 : Agree fp lo K m1 m2 := Agree.widen a2exact (by omega)
    have hF2 := hF1.agree a2
    have hf2 := codeFar_tail (a := copyWords (resultWords (D.erg f)) lo (frei Γ reserved)) hq.far
    have hc2 := (codeAt_right hq.code).agree a2 hf2
    simp only [copyWords_length] at hf2 hc2
    have hk2 := hk.agree ((a1.mono hlo).trans a2) hp.frame (by omega)
    have hWa2 : WeltAt m2 L σ := weltAt_stab hl hwl m1 m2 hWa1 (a2.mono (Nat.zero_le _))
    -- `ensures` over the result and the parameters, into slot `lo + returnWords (D.erg f) (D.gruende f)`
    have hpe : PreS L m2 _ fp K (lo + returnWords (D.erg f) (D.gruende f)) cens (ergEnv (D.erg f) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ0) :=
      ⟨Nat.le_trans (frei_ergCtx _ _) (by simp only [frei]; omega), hsm, hF2, codeAt_left hc2,
       codeFar_left (by rw [← List.length_append]; exact hf2),
       envAt_ergEnv hk2.env (by change ResultAt L m2 fp (FB + contextWords (D.params f)) _ _; rw [← hlo0]; exact value2), trivial, wstab_true _ _⟩
    obtain ⟨m3, s3, a3, b, hb, hbe⟩ := lowEns_ok (fp := fp) (K := K) σ0
      ((σ.lese Λ e.orte).lese (vertragVon D f).ende (P.ensures f).orte) (fun _ h => h) hl (P.ensures f) (lo + returnWords (D.erg f) (D.gruende f)) cens
      tens hens (by omega) m2 _ _ (PreS.welt hpe (Nat.le_refl K) hWa2 hl hwl) hk2.entry |>.word trivial
    have hF3 := hF2.agree a3
    have hf3 := codeFar_tail (a := cens) hf2
    have hc3 := (codeAt_right hc2).agree a3 hf3
    have hbrz := hc3 0 (by simp)
    simp only [ci, List.getElem_cons_zero, List.cons_append, Nat.mul_zero, BitVec.add_zero] at hbrz
    have hd1 : sx (II.f ((lo + returnWords (D.erg f) (D.gruende f) : Nat) : Int)) = BitVec.ofNat 64 (lo + returnWords (D.erg f) (D.gruende f)) := sx_nat (by omega)
    simp only [Enc] at hbe
    simp only [RetZ0]
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
      have hcS : CodeAt m3 (_ + BitVec.ofNat 64 48) (stopC 102 (lo + returnWords (D.erg f) (D.gruende f))) :=
        codeAt_right (a := [ci 19 ((lo + returnWords (D.erg f) (D.gruende f) : Nat) : Int) 48 0, ci 2 2 lo 0, ci 21 0 0 0]) hc3
      have hfS : CodeFar (_ + BitVec.ofNat 64 48) 3 fp K :=
        codeFar_tail (a := [ci 19 ((lo + returnWords (D.erg f) (D.gruende f) : Nat) : Int) 48 0, ci 2 2 lo 0, ci 21 0 0 0]) hf3
      exact Stops.prefix (s1.trans (s2.trans (s3.trans sb))) (stop_ok hcS hfS hF3 (by omega) hsm (by decide))
    · next htrue =>
      -- `ensures` holds: the result into slot 2, `ret`
      have hb1 : b = 1 := by
        split at hbe
        · exact hbe
        · next hn => simp only [Bool.not_eq_true] at hn; exact absurd hn htrue
      have rb := run_brz_ne (t := ⟨_, fp⟩) hbrz (by rw [hd1]; exact hb) (by rw [hb1]; decide)
      have sb := star_ins (fp := fp) (m' := m3) (codeAt_left (a := [ci 19 ((lo + returnWords (D.erg f) (D.gruende f) : Nat) : Int) 48 0]) hc3)
        (by simp [ci]) (by simp only [ci]; exact rb)
      have hc4 := codeAt_right (a := [ci 19 ((lo + returnWords (D.erg f) (D.gruende f) : Nat) : Int) 48 0]) hc3
      have value3 := value2.agree a3 hF2 (by omega) (by omega)
      obtain ⟨w, hw3⟩ := ResultAt.first value3
      have s5 := mov_to (codeAt_left (a := [ci 2 2 lo 0]) hc4) hF3 (j := 2) (s := lo) (by omega) (by omega) hsm hw3
      let m4 := write m3 (slot fp (BitVec.ofNat 64 2)) 8 w.toNat
      have a4 : Agree fp 2 K m3 m4 := agree_write hF3.room (Nat.le_refl _) (by omega) _
      have hf4 := codeFar_tail (a := [ci 2 2 lo 0]) (codeFar_tail (a := [ci 19 ((lo + returnWords (D.erg f) (D.gruende f) : Nat) : Int) 48 0]) hf3)
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
        (a1.mono (by omega)).trans ((a2.mono (by omega)).trans ((a3.mono (by omega)).trans a4)), ?_, ?_, ?_⟩
      · rw [← hlo0]
        exact value3.write_slot hF3.room (by omega) (by omega) (Or.inl (by omega)) w
      · change m4.rd64 (slot fp (BitVec.ofNat 64 2)) = m4.rd64 (slot fp (BitVec.ofNat 64 (FB + contextWords (D.params f))))
        rw [← hlo0]
        dsimp only [m4]
        rw [rd_same hF3 (by omega) w,
          rd_other (a := 2) (b := lo) hF3.room (by omega) (by omega) (by omega), hw3]
      · change m4.rd64 (slot fp (BitVec.ofNat 64 (FB + (contextWords (D.params f)) + returnWords (D.erg f) (D.gruende f)))) = some 1
        rw [← hlo0]
        dsimp only [m4]
        rw [rd_other hF3.room (by omega) (by omega) (by omega)]
        simpa only [hb1] using hb

/-- `ret e` in the frame below the world: its code writes only slots below `Ks`, so the world stays. -/
theorem ret_ok {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo reserved : Nat} {rp cfp : Runner.W} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (contextWords (D.params f))) (hens : lowEns L (P.ensures f) (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {Γ : Ctx} {Λ : List (Res D)} (e : ErgExpr D Γ Λ (vertragVon D f).erg) {ce : List II} {te : Nat}
    (he : lowErg L e (frei Γ reserved) reserved = some (ce, te)) (hK : max te (max tens (retTop lo (D.erg f) (D.gruende f))) ≤ Ks)
    (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) (ce ++ retC lo (frei Γ reserved) cens (D.erg f) (D.gruende f)) ρ reserved) (hlo : lo ≤ frei Γ reserved)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) :
    RetZ L P f σ0 ρ0 fp K rp cfp ⟨pc, fp⟩ m (σ.lese Λ e.orte)
      (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) := by
  have hks := hW.ks
  have hts := lowErg_top (reserved := reserved) e _ _ _ he
  have hpS : PreS L m pc fp Ks (frei Γ reserved) (ce ++ retC lo (frei Γ reserved) cens (D.erg f) (D.gruende f)) ρ reserved :=
    ⟨hp.ctx, by have := hp.small; omega, frameOK_sub hp.frame hks, hp.code, codeFar_sub2 hp.far hks, hp.env,
     trivial, wstab_true _ _⟩
  have hkS : Kopf L f m fp Ks rp cfp ρ0 P σ0 := ⟨hk.r0, hk.r1, hk.env, by simp only [retTop] at hK; omega, hk.entry⟩
  have h0 := ret_ok0 (σ0 := σ0) hlo0 hens e he hK m pc σ ρ hpS hlo hkS hWa hW.lay hW.lo
  simp only [RetZ0] at h0
  simp only [RetZ]
  split
  · next hf => rw [if_pos hf] at h0; exact h0
  · next hf =>
    rw [if_neg hf] at h0
    obtain ⟨m', s, a, hw⟩ := h0
    exact ⟨m', s, agreeW_of (Agree.widen a hks), hw,
      weltAt_stab hW.lay (by have := hW.lo; omega) m m' hWa (a.mono (Nat.zero_le _))⟩

/-- Reason returns bypass the normal postcondition and preserve the world and frame header. -/
theorem retWhy_ok {reserved : Nat} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {ρ0 : Env D (D.params f)} {Γ : Ctx} {m : Runner.Mem} {pc : Runner.W}
    {σ : World D} {ρ : Env D Γ} (r : Fin (D.gruende f))
    (hlo0 : lo = FB + contextWords (D.params f))
    (hK : retTop lo (D.erg f) (D.gruende f) ≤ Ks)
    (hp : PreS L m pc fp K (frei Γ reserved) (retWhyC lo r.val (D.erg f) (D.gruende f)) ρ reserved)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) :
    RetWhy L f fp K rp cfp ⟨pc, fp⟩ m σ r := by
  have hFB : FB = 4 := rfl
  have hks := hW.ks
  have area := reasonWords_le_returnWords (D.erg f) (D.gruende f)
  have positive := valueWords_pos (.why (D.gruende f))
  have small := hp.small
  have topBound : lo + returnWords (D.erg f) (D.gruende f) + 8 ≤ Ks := hK
  have frame := frameOK_sub hp.frame hks
  have room := frame.room
  let words := encodeWords L (.why (D.gruende f)) r
  let material := constWords words lo
  have width : words.length = valueWords (.why (D.gruende f)) := encodeWords_length L _ _
  have bound := constWords_bound words lo
  have pre : PreS L m pc fp Ks lo
      (material.1 ++ [ci 2 2 lo 0, ci 1 (lo + returnWords (D.erg f) (D.gruende f)) 0 0, ci 21 0 0 0]) ρ0 :=
    ⟨by simpa [frei, hlo0], by omega, frame, hp.code, codeFar_sub2 hp.far hks,
      hk.env, trivial, wstab_true _ _⟩
  obtain ⟨m1, s1, a1, value1⟩ := constValue_ok (L := L) (τ := .why (D.gruende f)) (c := material.1) (top := material.2) r trivial rfl
    (by change (constWords words lo).2 ≤ Ks; omega) pre.left
  have frame1 := frame.agree a1
  have far1 := codeFar_tail (a := material.1) pre.far
  have code1 := (codeAt_right pre.code).agree a1 far1
  let w := words[0]'(by omega)
  have read1 : m1.rd64 (slot fp (BitVec.ofNat 64 lo)) = some w := value1.2 0 (by change 0 < words.length; omega)
  have s2 := mov_to (codeAt_left (a := [ci 2 2 lo 0]) code1) frame1
    (j := 2) (s := lo) (by unfold retTop at hK; omega) (by unfold retTop at hK; omega)
    (by omega) read1
  let m2 := write m1 (slot fp (BitVec.ofNat 64 2)) 8 w.toNat
  have a2 : Agree fp 2 Ks m1 m2 := agree_write room (Nat.le_refl _) (by unfold retTop at hK; omega) _
  have frame2 := frame1.agree a2
  have far2 := codeFar_tail (a := [ci 2 2 lo 0]) far1
  have code2 := (codeAt_right (a := [ci 2 2 lo 0]) code1).agree a2 far2
  have value2 := ValueAt.write_slot (j := 2) value1 frame1.room (by unfold retTop at hK; omega)
    (by unfold retTop at hK; omega) (Or.inl (by omega)) w
  have s3 := const_to (j := lo + returnWords (D.erg f) (D.gruende f)) (k := 0)
    (codeAt_left (a := [ci 1 (lo + returnWords (D.erg f) (D.gruende f)) 0 0]) code2)
    frame2 (by unfold retTop at hK; omega) (by omega) (by decide)
  let m3 := write m2 (slot fp (BitVec.ofNat 64 (lo + returnWords (D.erg f) (D.gruende f)))) 8 0
  have a3 : Agree fp 2 Ks m2 m3 := agree_write room (by omega) (by unfold retTop at hK; omega) _
  have far3 := codeFar_tail (a := [ci 1 (lo + returnWords (D.erg f) (D.gruende f)) 0 0]) far2
  have code3 := (codeAt_right (a := [ci 1 (lo + returnWords (D.erg f) (D.gruende f)) 0 0]) code2).agree a3 far3
  have ret := code3 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at ret
  have kept := hk.agree (Agree.widen a1 hks) hp.frame (by omega)
  have head0 : m3.rd64 fp = some rp := by
    rw [← slot_zero fp]
    dsimp only [m3, m2]
    rw [rd_other frame2.room (by unfold retTop at hK; omega) (by omega) (by omega),
      rd_other frame1.room (by omega) (by omega) (by omega)]
    exact kept.r0
  have head1 : m3.rd64 (fp + 8) = some cfp := by
    rw [← slot_one fp]
    dsimp only [m3, m2]
    rw [rd_other frame2.room (by unfold retTop at hK; omega) (by omega) (by omega),
      rd_other frame1.room (by omega) (by omega) (by omega)]
    exact kept.r1
  have sr := Star.one (run_step (t := ⟨_, fp⟩) ret (by decide) (run_ret (t := ⟨_, fp⟩) head0 head1))
  have changed := (a1.mono (by omega : 2 ≤ lo)).trans (a2.trans a3)
  refine ⟨m3, s1.trans (s2.trans (s3.trans sr)), agreeW_of (Agree.widen changed hks), ?_, ?_, ?_,
    weltAt_stab hW.lay hW.lo m m3 hWa (changed.mono (Nat.zero_le _))⟩
  · rw [← hlo0]
    exact ValueAt.write_slot (j := lo + returnWords (D.erg f) (D.gruende f)) value2 frame2.room (by unfold retTop at hK; omega)
      (by unfold retTop at hK; omega) (Or.inr (by omega)) 0
  · change m3.rd64 (slot fp (BitVec.ofNat 64 2)) = m3.rd64 (slot fp (BitVec.ofNat 64 (FB + contextWords (D.params f))))
    rw [← hlo0]
    dsimp only [m3]
    rw [rd_other (a := lo + returnWords (D.erg f) (D.gruende f)) (b := 2)
        frame2.room (by omega) (by omega) (by omega),
      rd_other (a := lo + returnWords (D.erg f) (D.gruende f)) (b := lo)
        frame2.room (by omega) (by omega) (by omega)]
    dsimp only [m2]
    rw [rd_same frame1 (by omega) w,
      rd_other (a := 2) (b := lo) frame1.room (by omega) (by omega) (by omega), read1]
  · change m3.rd64 (slot fp (BitVec.ofNat 64 (FB + contextWords (D.params f) + returnWords (D.erg f) (D.gruende f)))) = some 0
    rw [← hlo0]
    exact rd_same frame2 (by unfold retTop at hK; omega) 0

end Gabbro.Stage0.Senke
