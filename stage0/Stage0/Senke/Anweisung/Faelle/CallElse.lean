/-
  Subject: A shared call-result binding and status branch for blocks and end blocks.
-/
import Stage0.Senke.Anweisung.Faelle.Kontext
import Stage0.Senke.Anweisung.SchleifeTeile
import Stage0.Senke.Anweisung.Fnptr

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The continuation starts after the binding and branch, or after the skipped success arm. -/
def callBranchPC (pc : Runner.W) (cc cr : List II) (ok : Bool) : Runner.W :=
  pc + BitVec.ofNat 64 (16 * (cc.length + if ok then 2 else cr.length + 3))

/-- Bind either encoded answer in the same variable slot, then read the disjoint status slot.
    This is independent of call semantics and of the continuation's kind. -/
theorem callBranch_ok {Γ : Ctx} {τ : Ty} {np : Nat} {cc cr ce : List II}
    {fp pc : Runner.W} {K Ks : Nat} {m m1 : Runner.Mem} {ρ : Env D Γ} {σ : World D}
    {w : Runner.W} {v : Wert D τ} {ok : Bool}
    (hp : PreS L m pc fp K (frei Γ) (elseC (frei Γ + FB + np + 1) (frei Γ) cc cr ce) ρ)
    (hs : 16 * (elseC (frei Γ + FB + np + 1) (frei Γ) cc cr ce).length < 2 ^ 31)
    (hW : WIn L fp Ks K) (ht : frei Γ + FB + np + 2 ≤ Ks)
    (s1 : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * cc.length), fp⟩ m1)
    (a1 : AgreeW L fp (frei Γ) K m m1)
    (hw : m1.rd64 (slot fp (BitVec.ofNat 64 (frei Γ + 2))) = some w)
    (hen : Enc L τ v w) (flag : ReturnFlag m1 (slot fp (BitVec.ofNat 64 (frei Γ))) np ok)
    (hWa : WeltAt m1 L σ) :
    ∃ m2, Star ⟨pc, fp⟩ m ⟨callBranchPC pc cc cr ok, fp⟩ m2 ∧
      AgreeW L fp (frei Γ) K m m2 ∧
      PreS L m2 (callBranchPC pc cc cr ok) fp K (frei (τ :: Γ)) (if ok then cr else ce) (.cons v ρ) ∧
      WeltAt m2 L σ := by
  have hFB3 : FB = 4 := rfl
  have hks := hW.ks
  have hq : PreS L m pc fp K (frei Γ)
      (cc ++ ([ci 2 (frei Γ) (frei Γ + 2) 0] ++
        ([ci 19 (frei Γ + FB + np + 1) (16 * (cr.length + 2)) 0] ++
          (cr ++ ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce))))) ρ := by
    simpa only [elseC, List.append_assoc, Int.natCast_add, Int.ofNat_one] using hp
  have hp1 := hq.nextW hW a1 (by have := hp.ctx; omega) (Nat.le_refl _) (by omega)
  have s2 := mov_to hp1.left.code hp1.frame (j := frei Γ) (s := frei Γ + 2)
    (by omega) (by omega) hp.small hw
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (frei Γ))) 8 w.toNat
  have a2s : Agree fp (frei Γ) Ks m1 m2 :=
    agree_write (frameOK_sub hp1.frame hks).room (Nat.le_refl _) (by omega) _
  have a2 := Agree.widen a2s hks
  have hp2 := hp1.next a2 (d' := frei Γ + 1) (by omega) (by omega)
  have hw2 : WeltAt m2 L σ := weltAt_stab hW.lay (by have := hW.lo; omega) m1 m2 hWa
    (a2s.mono (Nat.zero_le _))
  have en : EnvAt L m2 fp (.cons v ρ) := envAt_cons hp2.env (rd_same hp1.frame (by omega) w) hen
  have hf : m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ + FB + np + 1))) = some (if ok then 1 else 0) := by
    dsimp only [m2]
    rw [rd_other hp1.frame.room (by omega) (by omega) (by omega)]
    simpa only [ReturnFlag, slot_slot, Nat.add_assoc] using flag
  have hsmall := hp.small
  have hlen : 16 * (cr.length + 2) < 2 ^ 31 := by
    simp only [elseC, List.length_append, List.length_singleton] at hs
    omega
  cases ok with
  | true =>
    have sb := brz_stay hp2.left.code (j := frei Γ + FB + np + 1) (by omega) hp.small hf (by decide)
    have hp3 := hp2.next (a := [ci 19 (frei Γ + FB + np + 1) (16 * (cr.length + 2)) 0])
      (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    have heq : pc + BitVec.ofNat 64 (16 * cc.length) + BitVec.ofNat 64 (16 * 1) +
        BitVec.ofNat 64 (16 * 1) = callBranchPC pc cc cr true := by
      simp only [callBranchPC, Bool.false_eq_true, ↓reduceIte, addr_norm]
      congr 2 <;> omega
    refine ⟨m2, s1.trans (s2.trans (star_cast sb rfl (by simp only [List.length_singleton]; rw [heq]))), a1.trans (agreeW_of a2), ?_, hw2⟩
    change PreS L m2 (callBranchPC pc cc cr true) fp K (frei (τ :: Γ)) cr (.cons v ρ)
    rw [← heq]
    exact ⟨by simp only [frei, List.length_cons]; omega, hp3.small, hp3.frame, hp3.left.code, hp3.left.far,
      en, trivial, wstab_true _ _⟩
  | false =>
    have sb := brz_go hp2.left.code (j := frei Γ + FB + np + 1) (by omega) hp.small
      (lit32_nat hlen) hf
    have hp3 := ((hp2.next (a := [ci 19 (frei Γ + FB + np + 1) (16 * (cr.length + 2)) 0])
      (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)).next (a := cr)
      (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)).next
      (a := [ci 18 (16 * (ce.length + 1)) 0 0]) (Agree.refl _ _ _ _) (Nat.le_refl _) (by omega)
    have heq : pc + BitVec.ofNat 64 (16 * cc.length) + BitVec.ofNat 64 (16 * 1) +
        BitVec.ofNat 64 (16 * 1) + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofNat 64 (16 * 1) =
        callBranchPC pc cc cr false := by
      simp only [callBranchPC, Bool.false_eq_true, ↓reduceIte, addr_norm]
      congr 2 <;> omega
    refine ⟨m2, s1.trans (s2.trans (star_cast sb rfl ?_)), a1.trans (agreeW_of a2), ?_, hw2⟩
    · simp only [T.mk.injEq, and_true, callBranchPC, Bool.false_eq_true, ↓reduceIte]
      simp only [List.length_singleton]
      rw [show (16 * ((cr.length : Int) + 2)) = ((16 * (cr.length + 2) : Nat) : Int) by omega,
        BitVec.ofInt_natCast]
      simp only [addr_norm]
      congr 2 <;> omega
    · change PreS L m2 (callBranchPC pc cc cr false) fp K (frei (τ :: Γ)) ce (.cons v ρ)
      rw [← heq]
      exact ⟨by simp only [frei, List.length_cons]; omega, hp3.small, hp3.frame, hp3.code, hp3.far,
        en, trivial, wstab_true _ _⟩

/-- A call followed by the common binder reaches precisely the continuation selected by G. -/
theorem callElse_ok {A : D.Fn → Nat} {C : D.Fn → List II}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {dv : Runner.W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn} {τ : Ty}
    (hA : A g < 2 ^ 31) (args : Args D Γ Λ (D.params g)) (he : D.erg g = some τ)
    {ca cr ce : List II} {ta : Nat} {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem}
    {ρ : Env D Γ} (σ : World D)
    (hca : lowA L args (frei Γ + FB) = some (ca, ta))
    (ht : max (callTop g (frei Γ) ta) (frei Γ + FB + (D.params g).length + 2) + cap ≤ Ks)
    (hp : PreS L m pc fp K (frei Γ)
      (elseC (frei Γ + FB + (D.params g).length + 1) (frei Γ) (callC A g (frei Γ) ca) cr ce) ρ)
    (hs : 16 * (elseC (frei Γ + FB + (D.params g).length + 1) (frei Γ) (callC A g (frei Γ) ca) cr ce).length < 2 ^ 31)
    (hu : Umf L A C dv m fp Ks K) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) :
    (∃ σ' v m2, R g σ (evalArgs σ args σ ρ) = .ok σ' v ∧
      Star ⟨pc, fp⟩ m ⟨callBranchPC pc (callC A g (frei Γ) ca) cr true, fp⟩ m2 ∧
      AgreeW L fp (frei Γ) K m m2 ∧
      PreS L m2 (callBranchPC pc (callC A g (frei Γ) ca) cr true) fp K (frei (τ :: Γ)) cr (.cons (ergWert he v) ρ) ∧ WeltAt m2 L σ') ∨
    (∃ σ' r m2, R g σ (evalArgs σ args σ ρ) = .why σ' r ∧
      Star ⟨pc, fp⟩ m ⟨callBranchPC pc (callC A g (frei Γ) ca) cr false, fp⟩ m2 ∧
      AgreeW L fp (frei Γ) K m m2 ∧
      PreS L m2 (callBranchPC pc (callC A g (frei Γ) ca) cr false) fp K (frei (.why (D.gruende g) :: Γ)) ce (Env.cons (τ := .why (D.gruende g)) r ρ) ∧ WeltAt m2 L σ') ∨
    (∃ e, R g σ (evalArgs σ args σ ρ) = .logik e ∧ Stops ⟨pc, fp⟩ m (logikCode e)) ∨
    (∃ e, R g σ (evalArgs σ args σ ρ) = .hardware e ∧ Stops ⟨pc, fp⟩ m (hwCode e)) := by
  have hpc : PreS L m pc fp K (frei Γ) (callC A g (frei Γ) ca ++
      ([ci 2 (frei Γ) (frei Γ + 2) 0] ++ [ci 19 (frei Γ + FB + (D.params g).length + 1) (16 * (cr.length + 2)) 0] ++
       cr ++ [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce)) ρ := by
    simpa only [elseC, List.append_assoc, Int.natCast_add, Int.ofNat_one] using hp
  have hc := callC_ok hS hA args σ σ hca (by omega) hpc.left hu hW hWa
  cases hr : R g σ (evalArgs σ args σ ρ) with
  | ok σ' v =>
    rw [hr] at hc
    obtain ⟨m1, sx, ax, ⟨w, hw, hen, flag⟩, hw1⟩ := hc
    obtain ⟨m2, sx2, ax2, hp2, hw2⟩ := callBranch_ok hp hs hW (by omega) sx ax hw (encErg_wert he hen) flag hw1
    exact .inl ⟨σ', v, m2, rfl, sx2, ax2, hp2, hw2⟩
  | why σ' r =>
    rw [hr] at hc
    obtain ⟨m1, sx, ax, hw, flag, hw1⟩ := hc
    obtain ⟨m2, sx2, ax2, hp2, hw2⟩ := callBranch_ok (τ := .why (D.gruende g)) (v := r) hp hs hW (by omega) sx ax hw rfl flag hw1
    exact .inr (.inl ⟨σ', r, m2, rfl, sx2, ax2, hp2, hw2⟩)
  | logik e => rw [hr] at hc; exact .inr (.inr (.inl ⟨e, rfl, hc⟩))
  | hardware e => rw [hr] at hc; exact .inr (.inr (.inr ⟨e, rfl, hc⟩))

/-- A normal block continuation skips the reason handler at its fallthrough. -/
theorem callElse_jump {Γ : Ctx} {flag : Nat} {cc cr ce : List II}
    {fp pc : Runner.W} {K Ks lo : Nat} {m m' : Runner.Mem} {ρ : Env D Γ}
    (hp : PreS L m pc fp K (frei Γ) (elseC flag (frei Γ) cc cr ce) ρ)
    (hs : 16 * (elseC flag (frei Γ) cc cr ce).length < 2 ^ 31)
    (hW : WIn L fp Ks K) (ha : AgreeW L fp lo K m m') :
    Star ⟨callBranchPC pc cc cr true + BitVec.ofNat 64 (16 * cr.length), fp⟩ m'
      ⟨pc + BitVec.ofNat 64 (16 * (elseC flag (frei Γ) cc cr ce).length), fp⟩ m' := by
  let before := cc ++ [ci 2 (frei Γ) (frei Γ + 2) 0] ++
    [ci 19 flag (16 * (cr.length + 2)) 0] ++ cr
  have hq : PreS L m pc fp K (frei Γ)
      (before ++ ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce)) ρ := by
    simpa only [before, elseC, List.append_assoc, Int.natCast_add, Int.ofNat_one] using hp
  have hf := codeFar_right (n := before.length) (k := ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length)
    (by simpa only [List.length_append] using hq.far)
  have hc := codeAt_agreeWIn hW ha (codeAt_right hq.code) hf
  have hj : lit32 (16 * ((ce.length : Int) + 1)) = true := by
    apply lit_ok (by omega)
    simp only [elseC, List.length_append, List.length_singleton] at hs
    omega
  have sj := jmp_go (fp := fp) (codeAt_left hc) hj
  refine star_cast sj ?_ ?_
  · simp only [T.mk.injEq, and_true, before, callBranchPC, ↓reduceIte,
      List.length_append, List.length_singleton, addr_norm]
    exact congrArg (fun n : Nat => pc + BitVec.ofNat 64 n) (by omega)
  · simp only [T.mk.injEq, and_true, before, elseC, List.length_append, List.length_singleton]
    rw [show 16 * ((ce.length : Int) + 1) = ((16 * (ce.length + 1) : Nat) : Int) by omega,
      BitVec.ofInt_natCast, addr_norm]
    exact congrArg (fun n : Nat => pc + BitVec.ofNat 64 n) (by omega)

theorem blockCallElse_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {τ : Ty} {callee : D.Fn} {args : Args D Γ Λ (D.params callee)} {he : D.erg callee = some τ} {proof0 : _} {proof1 : _} {err : Endblock D (vertragVon D f) l (.why (D.gruende callee) :: Γ) (nach D callee Λ)} {rest : Block D (vertragVon D f) l (τ :: Γ) (nach D callee Λ) Λ'} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err) →
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .bindCallElse callee args he proof0 proof1 err rest) := by
  intro ihErr ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ca, ta⟩, hca, ⟨ce, te⟩, hce, ⟨cr, tr⟩, hcr, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [elseTop] at hK
  have hFB3 : FB = 4 := rfl
  have hpr' : ∀ j ∈ pr, j < frei (τ :: Γ) := by
    intro j hj; have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega
  have hprE : ∀ j ∈ pr, j < frei (.why (D.gruende callee) :: Γ) := by
    intro j hj; have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega
  simp only [execBlock]
  rcases callElse_ok hS (hA callee) args he (σ.lese Λ args.orte) hca (by omega) hp hs hu hW hWa with
    ⟨σ', v, m2, hR, st, a, hp2, hw2⟩ | ⟨σ', r, m2, hR, st, a, hp2, hw2⟩ |
    ⟨e, hR, st⟩ | ⟨e, hR, st⟩
  · rw [hR]
    have ih := ihRest (ex := exPlus ex (ce.length + 1)) cr tr hcr (by omega)
      (by simp only [elseC, List.length_append, List.length_singleton] at hs; omega) hW m2 _ σ' _ hp2 hlo
      (by simp only [frei, List.length_cons] at hlo2 ⊢; omega)
      (hu.agreeW hW a (by omega)) (hk.agreeW hW a (by omega)) hw2 hpr'
    refine Sim.prefix hlo st (a.mono hlo2) (keeps_of_agreeW hW a hpr (by have := hW.ks; omega))
      (Sim.cont (Sim.schrumpf ih) (fun m3 a3 => callElse_jump hp hs hW ((a.mono hlo2).trans a3)) ?_ ?_)
    · simp only [callBranchPC, exPlus, elseC, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
    · simp only [callBranchPC, exPlus, elseC, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
  · rw [hR]
    have ih := ihErr (ex := ex) ce te hce (by omega)
      (by simp only [elseC, List.length_append, List.length_singleton] at hs; omega) hW m2 _ σ' _ hp2
      (by simp only [frei, List.length_cons] at hlo2 ⊢; omega)
      (hu.agreeW hW a (by omega)) (hk.agreeW hW a (by omega)) hw2 hprE
    refine Sim.prefix hlo st (a.mono hlo2) (keeps_of_agreeW hW a hpr (by have := hW.ks; omega))
      (Ret.zuAusgang (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_))
    · simp only [callBranchPC, elseC, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
    · simp only [callBranchPC, elseC, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
  · rw [hR]; exact st
  · rw [hR]; exact st

theorem endCallElse_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowEns L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)} {he : D.erg g = some τ} {proof0 : _} {proof1 : _} {err : Endblock D (vertragVon D f) l (.why (D.gruende g) :: Γ) (nach D g Λ)} {rest : Endblock D (vertragVon D f) l (τ :: Γ) (nach D g Λ)} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err) →
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Endblock D (vertragVon D f) l Γ Λ from .bindCallElse g args he proof0 proof1 err rest) := by
  intro ihErr ihRest c top h hK hs hW m pc σ ρ hp hlo2 hu hk hWa hpr
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ca, ta⟩, hca, ⟨ce, te⟩, hce, ⟨cr, tr⟩, hcr, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [elseTop] at hK
  have hFB3 : FB = 4 := rfl
  have hlo : FB ≤ lo := by omega
  have hpr' : ∀ j ∈ pr, j < frei (τ :: Γ) := by
    intro j hj; have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega
  have hprE : ∀ j ∈ pr, j < frei (.why (D.gruende g) :: Γ) := by
    intro j hj; have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega
  simp only [execEnd]
  rcases callElse_ok hS (hA g) args he (σ.lese Λ args.orte) hca (by omega) hp hs hu hW hWa with
    ⟨σ', v, m2, hR, st, a, hp2, hw2⟩ | ⟨σ', r, m2, hR, st, a, hp2, hw2⟩ |
    ⟨e, hR, st⟩ | ⟨e, hR, st⟩
  · rw [hR]
    have ih := ihRest (ex := exPlus ex (ce.length + 1)) cr tr hcr (by omega)
      (by simp only [elseC, List.length_append, List.length_singleton] at hs; omega) hW m2 _ σ' _ hp2
      (by simp only [frei, List.length_cons] at hlo2 ⊢; omega)
      (hu.agreeW hW a (by omega)) (hk.agreeW hW a (by omega)) hw2 hpr'
    refine Ret.prefix (by omega) st (a.mono hlo2) (keeps_of_agreeW hW a hpr (by have := hW.ks; omega))
      (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_)
    · simp only [callBranchPC, exPlus, elseC, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
    · simp only [callBranchPC, exPlus, elseC, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
  · rw [hR]
    have ih := ihErr (ex := ex) ce te hce (by omega)
      (by simp only [elseC, List.length_append, List.length_singleton] at hs; omega) hW m2 _ σ' _ hp2
      (by simp only [frei, List.length_cons] at hlo2 ⊢; omega)
      (hu.agreeW hW a (by omega)) (hk.agreeW hW a (by omega)) hw2 hprE
    refine Ret.prefix (by omega) st (a.mono hlo2) (keeps_of_agreeW hW a hpr (by have := hW.ks; omega))
      (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_)
    · simp only [callBranchPC, elseC, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
    · simp only [callBranchPC, elseC, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
  · rw [hR]; exact st
  · rw [hR]; exact st

end Gabbro.Stage0.Senke
