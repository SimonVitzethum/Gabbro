/-
  File:      stage0/Stage0/Senke/Anweisung/Satz.lean
  Subject:   `ir_sim` for statements and blocks, calls included: where machine G ends a block normally (`ok`), the
             lowered code runs to its end and leaves the new environment in the frame, changing no slot below
             `lo`; where G ends in a logic outcome, the code stops with its `exit_group` code. G answers nothing
             else for a lowered block (`Sim`).
-/
import Stage0.Senke.Anweisung.Simulation
import Stage0.Senke.Anweisung.Schreiben
import Stage0.Senke.Anweisung.Schleife
import Stage0.Senke.Anweisung.TorLauf
import Stage0.Senke.Sperre.Satz
import Stage0.Senke.Anweisung.Atomar
import Stage0.Senke.Anweisung.Wahl
import Stage0.Senke.Anweisung.Option
import Stage0.Senke.Anweisung.Tag
import Stage0.Senke.Anweisung.Bytes.Shift

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {V : Vertrag D}

theorem encErg_wert {e : Option Ty} {τ : Ty} (he : e = some τ) {v : ErgVal D e} {w : Runner.W}
    (h : EncErg e v w) : Enc τ (ergWert he v) w := by
  subst he; exact h

mutual
theorem lowS_ok {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int} :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (s : Stmt D (vertragVon D f) l Γ Λ Λ') → (c : List II) → (top : Nat) →
    lowS A L lo (cens, tens) pr ex s = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS m pc fp K (frei Γ) c ρ →
    FB ≤ lo → lo ≤ frei Γ → Umf L A C dv m fp Ks K → Kopf f m fp K rp cfp ρ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ) →
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R s σ ρ)
  | _, Γ, Λ, _, .assignVar x e, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr => by
    simp only [lowS] at h
    split at h
    · next hlx =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ce, te⟩, he, hc⟩ := h
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [execStmt, Sim]
      have hks := hW.ks
      have htop := lowE_top e _ _ _ he
      have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
      obtain ⟨m1, s1, a1s, w, hw, hen⟩ := lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) e _ ce te he (by omega)
        m pc ρ hpw
      have a1 := Agree.widen a1s hks
      have hp1 := hp.next a1 (Nat.le_refl _) (by omega)
      have hxs := vslot_lt x
      have hsm := hp.small
      have s2 := mov_to hp1.code hp1.frame (j := vslot x) (by omega) (by omega) hsm hw
      have hF1 := hp1.frame
      have a2s : Agree fp lo Ks m1 _ := agree_write (frameOK_sub hF1 hks).room hlx.1 (by omega) w.toNat
      refine ⟨_, s1.trans (by rw [pc_add1]; exact s2), agreeW_of ((a1.mono hlo2).trans (Agree.widen a2s hks)), ?_,
        hpw.wstab m _ hWa ((a1s.mono (Nat.zero_le _)).trans (a2s.mono (Nat.zero_le _))),
        (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)).trans (keeps_write hF1.room (by omega) (fun j hj => by have := hpr j hj; omega) hlx.2 _)⟩
      refine envAt_set hp1.env (rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))) hen ?_
      intro τ' y hy
      have := vslot_lt y
      exact rd64_write_far (slot_far hF1.room (by omega) (by omega) (vslot_ne hy).symm)
    · simp at h
  | _, Γ, Λ, _, .ite cnd t e, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, hce, ⟨ct, tt⟩, hct, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append, List.length_singleton] at hs
    exact ite_ok hcc (by omega) (by omega) (by omega) (by omega) hW hlo hlo0 hlo2 hpr
      (fun m' pc' hp' hu' hk' hw' => lowB_ok (O := O) (passes := passes) (σ0 := σ0) (ex := exPlus ex (ce.length + 1))
        hS hA hlo0 hens t ct tt hct (by omega) (by omega) hW m' pc' _ ρ hp' hlo hlo2 hu' hk' hw' hpr)
      (fun m' pc' hp' hu' hk' hw' => lowB_ok (O := O) (passes := passes) (σ0 := σ0) (ex := ex) hS hA hlo0 hens e ce te
        hce (by omega) (by omega) hW m' pc' _ ρ hp' hlo hlo2 hu' hk' hw' hpr) hp hu hk hWa
  | _, Γ, Λ, _, .onTag v arms, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    simp only [lowS] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨cv, tv⟩, hcv, ⟨ca, ta⟩, hca, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact onTag_ok (lowArms_all hS hA hlo0 hens hW hlo arms) hcv hca (by omega) (by omega)
        (by simpa only [List.length_append] using hs) hW hlo hlo0 hlo2 hpr hp hu hk hWa
    · cases h
  | _, Γ, Λ, _, .call f args _ _, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, hu, hk, hWa, hpr => by
    simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, hca, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hct : frei Γ + FB + (D.params f).length + 1 ≤ callTop f (frei Γ) ta := by simp only [callTop]; omega
    have hc := callC_ok hS (hA f) args (σ.lese Λ args.orte) (σ.lese Λ args.orte) hca (by omega) hp hu hW hWa
    simp only [execStmt]
    generalize R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = o at hc ⊢
    cases o with
    | ok σ' v =>
      obtain ⟨m1, s1, a1, _, hw1⟩ := hc
      have := hW.ks
      exact ⟨m1, s1, a1.mono hlo2, envAt_agreeWIn hW hp.env a1 (Nat.le_refl _) (by omega), hw1,
        keeps_of_agreeW hW a1 hpr (by omega)⟩
    | logik e => exact hc
    | why _ _ => exact hc.elim
    | hardware e => exact hc
  | _, Γ, Λ, _, .ret e _, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, hk, hWa, hpr => by
    simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [execStmt, Sim]
    exact ret_ok hlo0 hens e he (by omega) m pc σ ρ hp hlo2 hk hW hWa
  | _, Γ, Λ, _, .assignGlob g e _ _, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr
  | _, Γ, Λ, _, .publish g e _ _ _ _, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr => by
    simp only [lowS] at h
    split at h
    · next hl =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ce, te⟩, he, hc⟩ := h
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [execStmt, Sim]
      have htop := lowE_top e _ _ _ he
      have hin := hW.lay.2.1 g
      obtain ⟨m', s', a', en, hw'⟩ := store_ok (σ := σ.lese Λ e.orte) hp hW hWa (by omega)
        (fun m pc hp => lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) e _ ce te he (by omega) m pc ρ hp)
        (fun m pc hp => (const_ok hp hl (by omega)).mono fun x hx => hx.trans (BitVec.ofInt_natCast _ _))
        hin (fun m w hm hpe => weltAt_glob hm hW.lay hW.dis hpe)
      exact ⟨m', s', a'.mono hlo2, en, hw', keeps_of_agreeW hW a' hpr (by have := hW.ks; omega)⟩
    · cases h
  | _, Γ, Λ, _, .assignSlot t f i e _ _, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr
  | _, Γ, Λ, _, .assignThru _ t _ f i e _ _, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr => by
    simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨ci1, ti⟩, hi, ⟨ca, ta⟩, ha, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [execStmt, Sim]
    have htop := lowE_top e _ _ _ he
    have hst := slotA_top ha
    simp only at hst
    generalize hσE : σ.lese Λ _ = σE
    have hWaE : WeltAt m L σE := by rw [← hσE]; exact hWa
    have hn0 := (eval σE i σE ρ).lo_le
    have hkc : ((eval σE i σE ρ).n.toNat : Int) < D.count t := by have := (eval σE i σE ρ).le_hi; omega
    have hkn : (((eval σE i σE ρ).n.toNat : Nat) : Int) = (eval σE i σE ρ).n := Int.toNat_of_nonneg hn0
    have hin := hW.lay.1 t f _ hkc
    obtain ⟨m', s', a', en, hw'⟩ := store_ok (σ := σE) hp hW hWaE (by omega)
      (fun m pc hp => lowE_ok σE σE (fun _ h => h) e _ ce te he (by omega) m pc ρ hp)
      (fun m pc hp => slotA_ok ha (by omega)
        (fun m pc hp => lowE_ok σE σE (fun _ h => h) i _ ci1 ti hi (by omega) m pc ρ hp) hp)
      hin (fun m w hm hpe => by
        have := weltAt_slot hm hW.lay hW.dis hkc hpe
        rw [hkn] at this
        exact this)
    exact ⟨m', s', a'.mono hlo2, en, hw', keeps_of_agreeW hW a' hpr (by have := hW.ks; omega)⟩
  | _, Γ, Λ, _, .leave _, c, top, h, _, _, _, m, pc, σ, ρ, hp, _, _, _, _, hWa, _ => by
    simp only [lowS] at h
    split at h
    · next hl =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execStmt, Sim]
      exact jmp_reach hp.code hl hp.env hWa
    · cases h
  | _, Γ, Λ, _, .next _, c, top, h, _, _, _, m, pc, σ, ρ, hp, _, _, _, _, hWa, _ => by
    simp only [lowS] at h
    split at h
    · next hl =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [execStmt, Sim]
      exact jmp_reach hp.code hl hp.env hWa
    · cases h
  | _, Γ, Λ, _, .traverse t inv body, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    simp only [lowS] at h
    split at h
    · next hn =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨ci', hci, cb, hcb, htr⟩ := h
      simp only [travC] at htr
      split at htr
      · next hlenc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at htr
        obtain ⟨rfl, rfl⟩ := htr
        have hlen := travCode_len (s := frei Γ) (n := D.count t) (ci' := ci'.1) (cb := cb.1)
        simp only [execStmt]
        exact trav_ok hn hci hlenc hlo0 (by omega) hW hlo hlo2 hpr
          (fun m' pc' σ' ρ' hp' hu' hk' hw' => lowB_ok (O := O) (passes := passes) (σ0 := σ0) (pr := frei Γ :: pr)
            (ex := (48, 0)) hS hA hlo0 hens body cb.1 cb.2 hcb (by omega) (by omega) hW m' pc' σ' ρ' hp' hlo
            (by have := hlo2; simp only [frei, List.length_cons] at this ⊢; omega) hu' hk' hw'
            (fun j hj => by
              simp only [List.mem_cons] at hj
              simp only [frei, List.length_cons]
              rcases hj with rfl | hj
              · simp only [frei]; omega
              · have := hpr j hj; simp only [frei] at this; omega)) hp hu hk hWa
      · cases htr
    · cases h
  | _, Γ, Λ, _, .breaking _ body, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    simp only [lowS] at h
    simp only [execStmt]
    exact lowB_ok (O := O) (passes := passes) (σ0 := σ0) (pr := pr) (ex := ex) hS hA hlo0 hens body c top h hK hs hW
      m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  | _, Γ, Λ, _, .advances .., c, top, h, _, _, _, m, pc, σ, ρ, hp, _, _, _, _, hWa, _
  | _, Γ, Λ, _, .retires .., c, top, h, _, _, _, m, pc, σ, ρ, hp, _, _, _, _, hWa, _ => by
    simp only [lowS, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execStmt, Sim]
    exact ⟨m, by simpa using Star.refl _ m, AgreeW.refl _ _ _ _ _, hp.env, hWa, Keeps.refl _ _ _⟩
  | _, _, _, _, .putBytes .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, Γ, Λ, _, .shift t field ht i von nach hn he hw hl, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr =>
    shift_ok ht i von nach hn he hw hl h (by omega) hW hp hlo2 hWa hpr
  | _, Γ, Λ, _, .onOption o p a, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    simp only [lowS] at h
    split at h
    · next hn =>
      simp only [decide_eq_true_eq] at hn
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, hce, ⟨ct, tt⟩, hct, hc⟩ := h
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [List.length_append, List.length_cons, List.length_nil] at hs
      exact onOption_ok (o := o) (t := p) (e := a) (cc := cc) (ct := ct) (ce := ce) hn (by omega) hcc (by omega) (by omega) hW hlo hlo0 hlo2 hpr
        (fun k _ m' pc' hp' hu' hk' hw' => lowB_ok (O := O) (passes := passes) (σ0 := σ0)
          (ex := exPlus ex (ce.length + 1)) hS hA hlo0 hens p ct tt hct (by omega) (by omega) hW m' pc' _ (.cons k ρ)
          (by simpa only [frei, List.length_cons, Nat.add_succ] using hp') hlo
          (by simp only [frei, List.length_cons] at hlo2 ⊢; omega) hu' hk' hw'
          (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega))
        (fun m' pc' hp' hu' hk' hw' => lowB_ok (O := O) (passes := passes) (σ0 := σ0) (ex := ex)
          hS hA hlo0 hens a ce te hce (by omega) (by omega) hW m' pc' _ ρ hp' hlo hlo2 hu' hk' hw' hpr)
        hp hu hk hWa
    · cases h
  | _, _, _, _, .onWhy .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .callInd .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, Γ, Λ, _, .locks Lk hr body, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    simp only [lowS] at h
    split at h
    · next hc =>
      obtain ⟨hrf, hex1, hex2⟩ := hc
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨cb, tb⟩, hcb, hc⟩ := h
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hlen := locksCode_len L (L.lk Lk) (frei Γ) cb ex.1 ex.2
      have hks := hW.ks
      simp only [execStmt]
      exact locks_ok hrf hex1 hex2 (by omega) hW hlo0 hlo2 hpr
        (fun m' σ' hp' hu' hk' hw' => lowB_ok (O := O) (passes := passes) (σ0 := σ0) (pr := pr)
          (ex := (16 * 30, 16 * 60)) hS hA hlo0 hens body cb tb hcb (by omega) (by rw [hlen] at hs; omega)
          ⟨hW.lay, hW.dis, hW.top, hW.ord, by omega⟩ m' _ σ' ρ hp' hlo hlo2 hu' hk' hw' hpr) hp hu hk hWa
    · cases h
  | _, _, _, _, .retry .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .forever .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, Γ, Λ, _, .axiomCall a args hn _ _ _ _, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr => by
    simp only [lowS] at h
    have hks := hW.ks
    have h7 := torC_top h
    obtain ⟨m1, w, s1, a1, _, hw1, _⟩ := torC0_ok (O := O) (σ := σ.lese Λ args.orte) h (by omega) hW hp hWa
    obtain ⟨u, hu⟩ := einpassenErg_none (z := O.zeiger) hn
      (O.wirkt a ((σ.lese Λ args.orte).fragt (.inl a)) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2
    simp only [execStmt]
    rw [axiomAntwort_eq, hu]
    exact ⟨m1, s1, a1.mono hlo2, envAt_agreeWIn hW hp.env a1 (Nat.le_refl _) (by omega), hw1,
      keeps_of_agreeW hW a1 hpr (by omega)⟩
  | _, _, _, _, .regWrite .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .transition .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .retWhy .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h
  | _, _, _, _, .assignSlotRef .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS] at h

theorem lowB_ok {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int} :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (b : Block D (vertragVon D f) l Γ Λ Λ') → (c : List II) → (top : Nat) →
    lowB A L lo (cens, tens) pr ex b = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS m pc fp K (frei Γ) c ρ →
    FB ≤ lo → lo ≤ frei Γ → Umf L A C dv m fp Ks K → Kopf f m fp K rp cfp ρ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ) →
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R b σ ρ)
  | _, Γ, _, _, .nil, c, top, h, _, _, _, m, pc, σ, ρ, hp, _, _, _, _, hWa, hpr => by
    simp only [lowB, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execBlock, Sim]
    exact ⟨m, by simpa using Star.refl _ m, AgreeW.refl _ _ _ _ _, hp.env, hWa, Keeps.refl _ _ _⟩
  | _, Γ, _, _, .cons s rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cr, tr⟩, hr, ⟨cs, ts⟩, hs1, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have ih := lowS_ok (O := O) (passes := passes) (σ0 := σ0) (ex := exPlus ex cr.length) hS hA hlo0 hens s cs ts
      hs1 (by omega) (by omega) hW m pc σ ρ hp.left hlo hlo2 hu hk hWa hpr
    have hL : pc + BitVec.ofNat 64 (16 * cs.length) + BitVec.ofInt 64 (exPlus ex cr.length).1 =
        pc + BitVec.ofNat 64 (16 * (cs ++ cr).length) + BitVec.ofInt 64 ex.1 := by
      simp only [exPlus, List.length_append]; exact tgt_eq (by omega)
    have hN : pc + BitVec.ofNat 64 (16 * cs.length) + BitVec.ofInt 64 (exPlus ex cr.length).2 =
        pc + BitVec.ofNat 64 (16 * (cs ++ cr).length) + BitVec.ofInt 64 ex.2 := by
      simp only [exPlus, List.length_append]; exact tgt_eq (by omega)
    simp only [execBlock]
    generalize execStmt O passes R s σ ρ = o at ih ⊢
    cases o with
    | ok σ1 ρ1 =>
      obtain ⟨m1, s1, a1, e1, hw1, k1⟩ := ih
      have hf := codeFar_right (n := cs.length) (k := cr.length) (by simpa using hp.far)
      have hp1 : PreS m1 (pc + BitVec.ofNat 64 (16 * cs.length)) fp K (frei Γ) cr ρ1 :=
        ⟨hp.ctx, hp.small, frameOK_agreeW hp.frame a1, codeAt_agreeWIn hW a1 (codeAt_right hp.code) hf, hf, e1, trivial,
          wstab_true _ _⟩
      have ih2 := lowB_ok (O := O) (passes := passes) (σ0 := σ0) (ex := ex) hS hA hlo0 hens rest cr tr hr (by omega)
        (by omega) hW m1 _ σ1 ρ1 hp1 hlo hlo2 (hu.agreeW hW a1 hlo) (hk.agreeW hW a1 (by omega)) hw1 hpr
      rw [pc_add1]
      exact Sim.prefix hlo s1 a1 k1 ih2
    | zurueck | why | leave | next | logik | hardware => exact Sim.ziel ih (fun _ _ h => by cases h) hL hN
  | _, Γ, Λ, _, .bind e rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    simp only [execBlock]
    have hks := hW.ks
    have htop := lowE_top e _ _ _ he
    have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, s1, a1s, w, hw, hen⟩ :=
      lowE_ok (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) e _ ce te he (by omega) m pc ρ hpw
    have a1 := Agree.widen a1s hks
    have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
    have hf := codeFar_right (n := ce.length) (k := cr.length) (by simpa using hp.far)
    have hp1 : PreS m1 (pc + BitVec.ofNat 64 (16 * ce.length)) fp K (frei Γ + 1) cr
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) :=
      ⟨by simp only [frei, List.length_cons]; omega, hp.small, hp.frame.agree a1, (codeAt_right hp.code).agree a1 hf, hf,
       envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) hw hen, trivial, wstab_true _ _⟩
    have ih := lowB_ok (O := O) (passes := passes) (σ0 := σ0) (ex := ex) hS hA hlo0 hens rest cr tr hr (by omega)
      (by omega) hW m1 _ (σ.lese Λ e.orte) _ hp1 hlo
      (by simp only [frei, List.length_cons] at hlo2 ⊢; omega) (hu.agreeW hW (agreeW_of (a1.mono hlo2)) hlo)
      (hk.agreeW hW (agreeW_of (a1.mono hlo2)) (by omega)) hWa1 (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
    rw [pc_add1]
    exact Sim.prefix hlo s1 (agreeW_of (a1.mono hlo2)) (keeps_of_agreeW hW a1 hpr (by have := hW.ks; omega)) (Sim.schrumpf ih)
  | _, Γ, Λ, _, .bindCall f args he _ _ rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ca, ta⟩, hca, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hFB3 : FB = 3 := rfl
    have hks := hW.ks
    have hct : frei Γ + FB + (D.params f).length + 1 ≤ callTop f (frei Γ) ta := by simp only [callTop]; omega
    have hc := callC_ok hS (hA f) args (σ.lese Λ args.orte) (σ.lese Λ args.orte) hca (by omega) hp.left.left hu hW hWa
    simp only [execBlock]
    generalize R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) = o at hc ⊢
    cases o with
    | ok σ' v =>
      obtain ⟨m1, s1, a1, ⟨w, hw, hew⟩, hw1⟩ := hc
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
      have hp2 : PreS m2 _ fp K (frei Γ + 1) cr (Env.cons (ergWert he v) ρ) :=
        ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
         envAt_cons hq.env (rd_same hp1.frame (by omega) w) (encErg_wert he hew), trivial, wstab_true _ _⟩
      have ih := lowB_ok (O := O) (passes := passes) (σ0 := σ0) (ex := ex) hS hA hlo0 hens rest cr tr hr (by omega)
        (by omega) hW m2 _ σ' _ hp2 hlo
        (by simp only [frei, List.length_cons] at hlo2 ⊢; omega)
        (hu.agreeW hW ((a1.trans (agreeW_of a2)).mono hlo2) hlo)
        (hk.agreeW hW ((a1.trans (agreeW_of a2)).mono hlo2) (by omega)) hw2
        (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
      rw [pc_add1 pc (callC A f (frei Γ) ca ++ [ci 2 (frei Γ) (frei Γ + 2) 0]) cr]
      exact Sim.prefix hlo (s1.trans s2) ((a1.trans (agreeW_of a2)).mono hlo2)
        (keeps_of_agreeW hW (a1.trans (agreeW_of a2)) hpr (by have := hW.ks; omega)) (Sim.schrumpf ih)
    | logik e => exact hc
    | why _ _ => exact hc.elim
    | hardware e => exact hc
  | _, _, _, _, .bindCallInd .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .bindCallElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, Γ, Λ, _, .bindAxiom a args he _ _ _ _ rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa,
      hpr => by
    simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ct, tt⟩, ht, ck, hck, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append] at hs
    have hks := hW.ks
    simp only [execBlock]
    rcases torBind_ok (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ) he ht hck (by omega) (by omega) hW hp hWa with
      ⟨v, m2, w, hAA, s12, a12, hw2, hen, hW2⟩ | ⟨hAA, hst⟩
    · rw [hAA]
      have hq := hp.nextW hW a12 (d' := frei Γ + 1) (by have := hp.ctx; omega) (by omega) (by omega)
      have hp2 : PreS m2 _ fp K (frei Γ + 1) cr (Env.cons (ergWert he v) ρ) :=
        ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
         envAt_cons hq.env hw2 hen, trivial, wstab_true _ _⟩
      have ih := lowB_ok (O := O) (passes := passes) (σ0 := σ0) (ex := ex) hS hA hlo0 hens rest cr tr hr (by omega)
        (by omega) hW m2 _ _ _ hp2 hlo
        (by simp only [frei, List.length_cons] at hlo2 ⊢; omega)
        (hu.agreeW hW (a12.mono hlo2) hlo) (hk.agreeW hW (a12.mono hlo2) (by omega)) hW2
        (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)
      rw [pc_add1 pc (ct ++ ck) cr]
      exact Sim.prefix hlo s12 (a12.mono hlo2) (keeps_of_agreeW hW a12 hpr (by omega)) (Sim.schrumpf ih)
    · rw [hAA]
      exact hst
  | _, _, _, _, .bindAxiomElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .regRead .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .regReadElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, Γ, Λ, _, .awaits g _ _ _ _ rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    simp only [lowB] at h
    split at h
    · next hl =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨cr, tr⟩, hr, hc⟩ := h
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [List.length_append] at hs
      exact awaits_ok hl (by omega) hW hlo hlo0 hlo2 hpr (fun m' σ' ρ' hp' hu' hk' hw' =>
        lowB_ok (O := O) (passes := passes) (σ0 := σ0) (ex := ex) hS hA hlo0 hens rest cr tr hr (by omega)
          (by omega) hW m' _ σ' ρ' hp' hlo (by simp only [frei, List.length_cons] at hlo2 ⊢; omega) hu' hk' hw'
          (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)) hp hu hk hWa
    · cases h
  | _, Γ, Λ, _, .exchange g neu _ _ rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    simp only [lowB] at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff, pure] at h
      obtain ⟨⟨cn, tn⟩, hn, ⟨cr, tr⟩, hr, h⟩ := h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlen := exC_len (frei Γ) (L.ga g) cn
        simp only [List.length_append, hlen] at hs
        exact exch_ok hn (by omega) (by omega) hW hlo hlo0 hlo2 hpr (fun m' σ' ρ' hp' hu' hk' hw' =>
          lowB_ok (O := O) (passes := passes) (σ0 := σ0) (ex := ex) hS hA hlo0 hens rest cr tr hr (by omega)
            (by omega) hW m' _ σ' ρ' hp' hlo (by simp only [frei, List.length_cons] at hlo2 ⊢; omega) hu' hk' hw'
            (fun j hj => by have := hpr j hj; simp only [frei, List.length_cons] at this ⊢; omega)) hp hu hk hWa
      · cases h
    · cases h
  | _, _, _, _, .narrow .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .check .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .float .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatLit .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatOf .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatNarrow .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h

theorem lowArms_all {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} (hW : WIn L fp Ks K) (hlo : FB ≤ lo) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {cs : List (Option (Int × Int))} →
    (arms : Arms D (vertragVon D f) l Γ Λ Λ' cs) →
    ArmsAll (fun b => BlockRuns O passes R L A C dv cap P f σ0 ρ0 rp cfp fp lo Ks K (cens, tens) pr b) arms
  | _, _, _, _, _, .nil => trivial
  | _, _, _, _, _, .cons b rest =>
    ⟨(fun ex cb tb hc ht hs m pc σ ρ hp hlo2 hu hk hw hpr =>
        lowB_ok hS hA hlo0 hens b cb tb hc ht hs hW m pc σ ρ hp hlo hlo2 hu hk hw hpr),
      lowArms_all hS hA hlo0 hens hW hlo rest⟩

end

end Gabbro.Stage0.Senke
