/-
  File:      stage0/Stage0/Senke/Anweisung/Satz.lean
  Subject:   Mutual `ir_sim` for statements, blocks and function end blocks, calls included: where machine G ends a block normally (`ok`), the
             lowered code runs to its end and leaves the new environment in the frame, changing no slot below
             `lo`; where G ends in a logic outcome, the code stops with its `exit_group` code. G answers nothing
             else for a lowered block (`Sim`).
-/
import Stage0.Senke.Anweisung.Schreiben
import Stage0.Senke.Sperre.Satz
import Stage0.Senke.Anweisung.Faelle.Wahl
import Stage0.Senke.Anweisung.Option
import Stage0.Senke.Anweisung.Tag
import Stage0.Senke.Anweisung.Bytes.Shift
import Stage0.Senke.Anweisung.Bytes.Put

import Stage0.Senke.Anweisung.Faelle.Schreiben
import Stage0.Senke.Anweisung.Faelle.Speicher
import Stage0.Senke.Anweisung.Faelle.Traversal
import Stage0.Senke.Anweisung.Faelle.Bloecke
import Stage0.Senke.Anweisung.Faelle.BlockRuf
import Stage0.Senke.Anweisung.Faelle.Ende
import Stage0.Senke.Anweisung.Faelle.EndRuf
import Stage0.Senke.Anweisung.Faelle.EndWahl
import Stage0.Senke.Anweisung.Faelle.EndFehler
import Stage0.Senke.Anweisung.Faelle.EndAtomar

import Stage0.Senke.Anweisung.Faelle.Check

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {V : Vertrag D}

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
  | _, Γ, Λ, _, .assignVar x e, c, top, h, hK, arg4, hW, m, pc, σ, ρ, hp, arg11, hlo2, arg13, arg14, hWa, hpr => by
    exact assignVar_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (x := x) (e := e)
      c top h hK arg4 hW m pc σ ρ hp arg11 hlo2 arg13 arg14 hWa hpr
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
  | _, Γ, Λ, _, .call f args proof0 proof1, c, top, h, hK, arg4, hW, m, pc, σ, ρ, hp, arg11, hlo2, hu, hk, hWa, hpr => by
    exact call_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (callee := f) (args := args) (proof0 := proof0) (proof1 := proof1)
      c top h hK arg4 hW m pc σ ρ hp arg11 hlo2 hu hk hWa hpr
  | _, Γ, Λ, _, .ret e proof0, c, top, h, hK, arg4, hW, m, pc, σ, ρ, hp, arg11, hlo2, arg13, hk, hWa, hpr => by
    exact ret_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (e := e) (proof0 := proof0)
      c top h hK arg4 hW m pc σ ρ hp arg11 hlo2 arg13 hk hWa hpr
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
  | _, Γ, Λ, _, .leave proof0, c, top, h, arg3, arg4, arg5, m, pc, σ, ρ, hp, arg11, arg12, arg13, arg14, hWa, arg16 => by
    exact leave_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (proof0 := proof0)
      c top h arg3 arg4 arg5 m pc σ ρ hp arg11 arg12 arg13 arg14 hWa arg16
  | _, Γ, Λ, _, .next proof0, c, top, h, arg3, arg4, arg5, m, pc, σ, ρ, hp, arg11, arg12, arg13, arg14, hWa, arg16 => by
    exact next_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (proof0 := proof0)
      c top h arg3 arg4 arg5 m pc σ ρ hp arg11 arg12 arg13 arg14 hWa arg16
  | _, Γ, Λ, _, .traverse t inv body, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    exact traverse_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (t := t) (inv := inv) (body := body)
      (fun {pr ex} => lowB_ok (pr := pr) (ex := ex) hS hA hlo0 hens body)
      c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
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
  | _, Γ, Λ, _, .putBytes t field hf n i hlo hhi e hw hl, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr =>
    putBytes_ok hf n i hlo hhi e hw hl h (by omega) hW hp hlo2 hWa hpr
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
  | _, Γ, Λ, _, .axiomCall a args hn proof0 proof1 proof2 proof3, c, top, h, hK, arg4, hW, m, pc, σ, ρ, hp, arg11, hlo2, arg13, arg14, hWa, hpr => by
    exact axiomCall_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (a := a) (args := args) (hn := hn) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (proof3 := proof3)
      c top h hK arg4 hW m pc σ ρ hp arg11 hlo2 arg13 arg14 hWa hpr
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
    exact blockCons_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (s := s) (rest := rest)
      (fun {pr ex} => lowS_ok (pr := pr) (ex := ex) hS hA hlo0 hens s)
      (fun {pr ex} => lowB_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  | _, Γ, Λ, _, .bind e rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    exact blockBind_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (e := e) (rest := rest)
      (fun {pr ex} => lowB_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  | _, Γ, Λ, _, .bindCall f args he proof0 proof1 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    exact blockCall_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (callee := f) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (rest := rest)
      (fun {pr ex} => lowB_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  | _, _, _, _, .bindCallInd .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .bindCallElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, Γ, Λ, _, .bindAxiom a args he proof0 proof1 proof2 proof3 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    exact blockAxiom_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (a := a) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (proof3 := proof3) (rest := rest)
      (fun {pr ex} => lowB_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
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
  | _, Γ, Λ, _, .check cnd err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    exact blockCheck_case hS hA hlo0 hens
      (fun {pr ex} => lowEnd_ok (pr := pr) (ex := ex) hS hA hlo0 hens err)
      (fun {pr ex} => lowB_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  | _, _, _, _, .float .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatLit .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatOf .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .floatNarrow .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h

theorem lowEnd_ok {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) (hens : lowE L (P.ensures f) (lo + 1) = some (cens, tens))
    {pr : List Nat} {ex : Int × Int} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → (b : Endblock D (vertragVon D f) l Γ Λ) → (c : List II) →
    (top : Nat) → lowEnd A L lo (cens, tens) pr ex b = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS m pc fp K (frei Γ) c ρ →
    lo ≤ frei Γ → Umf L A C dv m fp Ks K → Kopf f m fp K rp cfp ρ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ) →
    Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R b σ ρ)
  | _, Γ, Λ, .ret e proof0, c, top, h, hK, arg4, hW, m, pc, σ, ρ, hp, hlo, arg12, hk, hWa, hpr => by
    exact endRet_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (e := e) (proof0 := proof0)
      c top h hK arg4 hW m pc σ ρ hp hlo arg12 hk hWa hpr
  | _, Γ, _, .cons s rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    exact endCons_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (s := s) (rest := rest)
      (fun {pr ex} => lowS_ok (pr := pr) (ex := ex) hS hA hlo0 hens s)
      (fun {pr ex} => lowEnd_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  | _, Γ, Λ, .bind e rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    exact endBind_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (e := e) (rest := rest)
      (fun {pr ex} => lowEnd_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  | _, Γ, Λ, .bindCall g args he proof0 proof1 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    exact endCall_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (g := g) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (rest := rest)
      (fun {pr ex} => lowEnd_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  | _, Γ, Λ, .ite cnd t e, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    exact endIte_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (cnd := cnd) (t := t) (e := e)
      (fun {pr ex} => lowEnd_ok (pr := pr) (ex := ex) hS hA hlo0 hens t)
      (fun {pr ex} => lowEnd_ok (pr := pr) (ex := ex) hS hA hlo0 hens e)
      c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  | _, _, _, .retWhy .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .leave .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .next .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .bindCallElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, Γ, Λ, .bindAxiom a args he proof0 proof1 proof2 proof3 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    exact endAxiom_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (a := a) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (proof3 := proof3) (rest := rest)
      (fun {pr ex} => lowEnd_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  | _, Γ, Λ, .bindAxiomElse a args he proof0 proof1 proof2 proof3 proof4 err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    exact endAxiomElse_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (a := a) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (proof3 := proof3) (proof4 := proof4) (err := err) (rest := rest)
      (fun {pr ex} => lowEnd_ok (pr := pr) (ex := ex) hS hA hlo0 hens err)
      (fun {pr ex} => lowEnd_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  | _, _, _, .regRead .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .regReadElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, Γ, Λ, .awaits g proof0 proof1 proof2 proof3 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    exact endAwaits_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (g := g) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (proof3 := proof3) (rest := rest)
      (fun {pr ex} => lowEnd_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  | _, _, _, .bindCallInd .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, _, _, .narrow .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd] at h
  | _, Γ, Λ, .exchange g neu proof0 proof1 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    exact endExchange_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (g := g) (neu := neu) (proof0 := proof0) (proof1 := proof1) (rest := rest)
      (fun {pr ex} => lowEnd_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr

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
