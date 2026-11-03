module
public import Stage0.Senke.Anweisung.Satz.Teil2Opt
public import Stage0.Senke.Anweisung.Satz.Teil2OptElse

public import Stage0.Senke.Anweisung.Schreiben
public import Stage0.Senke.Welt.Spans.CellStore
public import Stage0.Senke.Welt.WordCell
public import Stage0.Senke.Sperre.Satz
public import Stage0.Senke.Anweisung.Faelle.Gleit.Narrow
public import Stage0.Senke.Anweisung.Faelle.Gleit.Literal
public import Stage0.Senke.Anweisung.Faelle.Gleit.Add
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Wahl
public import Stage0.Senke.Anweisung.Bindung.Option
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Why
public import Stage0.Senke.Anweisung.Faelle.CallElse
public import Stage0.Senke.Anweisung.Faelle.Fnptr
public import Stage0.Senke.Anweisung.Bytes.Shift
public import Stage0.Senke.Anweisung.Bytes.Put
public import Stage0.Senke.Anweisung.Faelle.Schreiben
public import Stage0.Senke.Anweisung.Faelle.Speicher
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Traversal
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Retry
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Runtime.Teil2
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Emission
public import Stage0.Senke.Anweisung.Faelle.Bloecke
public import Stage0.Senke.Anweisung.Faelle.BlockRuf
public import Stage0.Senke.Anweisung.Faelle.Ende
public import Stage0.Senke.Anweisung.Faelle.Ends.EndRuf
public import Stage0.Senke.Anweisung.Faelle.Ends.EndWahl
public import Stage0.Senke.Anweisung.Faelle.Ends.EndFehler
public import Stage0.Senke.Anweisung.Faelle.Ends.EndAtomar
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.NarrowCases
public import Stage0.Senke.Anweisung.Faelle.BlockFehler
public import Stage0.Senke.Anweisung.Satz.Teil4

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable [Kern]
variable {D : Deklaration} {L : Lay D} {V : Vertrag D}

mutual
theorem lowS_ok {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int} :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (s : Stmt D (vertragVon D f) l Γ Λ Λ') → (c : List II) → (top : Nat) →
    lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex s = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved →
    FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) →
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R s σ ρ) reserved
  | _, Γ, Λ, _, .assignVar x e, c, top, h, hK, arg4, hW, m, pc, σ, ρ, hp, arg11, hlo2, arg13, arg14, hWa, hpr => by
    exact assignVar_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (x := x) (e := e)
      c top h hK arg4 hW m pc σ ρ hp arg11 hlo2 arg13 arg14 hWa hpr
  | _, Γ, Λ, _, .ite cnd t e, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowS_ok_ite (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (cnd := cnd) (t := t) (e := e) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_t := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ t) (ih_lowB_ok_e := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ e)
  | _, Γ, Λ, _, .onTag v arms, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowS_ok_onTag (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (v := v) (arms := arms) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowArms_all_arms := fun hS hA hlo0 hens hW hlo => lowArms_all hS hA hlo0 hens hW hlo arms)
  | _, Γ, Λ, _, .call f args proof0 proof1, c, top, h, hK, arg4, hW, m, pc, σ, ρ, hp, arg11, hlo2, hu, hk, hWa, hpr => by
    exact call_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (callee := f) (args := args) (proof0 := proof0) (proof1 := proof1)
      c top h hK arg4 hW m pc σ ρ hp arg11 hlo2 hu hk hWa hpr
  | _, Γ, Λ, _, .ret e proof0, c, top, h, hK, arg4, hW, m, pc, σ, ρ, hp, arg11, hlo2, arg13, hk, hWa, hpr => by
    exact ret_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (e := e) (proof0 := proof0)
      c top h hK arg4 hW m pc σ ρ hp arg11 hlo2 arg13 hk hWa hpr
  | _, Γ, Λ, _, .assignGlob g e zz1 zz2, c, top, h, hK, zzh3, hW, m, pc, σ, ρ, hp, zzh4, hlo2, zzh5, zzh6, hWa, hpr =>
      lowS_ok_assignGlob (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (g := g) (e := e) (zz1 := zz1) (zz2 := zz2) (c := c) (top := top) (h := h) (hK := hK) (zzh3 := zzh3) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (zzh4 := zzh4) (hlo2 := hlo2) (zzh5 := zzh5) (zzh6 := zzh6) (hWa := hWa) (hpr := hpr)
  | _, Γ, Λ, _, .publish g e zz1 zz2 zz3 zz4, c, top, h, hK, zzh5, hW, m, pc, σ, ρ, hp, zzh6, hlo2, zzh7, zzh8, hWa, hpr =>
      lowS_ok_publish (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (g := g) (e := e) (zz1 := zz1) (zz2 := zz2) (zz3 := zz3) (zz4 := zz4) (c := c) (top := top) (h := h) (hK := hK) (zzh5 := zzh5) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (zzh6 := zzh6) (hlo2 := hlo2) (zzh7 := zzh7) (zzh8 := zzh8) (hWa := hWa) (hpr := hpr)
  | _, Γ, Λ, _, .assignSlot t f i e _ _, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr
  | _, Γ, Λ, _, .assignThru _ t _ f i e _ _, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr => by
    simp only [lowS, ← hlo0, resultWords_vertragVon, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ce, te⟩, he, ⟨ci1, ti⟩, hi, hc⟩ := h
    simp only [execStmt, Sim]
    have hks := hW.ks
    have tops := slotStoreC_top hc
    generalize hσE : σ.lese Λ _ = σE
    have hWaE : WeltAt m L σE := by rw [← hσE]; exact hWa
    have hn0 := (eval σE i σE ρ).lo_le
    have hkc : ((eval σE i σE ρ).n.toNat : Int) < D.count t := by have := (eval σE i σE ρ).le_hi; omega
    have toWord : BitVec.ofInt 64 (eval σE i σE ρ).n = BitVec.ofNat 64 (eval σE i σE ρ).n.toNat := by
      rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg hn0]
    obtain ⟨m', s', a', hw'⟩ := slotStoreC_ok (σ := σE) (kn := (eval σE i σE ρ).n.toNat) hc (by omega)
      (L.bounded hkc) hW.lay hW.dis hW.lo (PreS.welt hp hks hWaE hW.lay hW.lo)
      (fun m pc hp => lowE_ok σE σE (fun _ h => h) hW.lay e _ ce te he (by omega) m pc ρ hp)
      (fun m pc hp => ((lowE_ok σE σE (fun _ h => h) hW.lay i _ ci1 ti hi (by omega) m pc ρ hp).word trivial).mono
        fun w hw => by simp only [Enc] at hw; rw [hw, toWord])
    rw [Int.toNat_of_nonneg hn0] at hw'
    exact ⟨m', s', (a'.widen hks).mono hlo2,
      envAt_agreeW hp.env a' hW.lo (by have := hp.frame.room; omega) (Nat.le_refl _) (by omega), hw',
      keeps_of_agreeW hW (a'.widen hks) hpr (by omega)⟩
  | _, Γ, Λ, _, .leave proof0, c, top, h, arg3, arg4, arg5, m, pc, σ, ρ, hp, arg11, arg12, arg13, arg14, hWa, arg16 => by
    exact leave_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (proof0 := proof0)
      c top h arg3 arg4 arg5 m pc σ ρ hp arg11 arg12 arg13 arg14 hWa arg16
  | _, Γ, Λ, _, .next proof0, c, top, h, arg3, arg4, arg5, m, pc, σ, ρ, hp, arg11, arg12, arg13, arg14, hWa, arg16 => by
    exact next_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (proof0 := proof0)
      c top h arg3 arg4 arg5 m pc σ ρ hp arg11 arg12 arg13 arg14 hWa arg16
  | _, Γ, Λ, _, .traverse t inv body, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowS_ok_traverse (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (t := t) (inv := inv) (body := body) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_body := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ body)
  | _, Γ, Λ, _, .breaking zz1 body, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowS_ok_breaking (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (zz1 := zz1) (body := body) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_body := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ body)
  | _, Γ, Λ, _, .advances .., c, top, h, _, _, _, m, pc, σ, ρ, hp, _, _, _, _, hWa, _
  | _, Γ, Λ, _, .retires .., c, top, h, _, _, _, m, pc, σ, ρ, hp, _, _, _, _, hWa, _ => by
    simp only [lowS, ← hlo0, resultWords_vertragVon, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execStmt, Sim]
    exact ⟨m, by simpa using Star.refl _ m, AgreeW.refl _ _ _ _ _, hp.env, hWa, Keeps.refl _ _ _⟩
  | _, Γ, Λ, _, .putBytes t field hf n i hlo hhi e hw hl, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr =>
    putBytes_ok hf n i hlo hhi e hw hl h (by omega) hW hp hlo2 hWa hpr
  | _, Γ, Λ, _, .shift t field ht i von nach hn he hw hl, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, _, _, hWa, hpr =>
    shift_ok ht i von nach hn he hw hl h (by omega) hW hp hlo2 hWa hpr
  | _, Γ, Λ, _, .onOption o p a, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowS_ok_onOption (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (o := o) (p := p) (a := a) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_p := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ p) (ih_lowB_ok_a := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ a)
  | _, Γ, Λ, _, .onWhy v arms, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowS_ok_onWhy (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (v := v) (arms := arms) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowGrund_all_arms := fun hS hA hlo0 hens hW hlo => lowGrund_all hS hA hlo0 hens hW hlo arms)
  | _, Γ, Λ, _, .callInd p args hf hr, c, top, h, hK, _, hW, m, pc, σ, ρ, hp, _, hlo2, hu, _, hWa, hpr =>
    indStmt_ok hS hA p args hf hr h hK hW hp hlo2 hu hWa hpr
  | _, Γ, Λ, _, .locks Lk hr body, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowS_ok_locks (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (hr := hr) (body := body) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_body := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ body)
  | _, Γ, Λ, _, .retry n bis body overflow, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hw, hpr =>
      lowS_ok_retry (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (n := n) (bis := bis) (body := body) (overflow := overflow) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hw := hw) (hpr := hpr) (ih_lowB_ok_body := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ body) (ih_lowB_ok_overflow := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ overflow)
  | _, Γ, Λ, _, .forever a inv body, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hw, hpr =>
      lowS_ok_forever (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (a := a) (inv := inv) (body := body) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hw := hw) (hpr := hpr) (ih_lowB_ok_body := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ body)
  | _, Γ, Λ, _, .axiomCall a args hn proof0 proof1 proof2 proof3, c, top, h, hK, arg4, hW, m, pc, σ, ρ, hp, arg11, hlo2, arg13, arg14, hWa, hpr => by
    exact axiomCall_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (a := a) (args := args) (hn := hn) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (proof3 := proof3)
      c top h hK arg4 hW m pc σ ρ hp arg11 hlo2 arg13 arg14 hWa hpr
  | _, _, _, _, .axiomCallElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS, resultWords_vertragVon] at h
  | _, _, _, _, .callIndElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS, resultWords_vertragVon] at h
  | _, _, _, _, .regWrite .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS, resultWords_vertragVon] at h
  | _, _, _, _, .transition .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS, resultWords_vertragVon] at h
  | _, Γ, Λ, _, .retWhy r hp0, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    exact retWhy_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (r := r) (proof0 := hp0)
      c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  | _, Γ, Λ, _, .assignSlotRef r t ht ho field e hw hL, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
    assignSlotRef_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens r t ht ho field e
      c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr

  | _, _, _, _, .consumeTraverse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS, resultWords_vertragVon] at h
  | _, _, _, _, .retScoped .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS, resultWords_vertragVon] at h
  | _, _, _, _, .retWhyScoped .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowS, resultWords_vertragVon] at h

theorem lowB_ok {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int} :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (b : Block D (vertragVon D f) l Γ Λ Λ') → (c : List II) → (top : Nat) →
    lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex b = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved →
    FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) →
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R b σ ρ) reserved
  | _, Γ, _, _, .nil, c, top, h, zzh1, zzh2, zzh3, m, pc, σ, ρ, hp, zzh4, zzh5, zzh6, zzh7, hWa, hpr =>
      lowB_ok_nil (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (c := c) (top := top) (h := h) (zzh1 := zzh1) (zzh2 := zzh2) (zzh3 := zzh3) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (zzh4 := zzh4) (zzh5 := zzh5) (zzh6 := zzh6) (zzh7 := zzh7) (hWa := hWa) (hpr := hpr)
  | _, Γ, _, _, .cons s rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_cons (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (s := s) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowS_ok_s := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowS_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ s) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest)
  | _, Γ, Λ, _, .bind e rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_bind (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (e := e) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest)
  | _, Γ, Λ, _, .bindCall f args he proof0 proof1 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
    exact blockCall_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (callee := f) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (rest := rest)
      (fun {pr ex} => lowB_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
      c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  | _, Γ, Λ, _, .bindCallInd p args he proof0 proof1 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_bindCallInd (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (p := p) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest)
  | _, Γ, Λ, _, .bindCallElse g args he p0 p1 err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_bindCallElse (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (g := g) (args := args) (he := he) (p0 := p0) (p1 := p1) (err := err) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest) (ih_lowEnd_ok_err := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ err)
  | _, Γ, Λ, _, .bindAxiom a args he proof0 proof1 proof2 proof3 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_bindAxiom (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (a := a) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (proof3 := proof3) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest)
  | _, Γ, Λ, _, .bindAxiomOpt (e := some τ) a args he proof0 proof1 proof2 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_bindAxiomOpt_some (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (a := a) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest)
  | _, Γ, Λ, _, .bindAxiomElse a args he proof0 proof1 proof2 proof3 proof4 err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_bindAxiomElse (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (a := a) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (proof3 := proof3) (proof4 := proof4) (err := err) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest) (ih_lowEnd_ok_err := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ err)
  | _, _, _, _, .bindAxiomOpt (e := none) .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .bindCallIndElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, Γ, Λ, _, .bindAxiomOptElse (e := some τ) a args he hcall hd hgd hr err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_bindAxiomOptElse_some (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (a := a) (args := args) (he := he) (hr := hr) (hcall := hcall) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest) (ih_lowEnd_ok_err := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ err)
  | _, _, _, _, .bindAxiomOptElse (e := none) .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .regRead .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, _, _, _, .regReadElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowB] at h
  | _, Γ, Λ, _, .awaits g zz1 zz2 zz3 zz4 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_awaits (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (g := g) (zz1 := zz1) (zz2 := zz2) (zz3 := zz3) (zz4 := zz4) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest)
  | _, Γ, Λ, _, .exchange g neu zz1 zz2 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_exchange (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (g := g) (neu := neu) (zz1 := zz1) (zz2 := zz2) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest)
  | _, Γ, Λ, _, .narrow e low high err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_narrow (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (e := e) (low := low) (high := high) (err := err) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest) (ih_lowEnd_ok_err := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ err)
  | _, Γ, Λ, _, .narrowRequired e low high rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      blockNarrowRequired_case hS hA hlo0 hens (fun {pr ex} => lowB_ok hS hA hlo0 hens) c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  | _, Γ, Λ, _, .check cnd err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_check (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (cnd := cnd) (err := err) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest) (ih_lowEnd_ok_err := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ err)
  | _, Γ, Λ, _, .float op a b low high rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr => by
      cases op with
      | add =>
        exact blockFloatAdd_case hS hA hlo0 hens
          (fun {pr ex} => lowB_ok (pr := pr) (ex := ex) hS hA hlo0 hens rest)
          c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
      | sub => simp [lowB, floatAddBlockL] at h
      | mul => simp [lowB, floatAddBlockL] at h
      | div => simp [lowB, floatAddBlockL] at h
  | _, Γ, Λ, _, .floatLit q low high rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_floatLit (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (q := q) (low := low) (high := high) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest)
  | _, Γ, Λ, _, .floatOf e low high rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_floatOf (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (e := e) (low := low) (high := high) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest)
  | _, Γ, Λ, _, .floatNarrow e low high err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hlo2, hu, hk, hWa, hpr =>
      lowB_ok_floatNarrow (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (e := e) (low := low) (high := high) (err := err) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hlo2 := hlo2) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowB_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowB_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ rest) (ih_lowEnd_ok_err := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ err)

theorem lowEnd_ok {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → (b : Endblock D (vertragVon D f) l Γ Λ) → (c : List II) →
    (top : Nat) → lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex b = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (σ : World D) (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved →
    lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) →
    Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R b σ ρ) reserved
  | _, Γ, Λ, .ret e proof0, c, top, h, hK, arg4, hW, m, pc, σ, ρ, hp, hlo, arg12, hk, hWa, hpr => by
    exact endRet_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (e := e) (proof0 := proof0)
      c top h hK arg4 hW m pc σ ρ hp hlo arg12 hk hWa hpr
  | _, Γ, _, .cons s rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_cons (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (s := s) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowS_ok_s := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowS_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ _ s) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, Γ, Λ, .bind e rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_bind (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (e := e) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, Γ, Λ, .bindCall g args he proof0 proof1 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_bindCall (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (g := g) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, Γ, Λ, .ite cnd t e, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_ite (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (cnd := cnd) (t := t) (e := e) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_t := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ t) (ih_lowEnd_ok_e := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ e)
  | _, Γ, Λ, .retWhy r hp0, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    exact endWhy_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (r := r) (proof0 := hp0)
      c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  | _, Γ, Λ, .leave hp0, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    exact endLeave_case hS hA hlo0 hens (proof0 := hp0)
      c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  | _, Γ, Λ, .next hp0, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr => by
    exact endNext_case hS hA hlo0 hens (proof0 := hp0)
      c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  | _, Γ, Λ, .bindCallElse g args he p0 p1 err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_bindCallElse (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (g := g) (args := args) (he := he) (p0 := p0) (p1 := p1) (err := err) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_err := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ err) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, Γ, Λ, .bindAxiom a args he proof0 proof1 proof2 proof3 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_bindAxiom (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (a := a) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (proof3 := proof3) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, Γ, Λ, .bindAxiomOpt (e := some τ) a args he proof0 proof1 proof2 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_bindAxiomOpt_some (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (a := a) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, Γ, Λ, .bindAxiomElse a args he proof0 proof1 proof2 proof3 proof4 err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_bindAxiomElse (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (a := a) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (proof3 := proof3) (proof4 := proof4) (err := err) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_err := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ err) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, _, _, .bindAxiomOpt (e := none) .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd, resultWords_vertragVon] at h
  | _, _, _, .bindCallIndElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd, resultWords_vertragVon] at h
  | _, Γ, Λ, .bindAxiomOptElse (e := some τ) a args he hcall hd hgd hr err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_bindAxiomOptElse_some (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (a := a) (args := args) (he := he) (hr := hr) (hcall := hcall) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_err := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ err) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, _, _, .bindAxiomOptElse (e := none) .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd, resultWords_vertragVon] at h
  | _, _, _, .regRead .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd, resultWords_vertragVon] at h
  | _, _, _, .regReadElse .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd, resultWords_vertragVon] at h
  | _, Γ, Λ, .awaits g proof0 proof1 proof2 proof3 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_awaits (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (g := g) (proof0 := proof0) (proof1 := proof1) (proof2 := proof2) (proof3 := proof3) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, Γ, Λ, .bindCallInd p args he proof0 proof1 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_bindCallInd (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (p := p) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, Γ, Λ, .narrow e low high err rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_narrow (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (e := e) (low := low) (high := high) (err := err) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_err := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ err) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, Γ, Λ, .narrowRequired e low high rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      endNarrowRequired_case hS hA hlo0 hens (fun {pr ex} => lowEnd_ok hS hA hlo0 hens) c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr
  | _, Γ, Λ, .exchange g neu proof0 proof1 rest, c, top, h, hK, hs, hW, m, pc, σ, ρ, hp, hlo, hu, hk, hWa, hpr =>
      lowEnd_ok_exchange (hS := hS) (hA := hA) (hlo0 := hlo0) (hens := hens) (g := g) (neu := neu) (proof0 := proof0) (proof1 := proof1) (rest := rest) (c := c) (top := top) (h := h) (hK := hK) (hs := hs) (hW := hW) (m := m) (pc := pc) (σ := σ) (ρ := ρ) (hp := hp) (hlo := hlo) (hu := hu) (hk := hk) (hWa := hWa) (hpr := hpr) (ih_lowEnd_ok_rest := fun {O} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes} {R} {A} {C} {dv} {cap} (hS) (hA) {P} {fp} {K} {Ks} {lo} {rp} {cfp} {σ0} {ρ0} {cens} {tens} (hlo0) (hens) {reserved} {pr} {ex} => @lowEnd_ok O zinst1 zinst2 passes R A C dv cap hS hA P f fp K Ks lo rp cfp σ0 ρ0 cens tens hlo0 hens reserved pr ex _ _ _ rest)
  | _, _, _, .retScoped .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd, resultWords_vertragVon] at h
  | _, _, _, .retWhyScoped .., _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [lowEnd, resultWords_vertragVon] at h

theorem lowArms_all {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} (hW : WIn L fp Ks K) (hlo : FB ≤ lo) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {cs : List (Option Ty)} →
    (arms : Arms D (vertragVon D f) l Γ Λ Λ' cs) →
    ArmsAll (fun b => BlockRuns O passes R L A C dv cap P f σ0 ρ0 rp cfp fp lo Ks K (cens, tens) pr b reserved) arms
  | _, _, _, _, _, .nil => trivial
  | _, _, _, _, _, .cons b rest =>
    ⟨(fun ex cb tb hc ht hs m pc σ ρ hp hlo2 hu hk hw hpr =>
        lowB_ok hS hA hlo0 hens b cb tb hc ht hs hW m pc σ ρ hp hlo hlo2 hu hk hw hpr),
      lowArms_all hS hA hlo0 hens hW hlo rest⟩

theorem lowGrund_all {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} (hW : WIn L fp Ks K) (hlo : FB ≤ lo) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {n : Nat} →
    (arms : GrundArms D (vertragVon D f) l Γ Λ Λ' n) →
    GrundAll (fun b => BlockRuns O passes R L A C dv cap P f σ0 ρ0 rp cfp fp lo Ks K (cens, tens) pr b reserved) arms
  | _, _, _, _, _, .nil => trivial
  | _, _, _, _, _, .cons b rest =>
    ⟨(fun ex cb tb hc ht hs m pc σ ρ hp hlo2 hu hk hw hpr =>
        lowB_ok hS hA hlo0 hens b cb tb hc ht hs hW m pc σ ρ hp hlo hlo2 hu hk hw hpr),
      lowGrund_all hS hA hlo0 hens hW hlo rest⟩

end

end Gabbro.Stage0.Senke
