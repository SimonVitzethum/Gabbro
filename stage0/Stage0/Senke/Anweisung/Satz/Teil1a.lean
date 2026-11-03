/-
  File:      stage0/Stage0/Senke/Anweisung/Satz.lean
  Subject:   Mutual `ir_sim` for statements, blocks and function end blocks, calls included: where machine G ends a block normally (`ok`), the
             lowered code runs to its end and leaves the new environment in the frame, changing no slot below
             `lo`; where G ends in a logic outcome, the code stops with its `exit_group` code. G answers nothing
             outside the outcomes described by `Sim`, including two-way function returns.
-/
module
public import Stage0.Senke.Anweisung.Schreiben
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Sum.Statement
public import Stage0.Senke.Welt.Spans.CellStore
public import Stage0.Senke.Welt.WordCell
public import Stage0.Senke.Sperre.Satz
public import Stage0.Senke.Anweisung.Faelle.Gleit.Narrow
public import Stage0.Senke.Anweisung.Faelle.Gleit.Literal
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
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable [Kern]

variable {D : Deklaration} {L : Lay D} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem lowS_ok_ite {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (cnd)
    (t)
    (e)
    (c : List II)
    (top : Nat)
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.ite cnd t e : Stmt D (vertragVon D f) l Γ Λ Λ') = some (c, top))
    (hK : top + cap ≤ Ks)
    (hs : 16 * c.length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (hlo : FB ≤ lo)
    (hlo2 : lo ≤ frei Γ reserved)
    (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (ih_lowB_ok_t : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex t = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R t σ ρ) reserved)
    (ih_lowB_ok_e : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex e = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R e σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R (.ite cnd t e : Stmt D (vertragVon D f) l Γ Λ Λ') σ ρ) reserved :=
  by
  simp only [lowS, ← hlo0, resultWords_vertragVon, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, hce, ⟨ct, tt⟩, hct, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append, List.length_singleton] at hs
  exact ite_ok hcc (by omega) (by omega) (by omega) (by omega) hW hlo hlo0 hlo2 hpr
    (fun m' pc' hp' hu' hk' hw' => ih_lowB_ok_t (O := O) (passes := passes) (σ0 := σ0) (ex := exPlus ex (ce.length + 1))
      hS hA hlo0 hens ct tt hct (by omega) (by omega) hW m' pc' _ ρ hp' hlo hlo2 hu' hk' hw' hpr)
    (fun m' pc' hp' hu' hk' hw' => ih_lowB_ok_e (O := O) (passes := passes) (σ0 := σ0) (ex := ex) hS hA hlo0 hens ce te
      hce (by omega) (by omega) hW m' pc' _ ρ hp' hlo hlo2 hu' hk' hw' hpr) hp hu hk hWa

set_option linter.unusedSectionVars false in
theorem lowS_ok_onTag {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_cs}
    (v)
    (arms)
    (c : List II)
    (top : Nat)
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.onTag (cs := zi_cs) v arms : Stmt D (vertragVon D f) l Γ Λ Λ') = some (c, top))
    (hK : top + cap ≤ Ks)
    (hs : 16 * c.length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (hlo : FB ≤ lo)
    (hlo2 : lo ≤ frei Γ reserved)
    (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (ih_lowArms_all_arms : ∀ (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) (hW : WIn L fp Ks K) (hlo : FB ≤ lo), ArmsAll (fun b => BlockRuns O passes R L A C dv cap P f σ0 ρ0 rp cfp fp lo Ks K (cens, tens) pr b reserved) arms)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R (.onTag (cs := zi_cs) v arms : Stmt D (vertragVon D f) l Γ Λ Λ') σ ρ) reserved :=
  by
  simp only [lowS, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next hfit =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cv, tv⟩, hcv, ⟨ca, ta⟩, hca, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact onTag_ok (ih_lowArms_all_arms hS hA hlo0 hens hW hlo) hfit hcv hca (by omega) (by omega)
      (by simpa only [List.length_append] using hs) hW hlo hlo0 hlo2 hpr hp hu hk hWa
  · next separate =>
    split at h
    · next count =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨cv, tv⟩, hcv, ⟨ca, ta⟩, hca, rfl, rfl⟩ := h
      exact onSumTag_ok (ih_lowArms_all_arms hS hA hlo0 hens hW hlo)
        (Bool.eq_false_iff.mpr separate) count hcv hca (by omega) (by omega)
        (by simpa only [List.length_append] using hs) hW hlo hlo0 hlo2 hpr hp hu hk hWa
    · cases h

set_option linter.unusedSectionVars false in
theorem lowS_ok_assignGlob {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (e)
    (zz1)
    (zz2)
    (c : List II)
    (top : Nat)
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.assignGlob g e zz1 zz2 : Stmt D (vertragVon D f) l Γ Λ (Λ)) = some (c, top))
    (hK : top + cap ≤ Ks)
    (zzh3 : 16 * c.length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (zzh4 : FB ≤ lo)
    (hlo2 : lo ≤ frei Γ reserved)
    (zzh5 : Umf L A C dv m fp Ks K)
    (zzh6 : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R (.assignGlob g e zz1 zz2 : Stmt D (vertragVon D f) l Γ Λ (Λ)) σ ρ) reserved :=
  by
  simp only [lowS, ← hlo0, resultWords_vertragVon, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ce, te⟩, he, hc⟩ := h
  simp only [execStmt, Sim]
  have hks := hW.ks
  have gtop := globalStoreC_top hc
  generalize hσE : σ.lese Λ _ = σE
  have hWaE : WeltAt m L σE := by rw [← hσE]; exact hWa
  obtain ⟨m', s', a', hw'⟩ := globalStoreC_ok (σ := σE) hc (by omega) hW.lay hW.dis hW.lo
    (PreS.welt hp hks hWaE hW.lay hW.lo)
    (fun m pc hp => lowE_ok (same := by intro _; rfl) σE σE (fun _ h => h) hW.lay e _ ce te he (by have := lowE_top e _ _ _ he; omega) m pc ρ hp)
  exact ⟨m', s', (a'.widen hks).mono hlo2,
    envAt_agreeW hp.env a' hW.lo (by have := hp.frame.room; omega) (Nat.le_refl _) (by omega), hw',
    keeps_of_agreeW hW (a'.widen hks) hpr (by omega)⟩

set_option linter.unusedSectionVars false in
theorem lowS_ok_publish {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (e)
    (zz1)
    (zz2)
    (zz3)
    (zz4)
    (c : List II)
    (top : Nat)
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.publish g e zz1 zz2 zz3 zz4 : Stmt D (vertragVon D f) l Γ Λ (Λ)) = some (c, top))
    (hK : top + cap ≤ Ks)
    (zzh5 : 16 * c.length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (zzh6 : FB ≤ lo)
    (hlo2 : lo ≤ frei Γ reserved)
    (zzh7 : Umf L A C dv m fp Ks K)
    (zzh8 : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R (.publish g e zz1 zz2 zz3 zz4 : Stmt D (vertragVon D f) l Γ Λ (Λ)) σ ρ) reserved :=
  by
  simp only [lowS, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next hl =>
    simp only [Bool.and_eq_true] at hl
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [execStmt, Sim]
    have htop := lowE_top e _ _ _ he
    have hin := hW.lay.2.1 g
    obtain ⟨m', s', a', en, hw'⟩ := store_ok (σ := σ.lese Λ e.orte) hp hW hWa (by omega)
      (fun m pc hp => (lowE_ok (same := by intro _; rfl) (σ.lese Λ e.orte) (σ.lese Λ e.orte) (fun _ h => h) hW.lay e _ ce te he (by omega) m pc ρ hp).word
        (aggregateFits_compat hl.2))
      (fun m pc hp => (const_ok hp hl.1 (by omega)).mono fun x hx => hx.trans (BitVec.ofInt_natCast _ _))
      ⟨hin.1, by have := hin.2; rw [aggregateFits_width hl.2] at this; omega⟩
      (fun m w hm hpe => weltAt_globWord (aggregateFits_width hl.2) hm hW.lay hW.dis hpe)
    exact ⟨m', s', a'.mono hlo2, en, hw', keeps_of_agreeW hW a' hpr (by have := hW.ks; omega)⟩
  · cases h


end Gabbro.Stage0.Senke
