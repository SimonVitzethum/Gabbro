/-
  File:      stage0/Stage0/Senke/Anweisung/Satz.lean
  Subject:   Mutual `ir_sim` for statements, blocks and function end blocks, calls included: where machine G ends a block normally (`ok`), the
             lowered code runs to its end and leaves the new environment in the frame, changing no slot below
             `lo`; where G ends in a logic outcome, the code stops with its `exit_group` code. G answers nothing
             outside the outcomes described by `Sim`, including two-way function returns.
-/
module
public import Stage0.Senke.Anweisung.Schreiben
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
public import Stage0.Senke.Anweisung.Satz.Teil1a
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable [Kern]

variable {D : Deklaration} {L : Lay D} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem lowS_ok_traverse {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (t)
    (inv)
    (body)
    (c : List II)
    (top : Nat)
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.traverse t inv body : Stmt D (vertragVon D f) l Γ Λ (Λ)) = some (c, top))
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
    (ih_lowB_ok_body : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex body = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (Gabbro.Grammatik.Ty.index (D.count t) :: Γ)), PreS L m pc fp K (frei (Gabbro.Grammatik.Ty.index (D.count t) :: Γ) reserved) c ρ reserved → FB ≤ lo → lo ≤ frei (Gabbro.Grammatik.Ty.index (D.count t) :: Γ) reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (Gabbro.Grammatik.Ty.index (D.count t) :: Γ) reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R body σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R (.traverse t inv body : Stmt D (vertragVon D f) l Γ Λ (Λ)) σ ρ) reserved :=
  by
  exact traverse_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (t := t) (inv := inv) (body := body)
    (fun {pr ex} => ih_lowB_ok_body (pr := pr) (ex := ex) hS hA hlo0 hens)
    c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr

set_option linter.unusedSectionVars false in
theorem lowS_ok_breaking {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (zz1)
    (body)
    (c : List II)
    (top : Nat)
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.breaking zz1 body : Stmt D (vertragVon D f) l Γ Λ Λ') = some (c, top))
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
    (ih_lowB_ok_body : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex body = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R body σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R (.breaking zz1 body : Stmt D (vertragVon D f) l Γ Λ Λ') σ ρ) reserved :=
  by
  simp only [lowS, ← hlo0, resultWords_vertragVon] at h
  simp only [execStmt]
  exact ih_lowB_ok_body (O := O) (passes := passes) (σ0 := σ0) (pr := pr) (ex := ex) hS hA hlo0 hens c top h hK hs hW
    m pc σ ρ hp hlo hlo2 hu hk hWa hpr

set_option linter.unusedSectionVars false in
theorem lowS_ok_onOption {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (o)
    (p)
    (a)
    (c : List II)
    (top : Nat)
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.onOption (n := zi_n) o p a : Stmt D (vertragVon D f) l Γ Λ Λ') = some (c, top))
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
    (ih_lowB_ok_p : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex p = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (Gabbro.Grammatik.Ty.index zi_n :: Γ)), PreS L m pc fp K (frei (Gabbro.Grammatik.Ty.index zi_n :: Γ) reserved) c ρ reserved → FB ≤ lo → lo ≤ frei (Gabbro.Grammatik.Ty.index zi_n :: Γ) reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (Gabbro.Grammatik.Ty.index zi_n :: Γ) reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R p σ ρ) reserved)
    (ih_lowB_ok_a : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex a = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R a σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R (.onOption (n := zi_n) o p a : Stmt D (vertragVon D f) l Γ Λ Λ') σ ρ) reserved :=
  by
  simp only [lowS, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next hn =>
    simp only [decide_eq_true_eq] at hn
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cc, tc⟩, hcc, ⟨ce, te⟩, hce, ⟨ct, tt⟩, hct, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_append, List.length_cons, List.length_nil] at hs
    exact onOption_ok (o := o) (t := p) (e := a) (cc := cc) (ct := ct) (ce := ce) hn (by omega) hcc (by omega) (by omega) hW hlo hlo0 hlo2 hpr
      (fun k _ m' pc' hp' hu' hk' hw' => ih_lowB_ok_p (O := O) (passes := passes) (σ0 := σ0)
        (ex := exPlus ex (ce.length + 1)) hS hA hlo0 hens ct tt hct (by omega) (by omega) hW m' pc' _ (.cons k ρ)
        hp' hlo
        (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega) hu' hk' hw'
        (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega))
      (fun m' pc' hp' hu' hk' hw' => ih_lowB_ok_a (O := O) (passes := passes) (σ0 := σ0) (ex := ex)
        hS hA hlo0 hens ce te hce (by omega) (by omega) hW m' pc' _ ρ hp' hlo hlo2 hu' hk' hw' hpr)
      hp hu hk hWa
  · cases h

set_option linter.unusedSectionVars false in
theorem lowS_ok_onWhy {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_n}
    (v)
    (arms)
    (c : List II)
    (top : Nat)
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.onWhy (n := zi_n) v arms : Stmt D (vertragVon D f) l Γ Λ Λ') = some (c, top))
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
    (ih_lowGrund_all_arms : ∀ (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) (hW : WIn L fp Ks K) (hlo : FB ≤ lo), GrundAll (fun b => BlockRuns O passes R L A C dv cap P f σ0 ρ0 rp cfp fp lo Ks K (cens, tens) pr b reserved) arms)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R (.onWhy (n := zi_n) v arms : Stmt D (vertragVon D f) l Γ Λ Λ') σ ρ) reserved :=
  by
  simp only [lowS, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next hn =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cv, tv⟩, hcv, ⟨ca, ta⟩, hca, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact onWhy_ok hn (ih_lowGrund_all_arms hS hA hlo0 hens hW hlo) hcv hca (by omega) (by omega)
      (by simpa only [List.length_append] using hs) hW hlo hlo0 hlo2 hpr hp hu hk hWa
  · cases h

set_option linter.unusedSectionVars false in
theorem lowS_ok_locks {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (hr)
    (body)
    (c : List II)
    (top : Nat)
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.locks Lk hr body : Stmt D (vertragVon D f) l Γ Λ (Λ)) = some (c, top))
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
    (ih_lowB_ok_body : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex body = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R body σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R (.locks Lk hr body : Stmt D (vertragVon D f) l Γ Λ (Λ)) σ ρ) reserved :=
  by
  simp only [lowS, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next hc =>
    obtain ⟨hrf, hex1, hex2⟩ := hc
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cb, tb⟩, hcb, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hlen := locksCode_len L (L.lk Lk) (frei Γ reserved) cb ex.1 ex.2
    have hks := hW.ks
    simp only [execStmt]
    have run := locks_ok hrf hex1 hex2 (by omega) hW hlo0 hlo2 hpr
      (fun m' σ' hp' hu' hk' hw' => ih_lowB_ok_body (O := O) (passes := passes) (σ0 := σ0) (pr := pr)
        (ex := (16 * 30, 16 * 60)) hS hA hlo0 hens cb tb hcb (by omega) (by rw [hlen] at hs; omega)
        ⟨hW.lay, hW.dis, hW.top, hW.ord, by omega⟩ m' _ σ' ρ hp' hlo hlo2 hu' hk' hw' hpr) hp hu hk hWa
    have noReturn := retFreiB_istZ (O := O) (passes := passes) (R := R) body hrf (σ.nimmt Lk) ρ
    generalize result : execBlock O passes R body (σ.nimmt Lk) ρ = outcome at run noReturn ⊢
    cases outcome with
    | ok σ' ρ' | leave _ σ' ρ' | next _ σ' ρ' => exact run
    | logik e | hardware e => exact run
    | zurueck σ' v | why σ' v => cases noReturn
  · cases h

set_option linter.unusedSectionVars false in
theorem lowS_ok_retry {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (n)
    (bis)
    (body)
    (overflow)
    (c : List II)
    (top : Nat)
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.retry n bis body overflow : Stmt D (vertragVon D f) l Γ Λ (Λ)) = some (c, top))
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
    (hw : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (ih_lowB_ok_body : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex body = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R body σ ρ) reserved)
    (ih_lowB_ok_overflow : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex overflow = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R overflow σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R (.retry n bis body overflow : Stmt D (vertragVon D f) l Γ Λ (Λ)) σ ρ) reserved :=
  by
  exact retry_case hlo0
    (fun {pr ex} => ih_lowB_ok_body (pr := pr) (ex := ex) hS hA hlo0 hens)
    (fun {pr ex} => ih_lowB_ok_overflow (pr := pr) (ex := ex) hS hA hlo0 hens)
    c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hw hpr

end Gabbro.Stage0.Senke
