module
public import Stage0.Senke.Anweisung.Satz.Teil3a

public import Stage0.Senke.Anweisung.Schreiben
public import Stage0.Senke.Welt.Spans.CellStore
public import Stage0.Senke.Welt.WordCell
public import Stage0.Senke.Sperre.Satz
public import Stage0.Senke.Anweisung.Faelle.Gleit.Narrow
public import Stage0.Senke.Anweisung.Faelle.Gleit.Literal
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Wahl
public import Stage0.Senke.Anweisung.Option
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
public import Stage0.Senke.Anweisung.Faelle.EndRuf
public import Stage0.Senke.Anweisung.Faelle.EndWahl
public import Stage0.Senke.Anweisung.Faelle.EndFehler
public import Stage0.Senke.Anweisung.Faelle.EndAtomar
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.NarrowCases
public import Stage0.Senke.Anweisung.Faelle.BlockFehler
public import Stage0.Senke.Anweisung.Satz.Teil2

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable [Kern]
variable {D : Deklaration} {L : Lay D} {V : Vertrag D}

set_option linter.unusedSectionVars false in
theorem lowB_ok_floatLit {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (q)
    (low)
    (high)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.floatLit q low high rest : Block D (vertragVon D f) l Γ Λ Λ') = some (c, top))
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
    (ih_lowB_ok_rest : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex rest = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (Gabbro.Grammatik.Ty.fl low high :: Γ)), PreS L m pc fp K (frei (Gabbro.Grammatik.Ty.fl low high :: Γ) reserved) c ρ reserved → FB ≤ lo → lo ≤ frei (Gabbro.Grammatik.Ty.fl low high :: Γ) reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (Gabbro.Grammatik.Ty.fl low high :: Γ) reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R rest σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R (.floatLit q low high rest : Block D (vertragVon D f) l Γ Λ Λ') σ ρ) reserved :=
  by
  exact blockFloatLit_case hS hA hlo0 hens
    (fun {pr ex} => ih_lowB_ok_rest (pr := pr) (ex := ex) hS hA hlo0 hens)
    c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr

set_option linter.unusedSectionVars false in
theorem lowB_ok_floatOf {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (low)
    (high)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.floatOf (l1 := zi_l1) (h1 := zi_h1) e low high rest : Block D (vertragVon D f) l Γ Λ Λ') = some (c, top))
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
    (ih_lowB_ok_rest : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex rest = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (Gabbro.Grammatik.Ty.fl low high :: Γ)), PreS L m pc fp K (frei (Gabbro.Grammatik.Ty.fl low high :: Γ) reserved) c ρ reserved → FB ≤ lo → lo ≤ frei (Gabbro.Grammatik.Ty.fl low high :: Γ) reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (Gabbro.Grammatik.Ty.fl low high :: Γ) reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R rest σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R (.floatOf (l1 := zi_l1) (h1 := zi_h1) e low high rest : Block D (vertragVon D f) l Γ Λ Λ') σ ρ) reserved :=
  by
  exact blockFloatOfComputed_case hS hA hlo0 hens
    (fun {pr ex} => ih_lowB_ok_rest (pr := pr) (ex := ex) hS hA hlo0 hens)
    c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr

set_option linter.unusedSectionVars false in
theorem lowB_ok_floatNarrow {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (low)
    (high)
    (err)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e low high err rest : Block D (vertragVon D f) l Γ Λ Λ') = some (c, top))
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
    (ih_lowB_ok_rest : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex rest = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (Gabbro.Grammatik.Ty.fl low high :: Γ)), PreS L m pc fp K (frei (Gabbro.Grammatik.Ty.fl low high :: Γ) reserved) c ρ reserved → FB ≤ lo → lo ≤ frei (Gabbro.Grammatik.Ty.fl low high :: Γ) reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (Gabbro.Grammatik.Ty.fl low high :: Γ) reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R rest σ ρ) reserved)
    (ih_lowEnd_ok_err : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex err = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R err σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e low high err rest : Block D (vertragVon D f) l Γ Λ Λ') σ ρ) reserved :=
  by
  exact blockFloatNarrow_case hS hA hlo0 hens
    (fun {pr ex} => ih_lowEnd_ok_err (pr := pr) (ex := ex) hS hA hlo0 hens)
    (fun {pr ex} => ih_lowB_ok_rest (pr := pr) (ex := ex) hS hA hlo0 hens)
    c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr

set_option linter.unusedSectionVars false in
theorem lowEnd_ok_cons {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.cons (Λ' := zi_Λ') s rest : Endblock D (vertragVon D f) l Γ Λ) = some (c, top))
    (hK : top + cap ≤ Ks)
    (hs : 16 * c.length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (hlo : lo ≤ frei Γ reserved)
    (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (ih_lowS_ok_s : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex s = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R s σ ρ) reserved)
    (ih_lowEnd_ok_rest : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex rest = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R rest σ ρ) reserved)
    : Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R (.cons (Λ' := zi_Λ') s rest : Endblock D (vertragVon D f) l Γ Λ) σ ρ) reserved :=
  by
  exact endCons_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (s := s) (rest := rest)
    (fun {pr ex} => ih_lowS_ok_s (pr := pr) (ex := ex) hS hA hlo0 hens)
    (fun {pr ex} => ih_lowEnd_ok_rest (pr := pr) (ex := ex) hS hA hlo0 hens)
    c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr

set_option linter.unusedSectionVars false in
theorem lowEnd_ok_bind {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.bind (τ := zi_τ) e rest : Endblock D (vertragVon D f) l Γ Λ) = some (c, top))
    (hK : top + cap ≤ Ks)
    (hs : 16 * c.length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (hlo : lo ≤ frei Γ reserved)
    (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (ih_lowEnd_ok_rest : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex rest = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (zi_τ :: Γ)), PreS L m pc fp K (frei (zi_τ :: Γ) reserved) c ρ reserved → lo ≤ frei (zi_τ :: Γ) reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (zi_τ :: Γ) reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R rest σ ρ) reserved)
    : Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R (.bind (τ := zi_τ) e rest : Endblock D (vertragVon D f) l Γ Λ) σ ρ) reserved :=
  by
  exact endBind_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (e := e) (rest := rest)
    (fun {pr ex} => ih_lowEnd_ok_rest (pr := pr) (ex := ex) hS hA hlo0 hens)
    c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr

set_option linter.unusedSectionVars false in
theorem lowEnd_ok_bindCall {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (g)
    (args)
    (he)
    (proof0)
    (proof1)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.bindCall (τ := zi_τ) g args he proof0 proof1 rest : Endblock D (vertragVon D f) l Γ Λ) = some (c, top))
    (hK : top + cap ≤ Ks)
    (hs : 16 * c.length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (hlo : lo ≤ frei Γ reserved)
    (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (ih_lowEnd_ok_rest : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex rest = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (zi_τ :: Γ)), PreS L m pc fp K (frei (zi_τ :: Γ) reserved) c ρ reserved → lo ≤ frei (zi_τ :: Γ) reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (zi_τ :: Γ) reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R rest σ ρ) reserved)
    : Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R (.bindCall (τ := zi_τ) g args he proof0 proof1 rest : Endblock D (vertragVon D f) l Γ Λ) σ ρ) reserved :=
  by
  exact endCall_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (g := g) (args := args) (he := he) (proof0 := proof0) (proof1 := proof1) (rest := rest)
    (fun {pr ex} => ih_lowEnd_ok_rest (pr := pr) (ex := ex) hS hA hlo0 hens)
    c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr

set_option linter.unusedSectionVars false in
theorem lowEnd_ok_ite {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (cnd)
    (t)
    (e)
    (c : List II)
    (top : Nat)
    (h : lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.ite cnd t e : Endblock D (vertragVon D f) l Γ Λ) = some (c, top))
    (hK : top + cap ≤ Ks)
    (hs : 16 * c.length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (hlo : lo ≤ frei Γ reserved)
    (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (ih_lowEnd_ok_t : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex t = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R t σ ρ) reserved)
    (ih_lowEnd_ok_e : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex e = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R e σ ρ) reserved)
    : Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R (.ite cnd t e : Endblock D (vertragVon D f) l Γ Λ) σ ρ) reserved :=
  by
  exact endIte_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens (cnd := cnd) (t := t) (e := e)
    (fun {pr ex} => ih_lowEnd_ok_t (pr := pr) (ex := ex) hS hA hlo0 hens)
    (fun {pr ex} => ih_lowEnd_ok_e (pr := pr) (ex := ex) hS hA hlo0 hens)
    c top h hK hs hW m pc σ ρ hp hlo hu hk hWa hpr

end Gabbro.Stage0.Senke
