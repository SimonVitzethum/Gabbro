/- Literal rounding is performed in Lean; the IR only materialises the resulting bits. -/
module
public import NativeFloat.Literal
public import Stage0.Senke.Anweisung.Faelle.Gleit.Bind
public import Stage0.Senke.Ausdruck.Gleit.Wort
public import Stage0.Senke.Ausdruck.Gleit.Slots.Test
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem blockFloatLit_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {q low high : Int × Int} {rest : Block D (vertragVon D f) l (.fl low high :: Γ) Λ Λ'} :
    (∀ {pr ex}, BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .floatLit q low high rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, ← hlo0, floatLiteralL] at h
  cases hv : gleitPasst low high (bruch q) with
  | none =>
    rw [hv] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [execBlock, hv, Sim]
    change Stops ⟨pc, fp⟩ m 107
    exact stop_ok hp.code hp.far hp.frame (by have := hW.ks; omega) hp.small (by decide)
  | some v =>
    rw [hv] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hx : v.x = bruch q := by unfold gleitPasst at hv; split at hv <;> cases hv; rfl
    have hb : v.x.toBits.toNat < 65536 ^ 4 := by exact v.x.toBits.toBitVec.isLt
    let cw := konstWL 4 (bruch q).toBits.toNat (frei Γ reserved)
    have ht := konstWL_top 4 (bruch q).toBits.toNat (frei Γ reserved)
    have hks := hW.ks
    have htop : frei Γ reserved + 2 ≤ max cw.2 tr := by simp only [cw, konstWL, bin2]; omega
    change max cw.2 tr + cap ≤ Ks at hK
    simp only [execBlock, hv]
    refine bindValue_ok (L := L) (τ := .fl low high) (v := v) hW hlo hlo0 hlo2 hpr (by omega) ?_ ?_ hp hu hk hWa
    · intro m pc hp
      refine Ok.value (width := rfl) ?_
      exact (konstWL_ok 4 _ (by simpa only [hx] using hb) (by omega) hp).mono
        fun w hen => by
          simpa only [hx, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hen
    · intro m pc hp hu hk hw
      exact ihRest (ex := ex) cr tr hr (by omega)
        (by simp only [List.length_append] at hs; omega) hW m pc σ _ hp hlo
        (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega) hu hk hw
        (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega)

theorem blockFloatOfLit_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Int} {low high : Int × Int} {rest : Block D (vertragVon D f) l (.fl low high :: Γ) Λ Λ'} :
    (∀ {pr ex}, BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .floatOf (.lit n) low high rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  have hx : gleitAusInt n = bruch (n, 1) := by
    simpa only [gleitAusInt] using (Gabbro.Grammatik.bruch_integer n).symm
  have result := blockFloatLit_case hS hA hlo0 hens ihRest c top
    (by simpa only [lowB] using h) hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simpa only [execBlock, eval, Expr.orte, World.lese, World.merke,
    List.map_nil, List.nil_append, hx] using result

theorem blockFloatOfComputed_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {a b : Int} {e : Expr D Γ Λ (.int a b)} {low high : Int × Int} {rest : Block D (vertragVon D f) l (.fl low high :: Γ) Λ Λ'} :
    (∀ {pr ex}, BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex rest) →
    BlockCase (reserved := reserved) L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (show Block D (vertragVon D f) l Γ Λ Λ' from .floatOf e low high rest) := by
  intro ihRest c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowB, ← hlo0] at h
  split at h
  · next n =>
    exact blockFloatOfLit_case hS hA hlo0 hens ihRest c top
      (by simpa only [lowB] using h) hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  · simp only [nativeFloatBindL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cc, tc⟩, hcc, ⟨cr, tr⟩, hr, hc⟩ := h
    cases hc
    let σr := σ.lese Λ e.orte
    let x := gleitAusInt (eval σr e σr ρ).n
    have result := nativeFloatBind_ok (P := P) (σ := σr) (x := x)
      (out := fun v => execBlock O passes R rest σr (Env.cons v ρ))
      hcc (by omega) (by simpa only [List.length_append] using hs)
      hW hlo hlo0 hlo2 hpr
      (fun m pc pre =>
        (computedFloatOfE_ok (σ₀ := σr) (σ := σr) he pre (by omega) hW.lay rfl
          (fun _ h => h)).mono (fun w hw => by rw [hw]; exact nativeFloat_read_word _))
      (fun v m pc pre hu hk hw => ihRest (ex := ex) cr tr hr (by omega)
        (by simp only [floatNarrowC, List.length_append, List.length_nil, List.nil_append] at hs; omega)
        hW m pc σr _ pre hlo
        (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega) hu hk hw
        (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega))
      hp hu hk hWa
    simpa only [execBlock] using result


end Gabbro.Stage0.Senke
