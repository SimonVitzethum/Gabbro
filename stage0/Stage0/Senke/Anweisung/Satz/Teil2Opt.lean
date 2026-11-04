module
public import Stage0.Senke.Anweisung.Satz.Teil4

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
public import Stage0.Senke.Anweisung.Satz.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable [Kern]
variable {D : Deklaration} {L : Lay D} {V : Vertrag D}

private theorem someAnswer_env {e : Option Ty} {τ : Ty} {Γ : Ctx}
    (he : e = some τ) (v : ErgVal D e) (ρ : Env D Γ) :
    ergEnv (some τ) (he ▸ v) ρ = Env.cons (ergWert he v) ρ := by
  cases he
  rfl

theorem lowB_ok_bindAxiomOpt_some {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (proof0)
    (proof1)
    (proof2)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.bindAxiomOpt (e := some zi_τ) a args he proof0 proof1 proof2 rest : Block D (vertragVon D f) l Γ Λ Λ') = some (c, top))
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
    (ih_lowB_ok_rest : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex rest = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (zi_τ :: Γ)), PreS L m pc fp K (frei (zi_τ :: Γ) reserved) c ρ reserved → FB ≤ lo → lo ≤ frei (zi_τ :: Γ) reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (zi_τ :: Γ) reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R rest σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R (.bindAxiomOpt (e := some zi_τ) a args he proof0 proof1 proof2 rest : Block D (vertragVon D f) l Γ Λ Λ') σ ρ) reserved :=
  by
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨cg, tg⟩, hg, ⟨cr, tr⟩, hr, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  have hks := hW.ks
  simp only [execBlock]
  rcases plainForeignC_ok (L := L) (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ)
      he hg (by omega) hW hp hWa with
      ⟨v, m2, decoded, steps, changed, value, world⟩ | ⟨decoded, stopped⟩
  · rw [decoded]
    simp only [Ausgang.weiterOpt, someAnswer_env he v ρ]
    have span := plainForeignC_top he hg
    have next := hp.nextW hW changed (d' := frei Γ reserved + valueWords zi_τ)
      (by have := hp.ctx; omega) (by omega) (by omega)
    have pre : PreS L m2 _ fp K (frei (zi_τ :: Γ) reserved) cr
        (Env.cons (ergWert he v) ρ) reserved :=
      ⟨by simp only [frei, contextWords_cons]; omega, next.small, next.frame,
        next.code, next.far, envAt_cons next.env value, trivial, wstab_true _ _⟩
    have ih := ih_lowB_ok_rest (O := O) (passes := passes) (σ0 := σ0)
      (reserved := reserved) (pr := pr) (ex := ex) hS hA hlo0 hens cr tr hr
      (by omega) (by omega) hW m2 _ _ _ pre hlo
      (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega)
      (hu.agreeW hW (changed.mono hlo2) hlo)
      (hk.agreeW hW (changed.mono hlo2) (by omega)) world
      (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega)
    rw [pc_add1 pc cg cr]
    exact Sim.prefix hlo steps (changed.mono hlo2)
      (keeps_of_agreeW hW changed hpr (by omega)) (Sim.schrumpf ih)
  · rw [decoded]
    exact stopped

theorem lowEnd_ok_bindAxiomOpt_some {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (proof0)
    (proof1)
    (proof2)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.bindAxiomOpt (e := some zi_τ) a args he proof0 proof1 proof2 rest : Endblock D (vertragVon D f) l Γ Λ) = some (c, top))
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
    : Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R (.bindAxiomOpt (e := some zi_τ) a args he proof0 proof1 proof2 rest : Endblock D (vertragVon D f) l Γ Λ) σ ρ) reserved :=
  by
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨cg, tg⟩, hg, ⟨cr, tr⟩, hr, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  have hks := hW.ks
  have hFB3 : FB = 4 := rfl
  have hFramePrefix := functionFrame_prefix P f
  simp only [execEnd]
  rcases plainForeignC_ok (L := L) (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ)
      he hg (by omega) hW hp hWa with
      ⟨v, m2, decoded, steps, changed, value, world⟩ | ⟨decoded, stopped⟩
  · rw [decoded]
    simp only [EndAusgang.weiterOpt, someAnswer_env he v ρ]
    have span := plainForeignC_top he hg
    have next := hp.nextW hW changed (d' := frei Γ reserved + valueWords zi_τ)
      (by have := hp.ctx; omega) (by omega) (by omega)
    have pre : PreS L m2 _ fp K (frei (zi_τ :: Γ) reserved) cr
        (Env.cons (ergWert he v) ρ) reserved :=
      ⟨by simp only [frei, contextWords_cons]; omega, next.small, next.frame,
        next.code, next.far, envAt_cons next.env value, trivial, wstab_true _ _⟩
    have ih := ih_lowEnd_ok_rest (O := O) (passes := passes) (σ0 := σ0)
      (reserved := reserved) (pr := pr) (ex := ex) hS hA hlo0 hens cr tr hr
      (by omega) (by omega) hW m2 _ _ _ pre
      (by simp only [frei, contextWords_cons] at hlo ⊢; omega)
      (hu.agreeW hW changed (by omega)) (hk.agreeW hW changed (by omega)) world
      (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega)
    rw [pc_add1 pc cg cr]
    exact Ret.prefix (by omega) steps (changed.mono (by omega))
      (keeps_of_agreeW hW changed hpr (by omega)) (Ret.schrumpf ih)
  · rw [decoded]
    exact stopped

end Gabbro.Stage0.Senke
